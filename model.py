from m2_functions import abductive_inference_multi, projection, check_axiom_dimensions_multi, witness_set_nag
from itertools import combinations
import re
import os
from concurrent.futures import ProcessPoolExecutor, TimeoutError
import numpy as np
from itertools import product
from sympy import symbols as sp_symbols, sympify as sp_sympify, Poly as SpPoly
import argparse

def _str2bool(x: str) -> bool:
    if isinstance(x, bool):
        return x
    s = x.strip().lower()
    return s in {"1", "true", "t", "yes", "y", "on"}

def _parse_num_axiom_spec(spec: str, max_n: int) -> set[int]:
    """
    Accepts forms:
      - '[a,b]'  inclusive range
      - 'a..b'   inclusive range
      - 'a,b,c'  explicit set
      - 'k'      single n
      - 'all'    {0..max_n}
    Returns a set clipped to [0, max_n].
    """
    spec = spec.strip()
    vals = set()
    if spec.lower() == "all":
        return set(range(0, max_n + 1))
    if spec.startswith("[") and spec.endswith("]"):
        left, right = spec[1:-1].split(",", 1)
        a, b = int(left.strip()), int(right.strip())
        vals = set(range(min(a, b), max(a, b) + 1))
    elif ".." in spec:
        left, right = spec.split("..", 1)
        a, b = int(left.strip()), int(right.strip())
        vals = set(range(min(a, b), max(a, b) + 1))
    elif "," in spec:
        vals = {int(t.strip()) for t in spec.split(",") if t.strip()}
    else:
        vals = {int(spec)}
    # clip to [0, max_n]
    return {n for n in vals if 0 <= n <= max_n}


def _parse_m2_complex_token(tok: str) -> complex:
    """Parse a single Macaulay2 complex token like '.123-4.5*ii' into Python complex."""
    s = tok.strip()
    # M2 uses 'ii' for sqrt(-1)
    s = s.replace('*ii', 'j').replace('ii', 'j')
    # Fix leading decimals: .123 -> 0.123, -.45 -> -0.45
    s = s.replace('-.', '-0.').replace('+.','+0.')
    if s.startswith('.'):
        s = '0' + s
    # Also handle scientific notation attached to j, e.g., '1e-15+2e-16j' is fine
    try:
        return complex(s)
    except Exception:
        # As a fallback try to drop spaces
        return complex(s.replace(' ', ''))

def _read_witness_points(witness_path: str):
    """
    Return (var_order, comps) where:
      - var_order: List[str] (ring order printed in file)
      - comps: List[List[List[complex]]]  (each inner list = one component's points)
    """
    var_order = []
    comps = []
    cur = None

    with open(witness_path, 'r') as f:
        lines = [ln.rstrip('\n') for ln in f]

    i = 0
    # header
    while i < len(lines) and not lines[i].startswith('variable ordering:'):
        i += 1
    if i < len(lines):
        hdr = lines[i].split(':', 1)[1].strip()
        var_order = [v.strip() for v in hdr.split(',') if v.strip()]
        i += 1

    # scan components
    while i < len(lines):
        ln = lines[i]
        if ln.startswith('component_'):
            if cur is not None and cur:
                comps.append(cur)
            cur = []
            i += 1
            continue
        if ln.startswith('points:'):
            i += 1
            while i < len(lines) and lines[i] and not lines[i].startswith('component_'):
                row = lines[i]
                if not row.startswith('--') and row.strip():
                    toks = [t.strip() for t in row.split(',')]
                    coords = [_parse_m2_complex_token(t) for t in toks]
                    if cur is None:
                        cur = []
                    cur.append(coords)
                i += 1
            continue
        i += 1

    if cur is not None and cur:
        comps.append(cur)

    return var_order, comps



def _monomial_support_from_axiom(axiom: str, all_vars_in_ring: list[str]):
    """
    Given an axiom (string in your M2 syntax), return:
      vars_sub:  list of variables that actually appear in the axiom (degree > 0),
      alphas:    list of exponent tuples for EACH monomial of the axiom, but
                 restricted to vars_sub (same order as vars_sub),
      total_deg: total degree (max sum of exponents) of the axiom,
      monom_ct:  number of monomials in the axiom after combining like terms.
    Notes:
      - We parse with SymPy; '^' -> '**'.
      - We respect the exact monomial support of the axiom (not a degree box).
    """
    expr_str = axiom.replace('^', '**')
    # Create sympy symbols for all ring vars, in the same order
    sym_list = sp_symbols(' '.join(all_vars_in_ring))
    sym_map = {str(s): s for s in sym_list}
    expr = sp_sympify(expr_str, locals=sym_map)

    # Build a Poly over the full variable order (even if some vars don't appear)
    poly = SpPoly(expr, *[sym_map[v] for v in all_vars_in_ring], domain='EX')

    # Variables that actually appear with positive degree
    vars_sub = []
    idxs_sub = []
    for i, v in enumerate(all_vars_in_ring):
        d = poly.degree(sym_map[v])
        if d is not None and d > 0:
            vars_sub.append(v)
            idxs_sub.append(i)

    # Monomial support (tuples of exponents in full ring order)
    monoms_full = poly.monoms()       # List[Tuple[int,...]] aligned with all_vars_in_ring
    # Reduce support to vars_sub by slicing each exponent tuple
    alphas = [tuple(m[i] for i in idxs_sub) for m in monoms_full]

    total_deg = poly.total_degree()
    monom_ct  = len(alphas)
    return vars_sub, alphas, total_deg, monom_ct


def _vars_and_degrees_from_axiom(axiom: str, all_vars: list[str]):
    """
    From an axiom string like '-w^2*m2*d2 + Fc', extract per-variable degrees
    using SymPy. We treat '^' as '**', and only keep variables appearing with
    positive exponent. Returns an ordered (vars_sub, degs_sub) where order matches all_vars.
    """
    # SymPy parse
    expr_str = axiom.replace('^', '**')
    # Create sympy symbols for all vars; keep original names
    sym_map = {v: v for v in all_vars}
    syms = sp_symbols(' '.join(all_vars))
    # Map by name for Poly generation
    sym_dict = {str(s): s for s in syms}
    expr = sp_sympify(expr_str, locals=sym_dict)
    poly = SpPoly(expr, *[sym_dict[v] for v in all_vars], domain='EX')
    # degrees per var = max exponent of that var over all monomials where it appears
    degs = []
    vars_sub = []
    for idx, v in enumerate(all_vars):
        d = poly.degree(sym_dict[v])
        if d is not None and d > 0:
            vars_sub.append(v)
            degs.append(int(d))
    return vars_sub, degs

def _enumerate_multiindices(degs: list[int]):
    """Return list of exponent tuples with 0..deg_i along each axis (cartesian product)."""
    ranges = [range(d+1) for d in degs]
    return list(product(*ranges))

def _eval_monomials_row(coords: list[complex], alphas: list[tuple[int, ...]]) -> list[complex]:
    """Given coords [x1,...,xk] and exponent tuples alphas, return [prod x_i^{a_i}]."""
    out = []
    for a in alphas:
        val = 1+0j
        for x, e in zip(coords, a):
            if e:
                val *= (x ** e)
        out.append(val)
    return out

def _fit_nullspace(A: np.ndarray):
    """
    Compute the smallest right-singular vector of A (Ax ~ 0).
    Returns (x, sigma_min) normalized so max |x| == 1.
    """
    if A.size == 0:
        return None, None
    U, s, Vh = np.linalg.svd(A, full_matrices=False)
    x = Vh[-1, :]
    if np.max(np.abs(x)) > 0:
        x = x / np.max(np.abs(x))
    return x, (s[-1] if len(s) else None)

def _format_polynomial(var_names: list[str], alphas: list[tuple[int, ...]], coeffs: np.ndarray, tol=1e-10) -> str:
    """Human-readable polynomial string c1*m1 + c2*m2 + ... ~ 0."""
    terms = []
    for c, a in zip(coeffs, alphas):
        if abs(c) < tol:
            continue
        # Build monomial string
        mono_parts = []
        for v, e in zip(var_names, a):
            if e == 0:
                continue
            elif e == 1:
                mono_parts.append(v)
            else:
                mono_parts.append(f"{v}^{e}")
        mono = '*'.join(mono_parts) if mono_parts else "1"
        # Coeff (complex) with compact formatting
        c_str = f"{c.real:.6g}" if abs(c.imag) < tol else f"({c.real:.6g}{'+' if c.imag>=0 else ''}{c.imag:.6g}i)"
        terms.append(f"{c_str}*{mono}")
    if not terms:
        return "0"
    return " + ".join(terms)

def _format_poly_with_fixed_support(var_names: list[str],
                                    alphas: list[tuple[int, ...]],
                                    coeffs: np.ndarray,
                                    tol: float = 1e-10) -> str:
    """
    Produce a readable polynomial using EXACTLY the provided monomial support.
    """
    terms = []
    for c, a in zip(coeffs, alphas):
        if abs(c) < tol:
            continue
        # monomial
        mono_parts = []
        for v, e in zip(var_names, a):
            if e == 0:
                continue
            elif e == 1:
                mono_parts.append(v)
            else:
                mono_parts.append(f"{v}^{e}")
        mono = '*'.join(mono_parts) if mono_parts else '1'
        # coefficient (complex-aware)
        if abs(c.imag) < tol:
            c_str = f"{c.real:.6g}"
        else:
            c_str = f"({c.real:.6g}{'+' if c.imag>=0 else ''}{c.imag:.6g}i)"
        terms.append(f"{c_str}*{mono}")
    return " + ".join(terms) if terms else "0"


def read_problem(file_path):
    """
    Reads a physics problem from a structured TXT file and returns a dict with:
      - variables: List[str]
      - equations: List[str]
      - measured_vars: List[str]
      - non_measured_vars: List[str]
      - targets: List[str]  # NEW: multiple targets supported
    """
    with open(file_path, 'r') as f:
        content = f.read().strip()

    data = {
        'variables': [],
        'equations': [],
        'measured_vars': [],
        'non_measured_vars': [],
        'targets': []
    }

    # Variables
    vars_match = re.search(r'Variables:\s*\[(.*?)\]', content, re.DOTALL)
    if vars_match:
        vars_str = vars_match.group(1)
        data['variables'] = [v.strip().strip('"').strip("'") for v in vars_str.split(',') if v.strip()]

    # Equations: everything between "Equations:" and the next blank line followed by "Measured"
    eqs_match = re.search(r'Equations?:\s*(.*?)(?=\n\s*\n\s*Measured)', content, re.DOTALL | re.IGNORECASE)
    if eqs_match:
        eqs_str = eqs_match.group(1).strip()
        data['equations'] = [eq.strip() for eq in eqs_str.split('\n') if eq.strip()]

    # Measured variables
    measured_match = re.search(r'Measured Variables:\s*\[(.*?)\]', content, re.DOTALL | re.IGNORECASE)
    if measured_match:
        measured_str = measured_match.group(1)
        data['measured_vars'] = [v.strip().strip('"').strip("'") for v in measured_str.split(',') if v.strip()]
        data['non_measured_vars'] = [v for v in data['variables'] if v not in data['measured_vars']]

    # Target polynomials:
    # Accepts either a single-line "Target Polynomial: q" or a block:
    # Target Polynomial:
    # q1
    # q2
    targ_block = re.search(r'Target Polynomial:?(\s*\n+([\s\S]*))$', content, re.IGNORECASE)
    if targ_block:
        block = targ_block.group(1).strip()
        lines = [ln.strip() for ln in block.split('\n') if ln.strip()]
        # Normalize: if the first "line" is a one-liner following the colon, keep it; otherwise treat as multi-line
        data['targets'] = lines

    # Backward compatibility: if earlier code expects `target` as a string
    # you can still derive it with: target = data['targets'][0] if data['targets'] else ''
    return data

def vars_in_poly(poly: str, variables: list[str]) -> list[str]:
    # Match whole identifiers; avoid partial matches (e.g., 'm' matching 'm0')
    import re
    found = set()
    # Check longer names first to avoid shadowing (m0 before m)
    for v in sorted(variables, key=len, reverse=True):
        if re.search(rf'(?<![A-Za-z0-9_]){re.escape(v)}(?![A-Za-z0-9_])', poly):
            found.add(v)
    return list(found)


TIMEOUT_SECONDS = 30

def run_abduction_with_timeout(args):
    (vars, measured_vars, non_measured_vars,
     remaining_axioms, targets, filename, removed_axioms,
     require_in_gb_literal, measured_per_target, non_measured_per_target) = args
    try:
        abductive_inference_multi(
            vars, measured_vars, non_measured_vars,
            remaining_axioms, targets, filename, removed_axioms,
            require_in_gb_literal=require_in_gb_literal,
            measured_per_target=measured_per_target,
            non_measured_per_target=non_measured_per_target
        )
        return "completed"
    except Exception as e:
        return f"error: {e}"

def run_dimensionality_check_with_timeout(args):
    vars, axioms, targets, removed_axioms, filename = args
    try:
        return check_axiom_dimensions_multi(vars, axioms, targets, removed_axioms, filename)
    except Exception as e:
        return f"error: {e}"

def run_witness_with_timeout(args):
    vars, remaining_axioms, targets, filename = args
    try:
        return witness_set_nag(vars, remaining_axioms, targets, filename)
    except Exception as e:
        return f"error: {e}"

def main(args=None):
    parser = argparse.ArgumentParser(description="AI Noether: numerical + algebraic abduction and dimensionality checks")
    parser.add_argument("--numAxiom", type=str, default="all",
                        help="Subset sizes to remove. Examples: '[1,3]' (=> 1,2,3), '1,3,5', '2..4', '0', 'all'")
    parser.add_argument("--numericalAbduction", type=_str2bool, default=True,
                        help="Run numerical irreducible decomposition / witness sets (true/false)")
    parser.add_argument("--algebraicAbduction", type=_str2bool, default=True,
                        help="Run algebraic abductive inference in Macaulay2 (true/false)")
    parser.add_argument("--dimensionalityCheck", type=_str2bool, default=True,
                        help="Run dimension checks (true/false)")
    parser.add_argument("--timeout", type=int, default=30, help="Per-task timeout in seconds")
    parser.add_argument("--requireLiteralGB", type=_str2bool, default=True,
                        help="If true, require literal appearance of each target in eliminated GB")
    parser.add_argument("--problems", type=str, nargs="*", default=None,
                        help="Optional list of problem names; defaults to the hardcoded problems_list")

    cli = parser.parse_args(args=args)

    # Default problems list if not provided
    problems_list = cli.problems or [
        #'kepler',
        #'decay',
        #'einstein',
        #'einstein_mass',
        'einstein_length',
        'einstein_combined',
        #'escape_velocity',
        #'hagen',
        #'hall',
        #'inelastic_collision',
        #'kepler',
        #'kepler_2',
        #'light',
        #'photoHall',
        #'photoHall_2',

        #'kepler_noise',
        #'decay_noise',
        'einstein_noise',
        'einstein_mass_noise',
        'escape_velocity_noise',
        #'hagen_noise',
        #'hall_noise',
        #'inelastic_collision_noise',
        #'kepler_noise',
        #'kepler_2_noise',
        'light_noise',
        'photoHall_noise',
        'photoHall_2_noise',
    ]

    global TIMEOUT_SECONDS
    TIMEOUT_SECONDS = cli.timeout

    for problem_name in problems_list:
        filepath = f"systems_and_phenomena/real/{problem_name}/system.txt"
        problem_data = read_problem(filepath)

        vars = problem_data['variables']
        axioms = problem_data['equations']
        measured_vars = problem_data['measured_vars']
        non_measured_vars = problem_data['non_measured_vars']
        targets = problem_data['targets']  # multiple targets supported

        print(f"Problem: {problem_name}")
        output_dir = f'results/real/{problem_name}/'
        os.makedirs(output_dir, exist_ok=True)

        with open(f'{output_dir}/data.txt', 'w') as f:
            f.write(f"Variables: {vars}\n")
            f.write(f"Measured Variables: {measured_vars}\n")
            f.write(f"Non-Measured Variables: {non_measured_vars}\n")
            f.write(f"Axioms: {axioms}\n")
            f.write(f"Targets: {targets}\n")

        # Build the set of n values for THIS problem, clipped by len(axioms)
        n_allows = _parse_num_axiom_spec(cli.numAxiom, max_n=len(axioms))

        ##### Projection (per target) — unchanged #####
        print("Running Projection (per target)")
        for i, q in enumerate(targets, start=1):
            target_vars = vars_in_poly(q, vars)
            measured_subset = [v for v in measured_vars if v in target_vars]
            non_measured_subset = [v for v in vars if v not in measured_subset]
            fname = os.path.join(output_dir, f'projection_target_{i}.txt')
            projection(vars, axioms, measured_subset, non_measured_subset, fname, targets=[q])

        ##### Numerical Witness Sets (if enabled) #####
        if cli.numericalAbduction:
            print("Running Numerical Irreducible Decomposition (witness sets)")
            witness_root = os.path.join(output_dir, "witness_sets")
            os.makedirs(witness_root, exist_ok=True)

            with ProcessPoolExecutor() as executor:
                indices = list(range(len(axioms)))
                for n in sorted(n_allows):
                    n_dir = os.path.join(witness_root, f"{n}_axiom(s)_removed")
                    os.makedirs(n_dir, exist_ok=True)

                    for combo_indices in combinations(indices, n):
                        removed_axioms = [axioms[i] for i in combo_indices]
                        remaining_axioms = [axioms[i] for i in indices if i not in combo_indices]

                        combo_str = '_'.join(str(i + 1) for i in combo_indices) if combo_indices else "none"
                        combo_dir = os.path.join(n_dir, f"combo_{combo_str}")
                        os.makedirs(combo_dir, exist_ok=True)
                        filename = os.path.join(combo_dir, "witness.txt")


                        future = executor.submit(
                            run_witness_with_timeout,
                            (vars, remaining_axioms, targets, filename)
                        )
                        try:
                            result = future.result(timeout=TIMEOUT_SECONDS)
                            if isinstance(result, str) and result.startswith("error:"):
                                with open(filename, 'w') as f:
                                    f.write(f"Witness set skipped due to error: {result}\n")
                            else:
                                # === Fit a polynomial per dropped axiom, using witness points ===
                                try:
                                    var_order, comps = _read_witness_points(filename)
                                    if not comps or len(var_order) != len(vars):
                                        # no components or ring mismatch; write a note and continue
                                        with open(os.path.splitext(filename)[0] + "_fit_note.txt", "w") as ef:
                                            ef.write("No valid components or ring mismatch; skipping per-component fits.\n")
                                    else:
                                        # map var -> column index once
                                        col_idx = {v: var_order.index(v) for v in var_order}

                                        for cidx, comp_pts in enumerate(comps, start=1):
                                            # Prepare per-component matrix of full ring coords (rows = points)
                                            comp_rows = [[row[col_idx[v]] for v in var_order] for row in comp_pts]
                                            comp_rows = np.asarray(comp_rows, dtype=complex)

                                            for ax_local_pos, ax_idx in enumerate(combo_indices, start=1):
                                                axiom = axioms[ax_idx]
                                                ax_label = ax_idx + 1  # original 1-based index

                                                vars_sub, alphas, total_deg, monom_ct = _monomial_support_from_axiom(axiom, var_order)
                                                if not vars_sub or monom_ct == 0:
                                                    continue

                                                # project comp points to the variables actually used by the axiom
                                                try:
                                                    proj_idxs = [var_order.index(v) for v in vars_sub]
                                                except ValueError:
                                                    continue
                                                pts_sub = comp_rows[:, proj_idxs]

                                                # design matrix
                                                Phi = np.empty((len(pts_sub), len(alphas)), dtype=complex)
                                                for nrow, coord in enumerate(pts_sub):
                                                    for k, a in enumerate(alphas):
                                                        z = 1+0j
                                                        for xj, ej in zip(coord, a):
                                                            if ej:
                                                                z *= (xj ** ej)
                                                        Phi[nrow, k] = z

                                                coeffs, sigma_min = _fit_nullspace(Phi)
                                                rel_resid = None
                                                if coeffs is not None:
                                                    r = Phi @ coeffs
                                                    rel_resid = np.linalg.norm(r) / (np.linalg.norm(coeffs) + 1e-15)

                                                combo_dir = os.path.dirname(filename)
                                                out_path = os.path.join(combo_dir, f"fit_axiom{ax_label}_comp{cidx}.txt")
                                                with open(out_path, "w") as outf:
                                                    outf.write("=== Fitted relation from witness points (exact support) ===\n")
                                                    outf.write(f"Mode: per_component (component {cidx})\n")
                                                    outf.write(f"Dropped axiom original index (1-based): {ax_label}\n")
                                                    outf.write(f"Dropped axiom text: {axiom}\n")
                                                    outf.write(f"Variables used (order): {vars_sub}\n")
                                                    outf.write(f"#monomials (matched axiom): {monom_ct}\n")
                                                    outf.write(f"Total degree (matched axiom): {total_deg}\n")
                                                    outf.write(f"#points used (this component): {len(pts_sub)}\n")
                                                    if coeffs is None:
                                                        outf.write("Result: insufficient data to fit.\n")
                                                    else:
                                                        poly_str = _format_poly_with_fixed_support(vars_sub, alphas, coeffs)
                                                        outf.write(f"Smallest singular value: {sigma_min}\n")
                                                        outf.write(f"Relative residual ||A c||/||c||: {rel_resid}\n")
                                                        outf.write("Polynomial (≈ 0 on points; same monomials as missing axiom):\n")
                                                        outf.write(poly_str + " = 0\n")
                                except Exception as e:
                                    with open(os.path.splitext(filename)[0] + "_fit_error.txt", "w") as ef:
                                        ef.write(f"Fitting failed: {e}\n")

                        except TimeoutError:
                            with open(filename, 'w') as f:
                                f.write(f"Witness set skipped due to timeout after {TIMEOUT_SECONDS} seconds\n")
                            print(f"Timed out (witness set): {filename}")

        ##### Abductive Inference (if enabled) #####
        if cli.algebraicAbduction:
            measured_per_target = []
            non_measured_per_target = []
            for q in targets:
                target_vars = vars_in_poly(q, vars)
                measured_subset = [v for v in measured_vars if v in target_vars]
                non_measured_subset = [v for v in vars if v not in measured_subset]
                measured_per_target.append(measured_subset)
                non_measured_per_target.append(non_measured_subset)

            with ProcessPoolExecutor() as executor:
                indices = list(range(len(axioms)))
                for n in sorted(n_allows):
                    for combo_indices in combinations(indices, n):
                        removed_axioms = [axioms[i] for i in combo_indices]
                        remaining_axioms = [axioms[i] for i in indices if i not in combo_indices]

                        combo_str = '_'.join(str(i + 1) for i in combo_indices) if combo_indices else "none"
                        output_dir_inference = f'{output_dir}/{n}_axiom(s)_removed'
                        os.makedirs(output_dir_inference, exist_ok=True)
                        filename = os.path.join(output_dir_inference, f'abduction_{combo_str}.txt')

                        print(f"Running abductive inference by removing axioms {combo_indices}")

                        require_in_gb_literal = bool(cli.requireLiteralGB)

                        future = executor.submit(
                            run_abduction_with_timeout,
                            (vars, measured_vars, non_measured_vars, remaining_axioms,
                             targets, filename, removed_axioms, require_in_gb_literal,
                             measured_per_target, non_measured_per_target)
                        )
                        try:
                            result = future.result(timeout=TIMEOUT_SECONDS)
                            if result != "completed":
                                with open(filename, 'w') as f:
                                    f.write(f"Abduction skipped due to error: {result}\n")
                        except TimeoutError:
                            with open(filename, 'w') as f:
                                f.write(f"Abduction skipped due to timeout after {TIMEOUT_SECONDS} seconds\n")
                            print(f"Timed out: {filename}")

        ##### Dimensionality Checks (if enabled) #####
        if cli.dimensionalityCheck:
            dim_check_dir = f'{output_dir}/dimensionality_check'
            os.makedirs(dim_check_dir, exist_ok=True)
            all_aggregate_results = {}

            with ProcessPoolExecutor() as executor:
                # Dim-check historically ran for n >= 1; keep that, but intersect with chosen n's.
                chosen_for_dim = sorted({n for n in n_allows if n >= 1})
                for n in chosen_for_dim:
                    n_dir = os.path.join(dim_check_dir, f"{n}_axioms_removed")
                    os.makedirs(n_dir, exist_ok=True)

                    n_results = {
                        'total_subsets': 0,
                        'dimension_counts': {},
                        'equal_dimension': 0,
                    }

                    all_combos = list(combinations(axioms, n))
                    for count, subset in enumerate(all_combos, 1):
                        removed = list(subset)
                        filename = os.path.join(n_dir, f"subset_{count}_dimcheck.txt")
                        print(f"Running dimension check {count}/{len(all_combos)} for n={n}")

                        future = executor.submit(
                            run_dimensionality_check_with_timeout,
                            (vars, axioms, targets, removed, filename)
                        )
                        try:
                            result = future.result(timeout=TIMEOUT_SECONDS)
                            if isinstance(result, dict):
                                n_results['total_subsets'] += 1
                                dim = result['discovered_dimension']
                                n_results['dimension_counts'][dim] = n_results['dimension_counts'].get(dim, 0) + 1
                                if result['dimensions_equal']:
                                    n_results['equal_dimension'] += 1
                            else:
                                with open(filename, 'w') as f:
                                    f.write(f"Check skipped due to error: {result}\n")
                        except TimeoutError:
                            with open(filename, 'w') as f:
                                f.write(f"Check skipped due to timeout after {TIMEOUT_SECONDS} seconds\n")
                            print(f"Timed out: {filename}")

                    # Save per-n results
                    with open(os.path.join(n_dir, "aggregate_results.txt"), 'w') as f:
                        f.write(f"=== Results for removing {n} axioms ===\n")
                        f.write(f"Total subsets tested: {n_results['total_subsets']}\n")
                        f.write("Dimension distribution:\n")
                        for dim, count in sorted(n_results['dimension_counts'].items()):
                            f.write(f"  Dimension {dim}: {count} cases\n")
                        f.write(f"Cases with equal dimension: {n_results['equal_dimension']}\n")

                    all_aggregate_results[n] = n_results

                # Cross-n summary
                if all_aggregate_results:
                    total_subsets = sum(r['total_subsets'] for r in all_aggregate_results.values())
                    total_equal = sum(r['equal_dimension'] for r in all_aggregate_results.values())
                    combined_dim_counts = {}
                    for r in all_aggregate_results.values():
                        for dim, count in r['dimension_counts'].items():
                            combined_dim_counts[dim] = combined_dim_counts.get(dim, 0) + count

                    with open(os.path.join(dim_check_dir, "cross_n_aggregate.txt"), 'w') as f:
                        f.write("=== Aggregate Results Across All Subset Sizes ===\n")
                        for n, r in all_aggregate_results.items():
                            f.write(f"\nFor {n}-axiom removals:\n")
                            f.write(f"  Total subsets: {r['total_subsets']}\n")
                            f.write(f"  Equal dimensions: {r['equal_dimension']} ({r['equal_dimension']/max(r['total_subsets'],1):.1%})\n")
                            f.write("  Dimension distribution:\n")
                            for dim, count in sorted(r['dimension_counts'].items()):
                                f.write(f"    {dim}: {count}\n")
                        f.write("\n=== Grand Totals Across All Subset Sizes ===\n")
                        f.write(f"Total subsets tested: {total_subsets}\n")
                        f.write(f"Total cases with equal dimensions: {total_equal}\n")
                        pct = (total_equal/total_subsets) if total_subsets else 0.0
                        f.write(f"Percentage with equal dimensions: {pct:.1%}\n")
                        f.write("Combined dimension distribution:\n")
                        for dim, count in sorted(combined_dim_counts.items()):
                            f.write(f"  {dim}: {count} cases\n")


if __name__ == '__main__':
    main()




