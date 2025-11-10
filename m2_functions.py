import subprocess
import os

def abductive_inference(variables, measured_variables, non_measured_variables,
                        remaining_axioms, q, filename, removed_axioms):
    return abductive_inference_multi(
        variables, measured_variables, non_measured_variables,
        remaining_axioms, [q], filename, removed_axioms,
        require_in_gb_literal=True
    )

def abductive_inference_multi(variables, measured_variables, non_measured_variables,
                              remaining_axioms, targets, filename, removed_axioms,
                              require_in_gb_literal=True,
                              measured_per_target=None, non_measured_per_target=None):
    """
    Multi-target version:
      - targets: List[str] of target polynomials (all must be implied)
      - require_in_gb_literal: if True, also require each target to appear literally among the
        generators of the eliminated ideal's Groebner basis. If False, require remainder-zero
        (membership) instead.
      - measured_per_target / non_measured_per_target: optional per-target variable partitions
        (lists of lists), same length as `targets`. If omitted, the global measured/non-measured
        sets are reused for each target.
    """
    import subprocess, os

    macaulay2_path = "/opt/homebrew/bin/M2"

    # ---------- helpers to format M2 input ----------
    def m2_list(py_list):
        return ','.join(py_list) if py_list else ''

    def m2_listlist(list_of_lists):
        # Return a *fully-braced* M2 list of lists, e.g. {{a,b},{c}}
        if not list_of_lists:
            return '{}'  # empty list
        inner = []
        for sub in list_of_lists:
            inner.append('{' + m2_list(sub) + '}')
        return '{' + ','.join(inner) + '}'

    # ---------- per-target variable sets ----------
    if measured_per_target is None:
        measured_per_target = [measured_variables for _ in targets]
    if non_measured_per_target is None:
        non_measured_per_target = [non_measured_variables for _ in targets]

    measuredPT_m2 = m2_listlist(measured_per_target)        # e.g. {{c,F0},{c,F}}
    nonMeasuredPT_m2 = m2_listlist(non_measured_per_target) # e.g. {{d,dt,...},{...}}

    # ---------- Macaulay2 program ----------
    macaulay2_script = f"""
    needsPackage("PrimaryDecomposition", Reload => true)

    -- Ring
    R = QQ[{m2_list(variables)}, MonomialOrder => Lex];
    print("Ring defined: " | toString R);

    -- Sets
    remainingAxioms       = toList([{m2_list(remaining_axioms)}]);
    removedAxioms         = toList([{m2_list(removed_axioms)}]);
    measuredVariables     = toList([{m2_list(measured_variables)}]);
    nonMeasuredVariables  = toList([{m2_list(non_measured_variables)}]);

    -- Targets (multiple)
    qList = toList([{m2_list(targets)}]);
    print("Targets defined: " | toString qList);

    -- Per-target measured/non-measured lists (same length as qList)
    measuredPerTarget    = {measuredPT_m2};
    nonMeasuredPerTarget = {nonMeasuredPT_m2};
    k = #qList;

    -- Empty combo (the baseline: add nothing from component generators)
    empty = {{}};

    -- Ideal with ALL remaining axioms + ALL targets (for PD context)
    I = ideal(join(remainingAxioms, qList));
    print("Ideal defined: " | toString I);

    PD = primaryDecomposition I;
    print("Primary decomposition computed");

    -- Helpers
    isInIdeal = (poly, base) -> (
        M = ideal(base);
        G = gens gb M;
        poly % ideal(G) == 0
    );

    allInIdeal = (polys, base) -> all(polys, p -> isInIdeal(p, base));

    -- Per-target eliminated checks
    appearsInGBExactlyIdx = (i, combo) -> (
        M = ideal(join(remainingAxioms, combo));
        eliminatedIdeal = eliminate(nonMeasuredPerTarget#i, M);
        GBproj = gens gb eliminatedIdeal;
        member(true, toList apply(flatten entries GBproj, g -> g == (qList#i)))
    );

    inEliminatedIdealIdx = (i, combo) -> (
        M = ideal(join(remainingAxioms, combo));
        eliminatedIdeal = eliminate(nonMeasuredPerTarget#i, M);
        GBproj = gens gb eliminatedIdeal;
        (qList#i) % ideal(GBproj) == 0
    );

    allAppearInGBExactlyPT = (combo) ->
        all(toList(0..(k-1)), i -> appearsInGBExactlyIdx(i, combo));

    allInEliminatedIdealPT = (combo) ->
        all(toList(0..(k-1)), i -> inEliminatedIdealIdx(i, combo));

    -- Output file
    f = openOut "decomposition_analysis.txt";
    f << "Removed Axioms:" << endl;
    scan(removedAxioms, a -> f << toString a << endl);
    f << "Remaining Axioms:" << endl;
    scan(remainingAxioms, a -> f << toString a << endl);
    f << "Targets qList:" << endl;
    scan(qList, q -> f << toString q << endl);
    f << endl;

    savedCombos = {{}};
    strongCandidates = {{}};
    n = #removedAxioms;
    maxSize = n + k;

    scan(PD, J -> (
        f << "Ideal component: " << toString J << endl;
        idealGens = flatten entries gens J;
        idealGensList = toList idealGens;
        f << "  Found " << toString(#idealGensList) << " generators" << endl;

        limit = if maxSize < #idealGensList then maxSize else #idealGensList;
        combos = flatten for i from 0 to limit list subsets(idealGensList, i);
        f << "  Testing " << toString(#combos) << " combinations" << endl;

        scan(combos, combo -> (
            f << "  Trying combination: " << toString combo << endl;

            -- Filter out polynomials already implied by remaining axioms
            filteredCombo = select(combo, p -> not isInIdeal(p, remainingAxioms));
            f << "    Filtered combo: " << toString filteredCombo << endl;

            if #filteredCombo == 0 then (
                if #combo == 0 then (
                    -- Baseline: remaining axioms alone (no extra generators)
                    if allInEliminatedIdealPT(empty) then (
                        f << "    Base: remaining axioms alone imply ALL targets (per-target projections)" << endl;

                        if not member(empty, savedCombos) then savedCombos = append(savedCombos, empty);

                        if {"true" if require_in_gb_literal else "false"} then (
                            if allAppearInGBExactlyPT(empty) then (
                                f << "    Base also STRONG (literal appearance in each target's eliminated GB)" << endl;
                                if not member(empty, strongCandidates) then strongCandidates = append(strongCandidates, empty);
                            ) else (
                                f << "    Base not strong under literal-appearance check" << endl;
                            )
                        ) else (
                            -- remainder-zero already required to be saved; treat as strong too
                            f << "    Base also STRONG (remainder-zero criterion)" << endl;
                            if not member(empty, strongCandidates) then strongCandidates = append(strongCandidates, empty);
                        );
                    ) else (
                        f << "    Base: remaining axioms alone do NOT imply all targets" << endl;
                    );
                ) else (
                    f << "    Skipping: all combo elements already implied" << endl;
                );
            ) else (
                if allInEliminatedIdealPT(filteredCombo) then (
                    f << "    filteredCombo implies ALL targets (per-target projections)" << endl;

                    if not member(filteredCombo, savedCombos) then (
                        filteredCombo = sort filteredCombo;
                        savedCombos = append(savedCombos, filteredCombo);
                    );

                    if {"true" if require_in_gb_literal else "false"} then (
                        if allAppearInGBExactlyPT(filteredCombo) then (
                            f << "    Also STRONG: ALL targets appear literally in each target's eliminated GB" << endl;
                            if not member(filteredCombo, strongCandidates) then (
                                strongCandidates = append(strongCandidates, filteredCombo);
                            );
                        ) else (
                            f << "    Not STRONG under literal-appearance check" << endl;
                        )
                    ) else (
                        -- remainder-zero already required via allInEliminatedIdealPT => mark strong
                        f << "    Also STRONG by remainder-zero criterion" << endl;
                        if not member(filteredCombo, strongCandidates) then (
                            strongCandidates = append(strongCandidates, filteredCombo);
                        );
                    );
                ) else (
                    f << "    filteredCombo does NOT imply all targets" << endl;
                );
            );
        ));
    ));

    f << "Saved Polynomials (combos implying ALL targets):" << endl;
    scan(savedCombos, g -> f << toString g << endl);

    f << "Strong Candidates:" << endl;
    scan(strongCandidates, g -> f << toString g << endl);

    close f;
    """

    # ---------- write, run, collect ----------
    script_path = "temp_script.m2"
    with open(script_path, "w") as fh:
        fh.write(macaulay2_script)

    result = subprocess.run([macaulay2_path, "--script", script_path], capture_output=True, text=True)
    try:
        os.remove(script_path)
    except Exception:
        pass

    if result.stdout:
        print("M2 STDOUT:\n", result.stdout)
    if result.stderr:
        print("M2 STDERR:\n", result.stderr)

    try:
        with open("decomposition_analysis.txt", "r") as f:
            os.makedirs(os.path.dirname(filename), exist_ok=True)
            os.replace("decomposition_analysis.txt", filename)
            return f.read()
    except FileNotFoundError:
        return "Error: 'decomposition_analysis.txt' not found."

def projection(variables, axioms, measured_variables, non_measured_variables, filename, targets=None):
    """
    Unchanged output + if `targets` is provided (List[str]), we also:
      - check each target's remainder zero modulo eliminated GB,
      - and whether it appears literally in the eliminated GB generators.
    """
    macaulay2_path = "/opt/homebrew/bin/M2"

    def m2_list(py_list):
        return ','.join(py_list) if py_list else ''

    targets_list = m2_list(targets or [])

    macaulay2_script = f"""
    R = QQ[{m2_list(variables)}, MonomialOrder => Lex];
    axioms = toList([{m2_list(axioms)}]);
    measuredVariables = toList([{m2_list(measured_variables)}]);
    nonMeasuredVariables = toList([{m2_list(non_measured_variables)}]);

    I = ideal(axioms);
    GB = gens gb I;

    eliminatedIdeal = eliminate(nonMeasuredVariables, I);
    GBproj = gens gb eliminatedIdeal;

    f = openOut "projection_analysis.txt";
    f << "Gröbner basis of the ideal:" << endl;
    f << toString GB << endl << endl;
    f << "Gröbner basis of the eliminated ideal:" << endl;
    f << toString GBproj << endl << endl;

    f << "Polynomials of the eliminated GB (flattened):" << endl;
    scan(flatten entries GBproj, g -> f << toString g << endl);
    f << endl;

    -- Optional multi-target checks
    if ({'true' if targets else 'false'}) then (
        qList = toList([{targets_list}]);
        f << "Target checks in eliminated ideal (membership & literal appearance):" << endl;
        scan(qList, q -> (
            remZero = (q % ideal(GBproj) == 0);
            appears = member(true, toList apply(flatten entries GBproj, g -> g == q));
            f << "q = " << toString q << endl;
            f << "  remainderZero: " << toString remZero << endl;
            f << "  appearsLiterallyInGB: " << toString appears << endl;
        ));
    );

    close f;
    """

    script_path = "temp_script.m2"
    with open(script_path, "w") as file:
        file.write(macaulay2_script)

    result = subprocess.run([macaulay2_path, "--script", script_path], capture_output=True, text=True)
    try:
        os.remove(script_path)
    except Exception:
        pass

    if result.stdout:
        print("Output from Macaulay2:")
        print(result.stdout)
    if result.stderr:
        print("Errors:")
        print(result.stderr)

    try:
        with open("projection_analysis.txt", "r") as file:
            os.makedirs(os.path.dirname(filename), exist_ok=True)
            os.replace("projection_analysis.txt", filename)
            return file.read()
    except FileNotFoundError:
        return "Error: The file 'projection_analysis.txt' was not found."

def check_axiom_dimensions_multi(variables, all_axioms, targets, removed_axioms, filename="axiom_dimensions.txt"):
    """
    Compare:
      - dim(ideal(all_axioms))
      - dim(ideal(all_axioms \ removed_axioms))
      - dim(ideal(remaining_axioms + ALL targets))  # NEW
    """
    macaulay2_path = "/opt/homebrew/bin/M2"

    def fmt_list(xs):
        return ','.join(xs) if xs else ''

    macaulay2_script = f"""
    needsPackage("PrimaryDecomposition");

    R = QQ[{fmt_list(variables)}, MonomialOrder => Lex];

    allAxioms = {{{fmt_list(all_axioms)}}};
    targetList = {{{fmt_list(targets)}}};

    I = ideal(allAxioms);
    originalDim = dim I;

    remainingAxioms = allAxioms;
    {''.join([f'remainingAxioms = delete({ax}, remainingAxioms);' + chr(10) for ax in removed_axioms])}

    Ireduced = ideal(remainingAxioms);
    reducedDim = dim Ireduced;

    remainingWithTargets = apply(targetList, t -> t) | remainingAxioms;
    Idiscovered = ideal(remainingWithTargets);
    discoveredDim = dim Idiscovered;

    f = openOut "temp.txt";
    f << "Original dimension: " << originalDim << endl;
    f << "Reduced dimension: " << reducedDim << endl;
    f << "Discovered dimension: " << discoveredDim << endl;
    f << "Removed axioms: " << toString({{{fmt_list(removed_axioms)}}}) << endl;
    f << "Remaining axioms: " << toString(remainingAxioms) << endl;
    f << "Targets: " << toString(targetList) << endl;
    close f;
    """

    script_path = "temp_dimension_script.m2"
    with open(script_path, "w") as file:
        file.write(macaulay2_script)

    result = subprocess.run([macaulay2_path, "--script", script_path], capture_output=True, text=True)
    try:
        os.remove(script_path)
    except Exception:
        pass

    try:
        with open("temp.txt", "r") as f:
            temp_content = f.read()

        original_dim = reduced_dim = discovered_dim = None
        removed_axioms_list = []
        remaining_axioms_list = []
        targets_list = []

        for line in temp_content.split('\n'):
            if line.startswith("Original dimension:"):
                original_dim = int(line.split(':', 1)[1].strip())
            elif line.startswith("Reduced dimension:"):
                reduced_dim = int(line.split(':', 1)[1].strip())
            elif line.startswith("Discovered dimension:"):
                discovered_dim = int(line.split(':', 1)[1].strip())
            elif line.startswith("Removed axioms:"):
                s = line.split(':', 1)[1].strip()
                removed_axioms_list = [a.strip().strip('"') for a in s[1:-1].split(',')] if s.startswith('{') else []
            elif line.startswith("Remaining axioms:"):
                s = line.split(':', 1)[1].strip()
                remaining_axioms_list = [a.strip().strip('"') for a in s[1:-1].split(',')] if s.startswith('{') else []
            elif line.startswith("Targets:"):
                s = line.split(':', 1)[1].strip()
                targets_list = [a.strip().strip('"') for a in s[1:-1].split(',')] if s.startswith('{') else []

        dimensions_equal = (original_dim == discovered_dim)

        with open(filename, "a") as f:
            f.write("\n=== Dimension Analysis ===\n")
            f.write(f"Original dimension: {original_dim}\n")
            f.write(f"Removed axioms: {removed_axioms_list}\n")
            f.write(f"Remaining axioms: {remaining_axioms_list}\n")
            f.write(f"Reduced dimension: {reduced_dim}\n")
            f.write(f"Targets: {targets_list}\n")
            f.write(f"Discovered dimension: {discovered_dim}\n")
            f.write(f"Original == Discovered: {dimensions_equal}\n")

        os.remove("temp.txt")

        return {
            "original_dimension": original_dim,
            "reduced_dimension": reduced_dim,
            "discovered_dimension": discovered_dim,
            "removed_axioms": removed_axioms_list,
            "remaining_axioms": remaining_axioms_list,
            "targets": targets_list,
            "dimensions_equal": dimensions_equal
        }

    except FileNotFoundError:
        print("Error: temp.txt not found")
        return None
    except Exception as e:
        print(f"Error processing results: {e}")
        return None

def witness_set_nag(variables, remaining_axioms, targets, filename,
                    macaulay2_path="/opt/homebrew/bin/M2",
                    samples_per_component: int = 100):
    def m2_list(py_list):
        return ','.join(py_list) if py_list else ''

    macaulay2_script = f'''
    needsPackage("NumericalAlgebraicGeometry", Reload => true)

    -- Work over CC for numerical algebraic geometry
    R = CC[{m2_list(variables)}, MonomialOrder => Lex];

    remainingAxioms = toList([{m2_list(remaining_axioms)}]);
    qList           = toList([{m2_list(targets)}]);

    I = ideal(join(remainingAxioms, qList));

    -- Numerical irreducible decomposition
    W  = numericalIrreducibleDecomposition I;
    Ws = components W;

    -- Variables in ring order
    varList = flatten entries vars R;

    -- Target #points per component (witness + sampled)
    targetCount = {int(samples_per_component)};

    f = openOut "witness_set.txt";
    f << "variable ordering: ";
    for i from 0 to #varList - 1 do (
        f << toString(varList#i);
        if i < #varList - 1 then f << ", ";
    );
    f << endl << endl;

    for i from 0 to #Ws - 1 do (
        Wi = Ws#i;
        f << "component_" << toString(i+1) << ":" << endl;

        -- Equations
        f << "equations:" << endl;
        eqsList = equations Wi;
        scan(eqsList, e -> f << toString e << endl);

        -- Collect witness points (if available)
        ptsList = {{}};
        try (
            pts0 = points Wi;               -- list of Point
            ptsList = toList pts0;
        ) else (
            ptsList = {{}};
        );

        -- Top up to targetCount by sampling additional points on Wi
        added = 0;
        attempts = 0;
        maxAttempts = 5 * targetCount;     -- be generous to tolerate occasional failures
        while (#ptsList < targetCount and attempts < maxAttempts) do (
            attempts = attempts + 1;
            try (
                p = sample Wi;             -- sample a Point on the component
                ptsList = append(ptsList, p);
                added = added + 1;
            ) else (
                -- ignore failed sample and continue
                1;
            );
        );

        -- Points as CSV of coordinates (avoid printing the Point objects)
        f << "points:" << endl;            -- keep exact label so existing parser works
        scan(ptsList, P -> (
            C = coordinates P;             -- list of coordinates
            for j from 0 to #C - 1 do (
                f << toString(C#j);
                if j < #C - 1 then f << ", ";
            );
            f << endl;
        ));
        f << endl;
    );

    close f;
    '''

    script_path = "temp_witness_script.m2"
    with open(script_path, "w") as fh:
        fh.write(macaulay2_script)

    result = subprocess.run([macaulay2_path, "--script", script_path], capture_output=True, text=True)
    try:
        os.remove(script_path)
    except Exception:
        pass

    if result.stdout:
        print("M2 (witness) STDOUT:\n", result.stdout)
    if result.stderr:
        print("M2 (witness) STDERR:\n", result.stderr)

    try:
        with open("witness_set.txt", "r") as f:
            txt = f.read()
        os.makedirs(os.path.dirname(filename), exist_ok=True)
        os.replace("witness_set.txt", filename)
        return txt
    except FileNotFoundError:
        return "Error: 'witness_set.txt' not found."


