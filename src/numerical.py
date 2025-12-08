"""
AI-Noether: Numerical abduction functions

This module handles:
- Witness set computation (numerical irreducible decomposition)
- Symbolic regression on sampled points
- Coefficient normalization
- KeyMaera template generation
"""

import subprocess
import os
import numpy as np
from typing import List, Dict, Any, Optional, Tuple
from pathlib import Path
from itertools import product
from dataclasses import dataclass

from sympy import symbols as sp_symbols, sympify as sp_sympify, Poly as SpPoly

from .config import Config
from .templates import fill_m2_witness_set_template, fill_keymaera_reasoning_template
from .parsers import parse_m2_witness_set_output, WitnessSetResult, WitnessSetComponent
from .logging_utils import get_logger, log_subprocess_result


@dataclass
class SymbolicRegressionResult:
    """Result of symbolic regression on witness set points."""
    axiom_index: int  # Original 1-based index of the dropped axiom
    axiom_text: str
    component_index: int
    variables: List[str]
    monomials: List[Tuple[int, ...]]  # Exponent tuples
    coefficients: np.ndarray  # Complex coefficients
    coefficients_normalized: np.ndarray  # Normalized so max magnitude = 1
    singular_value: float
    relative_residual: float
    polynomial_string: str
    polynomial_string_normalized: str
    
    # Robust fitting info
    num_points_total: int = 0
    num_points_used: int = 0  # Inliers after outlier removal
    
    # Comparison with true axiom (if available)
    true_coefficients_normalized: Optional[np.ndarray] = None
    coefficient_l2_error: Optional[float] = None


def monomial_support_from_axiom(axiom: str, all_vars: List[str]) -> Tuple[List[str], List[Tuple[int, ...]], int, int]:
    """
    Extract monomial support from an axiom string.
    
    Returns:
        vars_sub: Variables that appear in the axiom
        alphas: List of exponent tuples for each monomial
        total_deg: Total degree of the polynomial
        monom_ct: Number of monomials
    """
    expr_str = axiom.replace('^', '**')
    sym_list = sp_symbols(' '.join(all_vars))
    sym_map = {str(s): s for s in sym_list}
    expr = sp_sympify(expr_str, locals=sym_map)
    
    poly = SpPoly(expr, *[sym_map[v] for v in all_vars], domain='EX')
    
    # Variables that actually appear with positive degree
    vars_sub = []
    idxs_sub = []
    for i, v in enumerate(all_vars):
        d = poly.degree(sym_map[v])
        if d is not None and d > 0:
            vars_sub.append(v)
            idxs_sub.append(i)
    
    # Monomial support
    monoms_full = poly.monoms()
    alphas = [tuple(m[i] for i in idxs_sub) for m in monoms_full]
    
    total_deg = poly.total_degree()
    monom_ct = len(alphas)
    
    return vars_sub, alphas, total_deg, monom_ct


def normalize_coefficients(
    coeffs: np.ndarray, 
    complex_threshold: float = 1e-6
) -> np.ndarray:
    """
    Normalize coefficients so the largest has magnitude 1.
    Also zero out small imaginary parts.
    
    Args:
        coeffs: Array of complex coefficients
        complex_threshold: If |imag(c)| < threshold, set imag(c) = 0
    
    Returns:
        Normalized coefficient array
    """
    # Find the coefficient with largest magnitude
    max_idx = np.argmax(np.abs(coeffs))
    max_val = coeffs[max_idx]
    
    if np.abs(max_val) < 1e-15:
        return coeffs  # Avoid division by zero
    
    # Normalize so max coefficient = 1
    normalized = coeffs / max_val
    
    # Zero out small imaginary parts
    for i in range(len(normalized)):
        if np.abs(normalized[i].imag) < complex_threshold:
            normalized[i] = normalized[i].real + 0j
    
    return normalized


def compute_coefficient_error(
    inferred: np.ndarray,
    true_coeffs: np.ndarray,
    monomials_inferred: List[Tuple[int, ...]],
    monomials_true: List[Tuple[int, ...]]
) -> float:
    """
    Compute L2 norm of difference between normalized coefficient vectors.
    
    Both vectors are normalized to have max coefficient = 1.
    Coefficients are matched by their monomial exponent tuples.
    
    Returns:
        L2 norm of the difference
    """
    # Normalize both
    inferred_norm = normalize_coefficients(inferred.copy())
    true_norm = normalize_coefficients(true_coeffs.copy())
    
    # Create dict mapping monomial -> coefficient for true
    true_dict = {m: c for m, c in zip(monomials_true, true_norm)}
    
    # Compute difference for matching monomials
    diff_sq = 0.0
    matched = 0
    
    for m, c_inf in zip(monomials_inferred, inferred_norm):
        if m in true_dict:
            c_true = true_dict[m]
            diff_sq += np.abs(c_inf - c_true) ** 2
            matched += 1
        else:
            # Monomial not in true - penalize
            diff_sq += np.abs(c_inf) ** 2
    
    # Also penalize monomials in true but not in inferred
    inferred_set = set(monomials_inferred)
    for m, c_true in zip(monomials_true, true_norm):
        if m not in inferred_set:
            diff_sq += np.abs(c_true) ** 2
    
    return np.sqrt(diff_sq)


def fit_nullspace(A: np.ndarray) -> Tuple[Optional[np.ndarray], Optional[float], Optional[float]]:
    """
    Compute the smallest right-singular vector of A (find x such that Ax ≈ 0).
    
    Returns:
        coeffs: Coefficient vector (normalized so max |c| = 1)
        sigma_min: Smallest singular value
        rel_resid: Relative residual ||Ax|| / ||x||
    """
    if A.size == 0:
        return None, None, None
    
    U, s, Vh = np.linalg.svd(A, full_matrices=False)
    x = Vh[-1, :]
    
    # Normalize so max |x| = 1
    if np.max(np.abs(x)) > 0:
        x = x / np.max(np.abs(x))
    
    sigma_min = s[-1] if len(s) else None
    
    # Compute relative residual
    r = A @ x
    rel_resid = np.linalg.norm(r) / (np.linalg.norm(x) + 1e-15)
    
    return x, sigma_min, rel_resid


def fit_nullspace_robust(
    A: np.ndarray,
    outlier_percentile: float = 90.0,
    max_iterations: int = 5,
    min_points: int = 5
) -> Tuple[Optional[np.ndarray], Optional[float], Optional[float], np.ndarray]:
    """
    Robust null-space fitting with iterative outlier removal.
    
    Uses iterative reweighting: fit, compute residuals, remove worst points, repeat.
    
    Args:
        A: Design matrix (n_points x n_monomials)
        outlier_percentile: Remove points with residual above this percentile (0-100)
        max_iterations: Maximum number of outlier removal iterations
        min_points: Minimum number of points to keep (stop if fewer remain)
    
    Returns:
        coeffs: Coefficient vector (normalized so max |c| = 1)
        sigma_min: Smallest singular value (on final inlier set)
        rel_resid: Relative residual on final inlier set
        inlier_mask: Boolean array indicating which rows were kept
    """
    if A.size == 0 or A.shape[0] < min_points:
        return None, None, None, np.array([], dtype=bool)
    
    n_rows = A.shape[0]
    inlier_mask = np.ones(n_rows, dtype=bool)
    
    for iteration in range(max_iterations):
        A_subset = A[inlier_mask]
        
        if A_subset.shape[0] < min_points:
            break
        
        # Fit on current inliers
        U, s, Vh = np.linalg.svd(A_subset, full_matrices=False)
        x = Vh[-1, :]
        
        # Normalize
        if np.max(np.abs(x)) > 0:
            x = x / np.max(np.abs(x))
        
        # Compute per-row residuals on ALL points
        residuals = np.abs(A @ x)
        
        # Compute threshold based on current inliers only
        inlier_residuals = residuals[inlier_mask]
        threshold = np.percentile(inlier_residuals, outlier_percentile)
        
        # Update inlier mask
        new_mask = residuals <= threshold
        
        # Ensure we keep at least min_points
        if np.sum(new_mask) < min_points:
            # Keep the min_points with smallest residuals
            sorted_idx = np.argsort(residuals)
            new_mask = np.zeros(n_rows, dtype=bool)
            new_mask[sorted_idx[:min_points]] = True
        
        # Check for convergence
        if np.array_equal(new_mask, inlier_mask):
            break
        
        inlier_mask = new_mask
    
    # Final fit on inliers
    A_final = A[inlier_mask]
    if A_final.shape[0] < 2:
        return None, None, None, inlier_mask
    
    U, s, Vh = np.linalg.svd(A_final, full_matrices=False)
    x = Vh[-1, :]
    
    if np.max(np.abs(x)) > 0:
        x = x / np.max(np.abs(x))
    
    sigma_min = s[-1] if len(s) else None
    
    r = A_final @ x
    rel_resid = np.linalg.norm(r) / (np.linalg.norm(x) + 1e-15)
    
    return x, sigma_min, rel_resid, inlier_mask


def format_polynomial(
    var_names: List[str],
    alphas: List[Tuple[int, ...]],
    coeffs: np.ndarray,
    tol: float = 1e-10
) -> str:
    """Format a polynomial as a human-readable string."""
    terms = []
    
    for c, a in zip(coeffs, alphas):
        if np.abs(c) < tol:
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
        
        mono = '*'.join(mono_parts) if mono_parts else '1'
        
        # Format coefficient
        if np.abs(c.imag) < tol:
            c_str = f"{c.real:.6g}"
        else:
            c_str = f"({c.real:.6g}{'+' if c.imag >= 0 else ''}{c.imag:.6g}i)"
        
        terms.append(f"{c_str}*{mono}")
    
    return ' + '.join(terms) if terms else '0'


def run_witness_set_computation(
    variables: List[str],
    remaining_axioms: List[str],
    targets: List[str],
    output_dir: str,
    config: Config
) -> Optional[WitnessSetResult]:
    """
    Run numerical irreducible decomposition to compute witness sets.
    
    Args:
        variables: List of variable names
        remaining_axioms: List of remaining axiom equations
        targets: List of target polynomials
        output_dir: Directory to save outputs
        config: Configuration object
    
    Returns:
        WitnessSetResult or None if failed
    """
    logger = get_logger()
    
    os.makedirs(output_dir, exist_ok=True)
    
    # Output files
    witness_output = os.path.join(output_dir, "witness_set.txt")
    script_path = os.path.join(output_dir, "witness_script.m2")
    
    # Fill template
    script_content = fill_m2_witness_set_template(
        variables=variables,
        remaining_axioms=remaining_axioms,
        targets=targets,
        samples_per_component=config.numerical.samples_per_component,
        engine=config.numerical.engine,
        bertini_path=config.paths.bertini,
        output_file=witness_output
    )
    
    # Write script
    with open(script_path, 'w') as f:
        f.write(script_content)
    
    logger.info(f"Running witness set computation, script: {script_path}")
    
    # Run Macaulay2
    try:
        result = subprocess.run(
            [config.paths.macaulay2, "--script", script_path],
            capture_output=True,
            text=True,
            timeout=config.execution.timeout_witness_set
        )
        
        log_subprocess_result(
            cmd=f"{config.paths.macaulay2} --script {script_path}",
            returncode=result.returncode,
            stdout=result.stdout,
            stderr=result.stderr,
            context="Witness Set"
        )
        
        # Read output file
        if os.path.exists(witness_output):
            with open(witness_output, 'r') as f:
                output_content = f.read()
            
            return parse_m2_witness_set_output(output_content)
        else:
            logger.error(f"Witness set output file not found: {witness_output}")
            return None
            
    except subprocess.TimeoutExpired:
        logger.error(f"Witness set computation timed out after {config.execution.timeout_witness_set}s")
        return None
    except Exception as e:
        logger.error(f"Witness set computation failed: {e}")
        return None


def perform_symbolic_regression(
    witness_result: WitnessSetResult,
    dropped_axioms: List[str],
    dropped_indices: List[int],
    all_axioms: List[str],
    output_dir: str,
    config: Config
) -> List[SymbolicRegressionResult]:
    """
    Perform symbolic regression on witness set points for each dropped axiom.
    
    For each dropped axiom and each component, fit a polynomial with the
    same monomial support as the dropped axiom.
    
    Args:
        witness_result: Result from witness set computation
        dropped_axioms: List of dropped axiom strings
        dropped_indices: Original 0-based indices of dropped axioms
        all_axioms: List of all axioms (for reference)
        output_dir: Directory to save outputs
        config: Configuration object
    
    Returns:
        List of SymbolicRegressionResult objects
    """
    logger = get_logger()
    
    os.makedirs(output_dir, exist_ok=True)
    results = []
    
    var_order = witness_result.variable_order
    
    # Create column index mapping
    col_idx = {v: i for i, v in enumerate(var_order)}
    
    for comp in witness_result.components:
        if not comp.points:
            continue
        
        # Convert points to numpy array
        comp_rows = np.array(comp.points, dtype=complex)
        
        for ax_local_pos, ax_idx in enumerate(dropped_indices):
            axiom = all_axioms[ax_idx]
            ax_label = ax_idx + 1  # 1-based
            
            try:
                vars_sub, alphas, total_deg, monom_ct = monomial_support_from_axiom(axiom, var_order)
            except Exception as e:
                logger.warning(f"Could not parse axiom {ax_label}: {e}")
                continue
            
            if not vars_sub or monom_ct == 0:
                continue
            
            # Project points to variables in this axiom
            try:
                proj_idxs = [col_idx[v] for v in vars_sub]
            except KeyError as e:
                logger.warning(f"Variable not found in ring: {e}")
                continue
            
            pts_sub = comp_rows[:, proj_idxs]
            
            # Build design matrix
            Phi = np.empty((len(pts_sub), len(alphas)), dtype=complex)
            for nrow, coord in enumerate(pts_sub):
                for k, a in enumerate(alphas):
                    z = 1 + 0j
                    for xj, ej in zip(coord, a):
                        if ej:
                            z *= (xj ** ej)
                    Phi[nrow, k] = z
            
            # Fit nullspace (robust or standard)
            num_points_total = Phi.shape[0]
            num_points_used = num_points_total
            
            if config.robust_fitting.enabled:
                coeffs, sigma_min, rel_resid, inlier_mask = fit_nullspace_robust(
                    Phi,
                    outlier_percentile=float(config.robust_fitting.outlier_percentile),
                    max_iterations=int(config.robust_fitting.max_iterations),
                    min_points=int(config.robust_fitting.min_points)
                )
                if inlier_mask is not None and len(inlier_mask) > 0:
                    num_points_used = int(np.sum(inlier_mask))
                    logger.debug(f"Robust fitting: {num_points_used}/{num_points_total} points used")
            else:
                coeffs, sigma_min, rel_resid = fit_nullspace(Phi)
            
            if coeffs is None:
                continue
            
            # Normalize
            coeffs_normalized = normalize_coefficients(
                coeffs.copy(),
                complex_threshold=float(config.normalization.complex_threshold)
            )
            
            # Format polynomials
            poly_str = format_polynomial(vars_sub, alphas, coeffs)
            poly_str_norm = format_polynomial(vars_sub, alphas, coeffs_normalized)
            
            # Compute error vs true axiom if requested
            true_coeffs_norm = None
            coeff_error = None
            
            if config.normalization.compute_coefficient_error:
                try:
                    # Get true coefficients from axiom
                    true_coeffs = get_true_coefficients(axiom, vars_sub, alphas)
                    if true_coeffs is not None:
                        true_coeffs_norm = normalize_coefficients(
                            true_coeffs.copy(),
                            complex_threshold=float(config.normalization.complex_threshold)
                        )
                        coeff_error = compute_coefficient_error(
                            coeffs_normalized, true_coeffs_norm,
                            alphas, alphas
                        )
                except Exception as e:
                    logger.debug(f"Could not compute coefficient error: {e}")
            
            result = SymbolicRegressionResult(
                axiom_index=ax_label,
                axiom_text=axiom,
                component_index=comp.index,
                variables=vars_sub,
                monomials=alphas,
                coefficients=coeffs,
                coefficients_normalized=coeffs_normalized,
                singular_value=sigma_min or 0.0,
                relative_residual=rel_resid or 0.0,
                polynomial_string=poly_str,
                polynomial_string_normalized=poly_str_norm,
                num_points_total=num_points_total,
                num_points_used=num_points_used,
                true_coefficients_normalized=true_coeffs_norm,
                coefficient_l2_error=coeff_error
            )
            
            results.append(result)
            
            # Save individual result
            out_path = os.path.join(output_dir, f"fit_axiom{ax_label}_comp{comp.index}.txt")
            with open(out_path, 'w') as f:
                f.write("=== Symbolic Regression Result ===\n")
                f.write(f"Dropped axiom index (1-based): {ax_label}\n")
                f.write(f"Dropped axiom text: {axiom}\n")
                f.write(f"Component index: {comp.index}\n")
                f.write(f"Variables: {vars_sub}\n")
                f.write(f"Number of monomials: {monom_ct}\n")
                f.write(f"Total degree: {total_deg}\n")
                f.write(f"Number of points (total): {num_points_total}\n")
                f.write(f"Number of points (used after outlier removal): {num_points_used}\n")
                f.write(f"Smallest singular value: {sigma_min}\n")
                f.write(f"Relative residual: {rel_resid}\n")
                f.write(f"\nInferred polynomial (raw):\n  {poly_str} = 0\n")
                f.write(f"\nInferred polynomial (normalized):\n  {poly_str_norm} = 0\n")
                if coeff_error is not None:
                    f.write(f"\nCoefficient L2 error vs true: {coeff_error}\n")
    
    return results


def get_true_coefficients(
    axiom: str,
    vars_sub: List[str],
    alphas: List[Tuple[int, ...]]
) -> Optional[np.ndarray]:
    """
    Extract the true coefficients from an axiom string.
    
    Returns array of coefficients aligned with the given monomials.
    """
    expr_str = axiom.replace('^', '**')
    sym_list = sp_symbols(' '.join(vars_sub))
    sym_map = {str(s): s for s in sym_list}
    
    try:
        expr = sp_sympify(expr_str, locals=sym_map)
        poly = SpPoly(expr, *[sym_map[v] for v in vars_sub], domain='EX')
        
        # Get coefficients for each monomial
        coeffs = []
        coeff_dict = poly.as_dict()
        
        for alpha in alphas:
            if alpha in coeff_dict:
                coeffs.append(complex(coeff_dict[alpha]))
            else:
                coeffs.append(0.0 + 0j)
        
        return np.array(coeffs, dtype=complex)
    except Exception:
        return None


def get_monomials_from_polynomial(poly_str: str, variables: List[str]) -> List[str]:
    """
    Extract monomial strings from a polynomial.
    
    Returns list of monomial strings like ['x^2', 'x*y', 'y^2', '1']
    """
    # This is a simplified version - for KeyMaera we need the actual monomials
    expr_str = poly_str.replace('^', '**')
    sym_list = sp_symbols(' '.join(variables))
    sym_map = {str(s): s for s in sym_list}
    
    try:
        expr = sp_sympify(expr_str, locals=sym_map)
        poly = SpPoly(expr, *[sym_map[v] for v in variables], domain='EX')
        
        monomials = []
        for monom in poly.monoms():
            parts = []
            for v, e in zip(variables, monom):
                if e == 0:
                    continue
                elif e == 1:
                    parts.append(v)
                else:
                    parts.append(f"{v}^{e}")
            
            mono_str = '*'.join(parts) if parts else '1'
            monomials.append(mono_str)
        
        return monomials
    except Exception:
        return []


def generate_keymaera_script(
    problem_name: str,
    target_index: int,
    axiom_combo: str,
    variables: List[str],
    known_axioms: List[str],
    regression_results: List[SymbolicRegressionResult],
    target: str,
    output_dir: str,
    config: Config
) -> Optional[str]:
    """
    Generate a KeyMaera script for noisy reasoning.
    
    Only generates script for regression results with good fit quality
    (singular value below threshold).
    
    Args:
        problem_name: Name of the physics problem
        target_index: Index of the target (1-based)
        axiom_combo: String identifying axiom combination
        variables: List of variable names
        known_axioms: List of known axiom equations
        regression_results: List of symbolic regression results
        target: Target polynomial string
        output_dir: Directory to save outputs
        config: Configuration object
    
    Returns:
        Path to generated script or None if not generated
    """
    logger = get_logger()
    
    # Filter to good fits (ensure threshold is float for comparison)
    threshold = float(config.numerical.singular_value_threshold)
    good_fits = [r for r in regression_results 
                 if r.singular_value < threshold]
    
    if not good_fits:
        logger.info(f"No regression results below threshold {threshold}")
        return None
    
    os.makedirs(output_dir, exist_ok=True)
    
    # Build abducted axioms structure for template
    abducted_axioms = []
    coeff_idx = 1
    
    for fit in good_fits:
        monomials = []
        for alpha in fit.monomials:
            parts = []
            for v, e in zip(fit.variables, alpha):
                if e == 0:
                    continue
                elif e == 1:
                    parts.append(v)
                else:
                    parts.append(f"{v}^{e}")
            mono = '*'.join(parts) if parts else '1'
            monomials.append(mono)
        
        abducted_axioms.append({
            'monomials': monomials,
            'coeff_prefix': f'c{fit.axiom_index}_'
        })
    
    # Build consequence structure
    target_monomials = get_monomials_from_polynomial(target, variables)
    if not target_monomials:
        target_monomials = [target]  # Fallback
    
    consequence = {
        'monomials': target_monomials,
        'coeff_prefix': 'd'
    }
    
    # Fill template
    script_content = fill_keymaera_reasoning_template(
        problem_name=problem_name,
        target_index=target_index,
        axiom_combo=axiom_combo,
        variables=variables,
        known_axioms=known_axioms,
        abducted_axioms=abducted_axioms,
        consequence=consequence
    )
    
    # Save script
    script_path = os.path.join(output_dir, f"reasoning_target{target_index}_{axiom_combo}.kyx")
    with open(script_path, 'w') as f:
        f.write(script_content)
    
    logger.info(f"Generated KeyMaera script: {script_path}")
    
    return script_path
