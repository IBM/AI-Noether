"""
AI-Noether: Template filling utilities

This module handles loading and filling templates for M2, Singular, and KeyMaera scripts.
Uses simple {placeholder} format for substitution.
"""

import os
import re
from typing import List, Dict, Any, Optional, Tuple
from pathlib import Path


# Get template directory (relative to this file)
TEMPLATE_DIR = Path(__file__).parent.parent / "templates"


def get_template_path(engine: str, template_name: str) -> Path:
    """
    Get the full path to a template file.
    
    Args:
        engine: "m2", "singular", or "keymaera"
        template_name: Name of template file (without extension for m2/singular)
    
    Returns:
        Path to template file
    """
    ext_map = {
        "m2": ".m2",
        "singular": ".sing",
        "keymaera": ".kyx"
    }
    ext = ext_map.get(engine, "")
    
    # Add extension if not present
    if not template_name.endswith(ext):
        template_name = template_name + ext
    
    return TEMPLATE_DIR / engine / template_name


def load_template(engine: str, template_name: str) -> str:
    """
    Load a template file.
    
    Args:
        engine: "m2", "singular", or "keymaera"
        template_name: Name of template file
    
    Returns:
        Template content as string
    """
    path = get_template_path(engine, template_name)
    with open(path, 'r') as f:
        return f.read()


def m2_list(items: List[str]) -> str:
    """Format a Python list as M2 comma-separated list."""
    return ', '.join(items) if items else ''


def m2_list_of_lists(items: List[List[str]]) -> str:
    """Format a list of lists for M2 (e.g., {{a,b},{c,d}})."""
    if not items:
        return '{}'
    inner = ['{' + m2_list(sub) + '}' for sub in items]
    return '{' + ', '.join(inner) + '}'


def singular_list(items: List[str]) -> str:
    """Format a Python list as Singular comma-separated list."""
    return ', '.join(items) if items else ''


# =============================================================================
# M2 Template Fillers
# =============================================================================

def fill_m2_projection_template(
    variables: List[str],
    axioms: List[str],
    measured_variables: List[str],
    non_measured_variables: List[str],
    output_file: str,
    targets: Optional[List[str]] = None
) -> str:
    """Fill the M2 projection template."""
    template = load_template("m2", "projection")
    
    # Generate targets check code
    if targets:
        targets_check_code = f"""
qList = toList([{m2_list(targets)}]);
elimIdeal = ideal(flatten entries GBproj);
f << "Target checks in eliminated ideal (membership & literal appearance):" << endl;
scan(qList, q -> (
    rem = q % elimIdeal;
    remZero = (rem == 0);
    appears = member(true, toList apply(flatten entries GBproj, g -> g == q));
    f << "q = " << toString q << endl;
    f << "  remainderZero: " << toString remZero << endl;
    f << "  appearsLiterallyInGB: " << toString appears << endl;
));
"""
    else:
        targets_check_code = "-- No targets specified"
    
    result = template.replace("{variables}", m2_list(variables))
    result = result.replace("{axioms}", m2_list(axioms))
    result = result.replace("{measured_variables}", m2_list(measured_variables))
    result = result.replace("{non_measured_variables}", m2_list(non_measured_variables))
    result = result.replace("{output_file}", output_file)
    result = result.replace("{targets_check_code}", targets_check_code)
    
    return result


def fill_m2_decomposition_template(
    variables: List[str],
    remaining_axioms: List[str],
    targets: List[str],
    output_file: str
) -> str:
    """Fill the M2 primary decomposition template."""
    template = load_template("m2", "decomposition")
    
    result = template.replace("{variables}", m2_list(variables))
    result = result.replace("{remaining_axioms}", m2_list(remaining_axioms))
    result = result.replace("{targets}", m2_list(targets))
    result = result.replace("{output_file}", output_file)
    
    return result


def fill_m2_reasoning_template(
    variables: List[str],
    remaining_axioms: List[str],
    targets: List[str],
    candidate_sets: List[List[str]],
    measured_per_target: List[List[str]],
    non_measured_per_target: List[List[str]],
    require_literal_gb: bool,
    output_file: str
) -> str:
    """Fill the M2 reasoning template."""
    template = load_template("m2", "reasoning")
    
    result = template.replace("{variables}", m2_list(variables))
    result = result.replace("{remaining_axioms}", m2_list(remaining_axioms))
    result = result.replace("{targets}", m2_list(targets))
    
    # Format candidate sets as M2 list of lists
    candidate_sets_m2 = m2_list_of_lists(candidate_sets)
    result = result.replace("{candidate_sets}", candidate_sets_m2)
    
    result = result.replace("{measured_per_target}", m2_list_of_lists(measured_per_target))
    result = result.replace("{non_measured_per_target}", m2_list_of_lists(non_measured_per_target))
    result = result.replace("{require_literal_gb}", "true" if require_literal_gb else "false")
    result = result.replace("{output_file}", output_file)
    
    return result


def fill_m2_dimensionality_template(
    variables: List[str],
    all_axioms: List[str],
    removed_axioms: List[str],
    targets: List[str],
    output_file: str
) -> str:
    """Fill the M2 dimensionality check template."""
    template = load_template("m2", "dimensionality")
    
    result = template.replace("{variables}", m2_list(variables))
    result = result.replace("{all_axioms}", m2_list(all_axioms))
    result = result.replace("{targets}", m2_list(targets))
    result = result.replace("{output_file}", output_file)
    
    # Generate remove axiom code
    remove_code = '\n'.join([f'remainingAxioms = delete({ax}, remainingAxioms);' 
                            for ax in removed_axioms])
    result = result.replace("{remove_axioms_code}", remove_code)
    
    # Format removed axioms list for output
    removed_list = m2_list(removed_axioms)
    result = result.replace("{removed_axioms_list}", removed_list)
    
    return result


def fill_m2_witness_set_template(
    variables: List[str],
    remaining_axioms: List[str],
    targets: List[str],
    samples_per_component: int,
    engine: str,
    bertini_path: str,
    output_file: str
) -> str:
    """Fill the M2 witness set (NAG) template."""
    template = load_template("m2", "witness_set")
    
    # Handle Bertini vs NAG
    use_bertini = (engine.lower() == "bertini")
    
    if use_bertini:
        bertini_load = f'needsPackage("Bertini", Reload => true, Configuration => {{"BERTINIexecutable" => "{bertini_path}"}})'
        nid_call = "W = bertiniPosDimSolve axiomIdeal;"
    else:
        bertini_load = "-- Using built-in NAG"
        nid_call = "W = numericalIrreducibleDecomposition axiomIdeal;"
    
    result = template.replace("{variables}", m2_list(variables))
    result = result.replace("{remaining_axioms}", m2_list(remaining_axioms))
    result = result.replace("{targets}", m2_list(targets))
    result = result.replace("{samples_per_component}", str(samples_per_component))
    result = result.replace("{bertini_package_load}", bertini_load)
    result = result.replace("{nid_call}", nid_call)
    result = result.replace("{output_file}", output_file)
    
    return result


# =============================================================================
# Singular Template Fillers
# =============================================================================

def fill_singular_decomposition_template(
    variables: List[str],
    remaining_axioms: List[str],
    targets: List[str],
    output_file: str
) -> str:
    """Fill the Singular decomposition template."""
    template = load_template("singular", "decomposition")
    
    result = template.replace("{variables}", singular_list(variables))
    
    # Generate axiom definitions
    axiom_defs = []
    axiom_names = []
    for i, ax in enumerate(remaining_axioms, 1):
        name = f"ax{i}"
        axiom_defs.append(f"poly {name} = {ax};")
        axiom_names.append(name)
    result = result.replace("{axiom_definitions}", '\n'.join(axiom_defs))
    
    if axiom_names:
        result = result.replace("{remaining_axioms_ideal}", singular_list(axiom_names))
    else:
        result = result.replace("{remaining_axioms_ideal}", "0")
    
    # Generate target definitions
    target_defs = []
    target_names = []
    for i, t in enumerate(targets, 1):
        name = f"targ{i}"
        target_defs.append(f"poly {name} = {t};")
        target_names.append(name)
    result = result.replace("{target_definitions}", '\n'.join(target_defs))
    
    if target_names:
        result = result.replace("{targets_ideal}", singular_list(target_names))
    else:
        result = result.replace("{targets_ideal}", "0")
    
    result = result.replace("{output_file}", output_file)
    
    return result


# =============================================================================
# KeyMaera Content Generation (Direct, No Template)
# =============================================================================

def generate_keymaera_content(
    problem_name: str,
    target_index: int,
    combo_str: str,
    abducted_axioms_info: List[Tuple[int, int, List[str]]],  # List of (axiom_index, component_index, monomials)
    variables: List[str],
    known_axioms: List[str],
    consequence_monomials: List[str]
) -> Tuple[str, str]:
    """
    Generate KeyMaera file content with proper formatting.
    
    This function generates content directly without using a template file,
    ensuring proper formatting with:
    - Physics variables in ProgramVariables (no coefficients)
    - Coefficients in existential quantifiers
    - One abducted axiom equation per removed axiom
    - Proper LHS = RHS format for equations
    
    Args:
        problem_name: Name of the physics problem
        target_index: Index of the target consequence (1-based)
        combo_str: String identifying the axiom combination removed (e.g., "1_3")
        abducted_axioms_info: List of tuples (axiom_index, component_index, monomials) 
                              for each abducted axiom. Each removed axiom should have
                              exactly one entry.
        variables: List of physics variable names
        known_axioms: List of known axiom equations (as strings)
        consequence_monomials: List of monomial strings for the consequence/target
    
    Returns:
        Tuple of (content, filename_suffix)
        - content: Complete KeyMaera file content as string
        - filename_suffix: Suffix for filename like "ax1c1_ax3c2"
    """
    # Build filename suffix from all axiom/component pairs
    axiom_comp_parts = []
    for ax_idx, comp_idx, _ in abducted_axioms_info:
        axiom_comp_parts.append(f"ax{ax_idx}c{comp_idx}")
    axiom_comp_suffix = "_".join(axiom_comp_parts)
    
    lines = []
    lines.append(f'ArchiveEntry "{problem_name}_target{target_index}_combo{combo_str}_{axiom_comp_suffix}"')
    lines.append('')
    lines.append('ProgramVariables')
    
    # Physics variable declarations ONLY (no coefficients here)
    for v in variables:
        lines.append(f'  Real {v};')
    
    lines.append('End.')
    lines.append('')
    lines.append('Problem')
    lines.append('  (')
    
    # Collect all coefficient names, avoiding conflicts with physics variables
    all_coeffs = []
    coeff_idx = 1
    
    def get_safe_coeff(idx: int) -> str:
        name = f"c{idx}"
        while name in variables:
            name = f"c_{idx}"
            idx += 100
        return name
    
    # Track coefficient ranges for each abducted axiom
    abducted_coeff_ranges = []  # List of (start_idx, end_idx) for each abducted axiom
    
    for ax_idx, comp_idx, monomials in abducted_axioms_info:
        start_idx = len(all_coeffs)
        for _ in monomials:
            all_coeffs.append(get_safe_coeff(coeff_idx))
            coeff_idx += 1
        end_idx = len(all_coeffs)
        abducted_coeff_ranges.append((start_idx, end_idx))
    
    # Coefficients for consequence
    conseq_start_idx = len(all_coeffs)
    for _ in consequence_monomials:
        all_coeffs.append(get_safe_coeff(coeff_idx))
        coeff_idx += 1
    
    # Existential quantifiers - one per line
    for c in all_coeffs:
        lines.append(f'    \\exists {c}')
    
    lines.append('    (')
    
    # Coefficient positivity
    coeff_pos = ' & '.join([f'{c}>0' for c in all_coeffs])
    lines.append(f'      {coeff_pos}')
    lines.append('      &')
    lines.append('      (')
    
    # Forall quantifiers - one per line
    for v in variables:
        lines.append(f'      \\forall {v}')
    
    lines.append('          (')
    lines.append('          (')
    
    # Variable positivity
    var_pos = ' & '.join([f'{v}>0' for v in variables])
    lines.append(f'            {var_pos}')
    
    # Known axiom equations
    for ax in known_axioms:
        if '=' in ax:
            lines.append(f'            & ( {ax} )')
        else:
            lines.append(f'            & ( {ax} = 0 )')
    
    # Abducted axiom equations - one for each abducted axiom
    for i, (ax_idx, comp_idx, monomials) in enumerate(abducted_axioms_info):
        start_idx, end_idx = abducted_coeff_ranges[i]
        axiom_coeffs = all_coeffs[start_idx:end_idx]
        
        if len(monomials) > 0:
            lhs_coeff = axiom_coeffs[0]
            lhs_mono = monomials[0]
            lhs = f'( {lhs_coeff} * {lhs_mono} )'
            
            if len(monomials) == 1:
                lines.append(f'            & {lhs} = 0')
            else:
                rhs_terms = []
                for j, mono in enumerate(monomials[1:], 1):
                    rhs_coeff = axiom_coeffs[j]
                    rhs_terms.append(f'( {rhs_coeff} * {mono} )')
                rhs = ' + '.join(rhs_terms)
                lines.append(f'            & {lhs} = {rhs}')
    
    lines.append('            )')
    lines.append('        ->')
    lines.append('          (')
    
    # Consequence equation
    if len(consequence_monomials) == 0:
        lines.append('            0 = 0')
    elif len(consequence_monomials) == 1:
        c = all_coeffs[conseq_start_idx]
        lines.append(f'            ( {c} * {consequence_monomials[0]} ) = 0')
    else:
        lhs_coeff = all_coeffs[conseq_start_idx]
        lhs = f'( {lhs_coeff} * {consequence_monomials[0]} )'
        
        rhs_terms = []
        for i, mono in enumerate(consequence_monomials[1:], 1):
            rhs_coeff = all_coeffs[conseq_start_idx + i]
            rhs_terms.append(f'( {rhs_coeff} * {mono} )')
        rhs = ' + '.join(rhs_terms)
        lines.append(f'            {lhs} = {rhs}')
    
    lines.append('          )')
    lines.append('          )')
    lines.append('      )')
    lines.append('    )')
    lines.append('  )')
    lines.append('End.')
    lines.append('')
    lines.append('End.')
    
    return '\n'.join(lines), axiom_comp_suffix


# =============================================================================
# KeyMaera Template Fillers (Deprecated - kept for backwards compatibility)
# =============================================================================

def fill_keymaera_reasoning_template(
    problem_name: str,
    target_index: int,
    axiom_combo: str,
    variables: List[str],
    known_axioms: List[str],
    abducted_axioms: List[Dict[str, Any]],
    consequence: Dict[str, Any]
) -> str:
    """
    Fill the KeyMaera reasoning template.
    
    DEPRECATED: Use generate_keymaera_content() instead for proper formatting.
    This function is kept for backwards compatibility only.
    
    Args:
        problem_name: Name of the physics problem
        target_index: Index of the target consequence
        axiom_combo: String identifying the axiom combination
        variables: List of variable names
        known_axioms: List of known axiom equations (as strings)
        abducted_axioms: List of dicts with:
            - 'monomials': List of monomial strings
            - 'coeff_prefix': Prefix for coefficient names (e.g., 'c')
        consequence: Dict with:
            - 'monomials': List of monomial strings
            - 'coeff_prefix': Prefix for coefficient names (e.g., 'd')
    
    Returns:
        Filled KeyMaera template
    """
    template = load_template("keymaera", "reasoning")
    
    # Basic substitutions
    result = template.replace("{problem_name}", problem_name)
    result = result.replace("{target_index}", str(target_index))
    result = result.replace("{axiom_combo}", axiom_combo)
    
    # Variable declarations
    var_decls = '\n'.join([f"  Real {v};" for v in variables])
    result = result.replace("{variable_declarations}", var_decls)
    
    # Collect all coefficient names
    all_coeffs = []
    coeff_idx = 1
    
    # Coefficients for abducted axioms
    for ax in abducted_axioms:
        for _ in ax['monomials']:
            all_coeffs.append(f"{ax['coeff_prefix']}{coeff_idx}")
            coeff_idx += 1
    
    # Coefficients for consequence
    conseq_coeffs = []
    for i, _ in enumerate(consequence['monomials'], 1):
        conseq_coeffs.append(f"{consequence['coeff_prefix']}{i}")
    all_coeffs.extend(conseq_coeffs)
    
    # Coefficient declarations
    coeff_decls = '\n'.join([f"  Real {c};" for c in all_coeffs])
    result = result.replace("{exist_coeff_declarations}", coeff_decls)
    
    # Existential quantifiers for coefficients
    exist_coeffs = ' '.join([f"\\exists {c}" for c in all_coeffs])
    result = result.replace("{exist_coefficients}", exist_coeffs)
    
    # Coefficient positivity constraints (all > 0)
    coeff_pos = ' & '.join([f"{c} > 0" for c in all_coeffs])
    result = result.replace("{coefficient_positivity}", coeff_pos)
    
    # Forall quantifiers for variables
    forall_vars = ' '.join([f"\\forall {v}" for v in variables])
    result = result.replace("{forall_variables}", forall_vars)
    
    # Variable positivity (optional, can be empty)
    var_pos = ' & '.join([f"{v} > 0" for v in variables])
    result = result.replace("{variable_positivity}", f"({var_pos}) &" if var_pos else "")
    
    # Known axiom equations
    known_eqs = '\n            '.join([f"& ( {ax} = 0 )" for ax in known_axioms])
    result = result.replace("{known_axiom_equations}", known_eqs if known_eqs else "")
    
    # Abducted axiom equations with coefficient * monomial format
    abducted_eqs_lines = []
    coeff_idx = 1
    for ax in abducted_axioms:
        terms = []
        for mono in ax['monomials']:
            coeff_name = f"{ax['coeff_prefix']}{coeff_idx}"
            terms.append(f"( {coeff_name} * {mono} )")
            coeff_idx += 1
        eq = ' + '.join(terms) + " = 0"
        abducted_eqs_lines.append(f"& ( {eq} )")
    
    abducted_eqs = '\n            '.join(abducted_eqs_lines)
    result = result.replace("{abducted_axiom_equations}", abducted_eqs if abducted_eqs else "")
    
    # Consequence equation
    conseq_terms = []
    for i, mono in enumerate(consequence['monomials'], 1):
        coeff_name = f"{consequence['coeff_prefix']}{i}"
        conseq_terms.append(f"( {coeff_name} * {mono} )")
    conseq_eq = ' + '.join(conseq_terms) + " = 0"
    result = result.replace("{consequence_equation}", conseq_eq)
    
    return result
