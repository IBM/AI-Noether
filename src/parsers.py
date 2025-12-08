"""
AI-Noether: Parsers for Macaulay2 and Singular output

This module provides functions to parse the output from M2 and Singular scripts.
"""

import re
from typing import List, Dict, Any, Optional, Tuple
from dataclasses import dataclass
import numpy as np


@dataclass
class DecompositionResult:
    """Result of primary decomposition."""
    components: List[List[str]]  # List of components, each is list of generators
    num_components: int
    raw_output: str


@dataclass
class ReasoningResult:
    """Result of reasoning step."""
    saved_combos: List[List[str]]
    strong_candidates: List[List[str]]
    raw_output: str


@dataclass 
class DimensionalityResult:
    """Result of dimensionality check."""
    original_dim: int
    reduced_dim: int
    discovered_dim: int
    dimensions_equal: bool
    removed_axioms: List[str]
    remaining_axioms: List[str]
    targets: List[str]
    raw_output: str


@dataclass
class WitnessSetComponent:
    """A single component from numerical irreducible decomposition."""
    index: int
    equations: List[str]
    points: List[List[complex]]


@dataclass
class WitnessSetResult:
    """Result of witness set computation."""
    variable_order: List[str]
    components: List[WitnessSetComponent]
    raw_output: str


# =============================================================================
# M2 Output Parsers
# =============================================================================

def parse_m2_decomposition_output(output: str) -> DecompositionResult:
    """
    Parse M2 decomposition output.
    
    Expected format:
    COMPONENT_1:
      num_generators: N
      GEN: polynomial1
      GEN: polynomial2
      ...
    COMPONENT_2:
      ...
    """
    components = []
    current_gens = []
    
    lines = output.strip().split('\n')
    
    for line in lines:
        line = line.strip()
        
        if line.startswith('COMPONENT_'):
            # Save previous component if any
            if current_gens:
                components.append(current_gens)
            current_gens = []
        elif line.startswith('GEN:'):
            gen = line[4:].strip()
            if gen:
                current_gens.append(gen)
    
    # Don't forget the last component
    if current_gens:
        components.append(current_gens)
    
    return DecompositionResult(
        components=components,
        num_components=len(components),
        raw_output=output
    )


def parse_m2_reasoning_output(output: str) -> ReasoningResult:
    """
    Parse M2 reasoning output.
    
    Expected format:
    SAVED_COMBOS:
      {poly1, poly2}
      {poly3}
    STRONG_CANDIDATES:
      {poly1, poly2}
    """
    saved_combos = []
    strong_candidates = []
    
    lines = output.strip().split('\n')
    current_section = None
    
    for line in lines:
        line = line.strip()
        
        if line == "SAVED_COMBOS:":
            current_section = "saved"
        elif line == "STRONG_CANDIDATES:":
            current_section = "strong"
        elif line.startswith('{') and current_section:
            # Parse M2 list
            content = line.strip('{}')
            if content:
                items = [s.strip() for s in content.split(',') if s.strip()]
            else:
                items = []
            
            if current_section == "saved":
                saved_combos.append(items)
            elif current_section == "strong":
                strong_candidates.append(items)
    
    return ReasoningResult(
        saved_combos=saved_combos,
        strong_candidates=strong_candidates,
        raw_output=output
    )


def parse_m2_dimensionality_output(output: str) -> Optional[DimensionalityResult]:
    """
    Parse M2 dimensionality check output.
    
    Expected format:
    Original dimension: N
    Reduced dimension: M
    Discovered dimension: K
    ...
    """
    original_dim = reduced_dim = discovered_dim = None
    removed_axioms = []
    remaining_axioms = []
    targets = []
    
    for line in output.strip().split('\n'):
        line = line.strip()
        
        if line.startswith("Original dimension:"):
            try:
                original_dim = int(line.split(':', 1)[1].strip())
            except ValueError:
                pass
        elif line.startswith("Reduced dimension:"):
            try:
                reduced_dim = int(line.split(':', 1)[1].strip())
            except ValueError:
                pass
        elif line.startswith("Discovered dimension:"):
            try:
                discovered_dim = int(line.split(':', 1)[1].strip())
            except ValueError:
                pass
        elif line.startswith("Removed axioms:"):
            content = line.split(':', 1)[1].strip()
            if content.startswith('{'):
                content = content.strip('{}')
                removed_axioms = [a.strip().strip('"') for a in content.split(',') if a.strip()]
        elif line.startswith("Remaining axioms:"):
            content = line.split(':', 1)[1].strip()
            if content.startswith('{'):
                content = content.strip('{}')
                remaining_axioms = [a.strip().strip('"') for a in content.split(',') if a.strip()]
        elif line.startswith("Targets:"):
            content = line.split(':', 1)[1].strip()
            if content.startswith('{'):
                content = content.strip('{}')
                targets = [t.strip().strip('"') for t in content.split(',') if t.strip()]
    
    if original_dim is None or discovered_dim is None:
        return None
    
    return DimensionalityResult(
        original_dim=original_dim,
        reduced_dim=reduced_dim or 0,
        discovered_dim=discovered_dim,
        dimensions_equal=(original_dim == discovered_dim),
        removed_axioms=removed_axioms,
        remaining_axioms=remaining_axioms,
        targets=targets,
        raw_output=output
    )


def _parse_m2_complex_token(tok: str) -> complex:
    """Parse a single Macaulay2 complex token like '.123-4.5*ii' into Python complex."""
    s = tok.strip()
    # M2 uses 'ii' for sqrt(-1)
    s = s.replace('*ii', 'j').replace('ii', 'j')
    # Fix leading decimals: .123 -> 0.123, -.45 -> -0.45
    s = s.replace('-.', '-0.').replace('+.', '+0.')
    if s.startswith('.'):
        s = '0' + s
    try:
        return complex(s)
    except Exception:
        return complex(s.replace(' ', ''))


def parse_m2_witness_set_output(output: str) -> WitnessSetResult:
    """
    Parse M2 witness set output.
    
    Expected format:
    variable ordering: x, y, z
    
    component_1:
    equations:
    poly1
    poly2
    points:
    val1, val2, val3
    val4, val5, val6
    ...
    """
    var_order = []
    components = []
    
    lines = output.strip().split('\n')
    i = 0
    
    # Parse header - variable ordering
    while i < len(lines) and not lines[i].startswith('variable ordering:'):
        i += 1
    if i < len(lines):
        hdr = lines[i].split(':', 1)[1].strip()
        var_order = [v.strip() for v in hdr.split(',') if v.strip()]
        i += 1
    
    # Parse components
    current_comp = None
    current_equations = []
    current_points = []
    in_equations = False
    in_points = False
    
    while i < len(lines):
        line = lines[i].rstrip()
        
        if line.startswith('component_'):
            # Save previous component
            if current_comp is not None:
                components.append(WitnessSetComponent(
                    index=current_comp,
                    equations=current_equations,
                    points=current_points
                ))
            
            # Start new component
            match = re.search(r'component_(\d+)', line)
            current_comp = int(match.group(1)) if match else len(components) + 1
            current_equations = []
            current_points = []
            in_equations = False
            in_points = False
        
        elif line.strip() == 'equations:':
            in_equations = True
            in_points = False
        
        elif line.strip() == 'points:':
            in_equations = False
            in_points = True
        
        elif in_equations and line.strip() and not line.startswith('component_'):
            current_equations.append(line.strip())
        
        elif in_points and line.strip() and not line.startswith('component_'):
            if not line.startswith('--'):
                toks = [t.strip() for t in line.split(',')]
                try:
                    coords = [_parse_m2_complex_token(t) for t in toks if t]
                    if coords:
                        current_points.append(coords)
                except Exception:
                    pass  # Skip malformed lines
        
        i += 1
    
    # Don't forget last component
    if current_comp is not None:
        components.append(WitnessSetComponent(
            index=current_comp,
            equations=current_equations,
            points=current_points
        ))
    
    return WitnessSetResult(
        variable_order=var_order,
        components=components,
        raw_output=output
    )


# =============================================================================
# Singular Output Parsers
# =============================================================================

def parse_singular_decomposition_output(output: str) -> DecompositionResult:
    """
    Parse Singular minAss output.
    
    Expected format (may have preamble with library loading messages):
    [1]:
       _[1]=L
       _[2]=d
       _[3]=v
       ...
    [2]:
       _[1]=delpb
       _[2]=delpa
       ...
    """
    components = []
    current_gens = []
    
    lines = output.strip().split('\n')
    in_component = False
    
    for line in lines:
        line = line.rstrip()
        
        # Check for component start: [N]:
        comp_match = re.match(r'^\[(\d+)\]:$', line.strip())
        if comp_match:
            # Save previous component if any
            if current_gens:
                components.append(current_gens)
            current_gens = []
            in_component = True
            continue
        
        # Check for generator: _[N]=polynomial
        gen_match = re.match(r'^\s*_\[(\d+)\]=(.+)$', line)
        if gen_match and in_component:
            polynomial = gen_match.group(2).strip()
            if polynomial:
                current_gens.append(polynomial)
    
    # Don't forget last component
    if current_gens:
        components.append(current_gens)
    
    return DecompositionResult(
        components=components,
        num_components=len(components),
        raw_output=output
    )


# =============================================================================
# Problem File Parser
# =============================================================================

def read_problem(file_path: str) -> Dict[str, Any]:
    """
    Read a physics problem from a structured TXT file.
    
    Returns dict with:
      - variables: List[str]
      - equations: List[str]
      - measured_vars: List[str]
      - non_measured_vars: List[str]
      - targets: List[str]
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
        data['variables'] = [v.strip().strip('"').strip("'") 
                            for v in vars_str.split(',') if v.strip()]
    
    # Equations: everything between "Equations:" and "Measured"
    eqs_match = re.search(r'Equations?:\s*(.*?)(?=\n\s*\n\s*Measured)', 
                          content, re.DOTALL | re.IGNORECASE)
    if eqs_match:
        eqs_str = eqs_match.group(1).strip()
        data['equations'] = [eq.strip() for eq in eqs_str.split('\n') if eq.strip()]
    
    # Measured variables
    measured_match = re.search(r'Measured Variables:\s*\[(.*?)\]', 
                               content, re.DOTALL | re.IGNORECASE)
    if measured_match:
        measured_str = measured_match.group(1)
        data['measured_vars'] = [v.strip().strip('"').strip("'") 
                                for v in measured_str.split(',') if v.strip()]
        data['non_measured_vars'] = [v for v in data['variables'] 
                                     if v not in data['measured_vars']]
    
    # Target polynomials (can be multi-line)
    targ_block = re.search(r'Target Polynomial:?(\s*\n+([\s\S]*))$', 
                           content, re.IGNORECASE)
    if targ_block:
        block = targ_block.group(1).strip()
        lines = [ln.strip() for ln in block.split('\n') if ln.strip()]
        data['targets'] = lines
    
    return data


def vars_in_poly(poly: str, variables: List[str]) -> List[str]:
    """Find which variables from the list appear in a polynomial string."""
    found = set()
    # Check longer names first to avoid partial matches
    for v in sorted(variables, key=len, reverse=True):
        if re.search(rf'(?<![A-Za-z0-9_]){re.escape(v)}(?![A-Za-z0-9_])', poly):
            found.add(v)
    return list(found)
