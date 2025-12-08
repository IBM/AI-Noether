"""
AI-Noether: Reasoning functions

This module handles the reasoning step - testing if candidate axiom sets prove targets.
Includes logic for duplicate and superset elimination.
"""

import subprocess
import os
from itertools import combinations
from typing import List, Optional, Set, FrozenSet, Tuple
from pathlib import Path

from .config import Config
from .templates import fill_m2_reasoning_template
from .parsers import parse_m2_reasoning_output, ReasoningResult, DecompositionResult
from .logging_utils import get_logger, log_subprocess_result


def _frozenset_from_list(items: List[str]) -> FrozenSet[str]:
    """Convert a list of strings to a frozenset for set operations."""
    return frozenset(items)


def _list_from_frozenset(items: FrozenSet[str]) -> List[str]:
    """Convert a frozenset back to a sorted list."""
    return sorted(list(items))


def is_superset_of_any(candidate: FrozenSet[str], existing: Set[FrozenSet[str]]) -> bool:
    """
    Check if candidate is a superset of any set in existing.
    
    If set A can prove Q, then any superset of A can also prove Q (trivially).
    We don't want to save such supersets.
    """
    for ex in existing:
        if ex.issubset(candidate) and ex != candidate:
            return True
    return False


def filter_supersets(candidates: List[List[str]]) -> List[List[str]]:
    """
    Filter out candidates that are supersets of other candidates.
    
    Keep only minimal sets - if {A} proves Q, don't keep {A, B}.
    """
    # Convert to frozensets for efficient set operations
    candidate_sets = [_frozenset_from_list(c) for c in candidates]
    
    # Sort by size (ascending) so we process smaller sets first
    indexed = sorted(enumerate(candidate_sets), key=lambda x: len(x[1]))
    
    kept = set()
    kept_original = []
    
    for orig_idx, candidate in indexed:
        if not is_superset_of_any(candidate, kept):
            kept.add(candidate)
            kept_original.append(candidates[orig_idx])
    
    return kept_original


def remove_duplicates(candidates: List[List[str]]) -> List[List[str]]:
    """Remove duplicate candidate sets (order-independent)."""
    seen = set()
    unique = []
    
    for candidate in candidates:
        key = _frozenset_from_list(candidate)
        if key not in seen:
            seen.add(key)
            unique.append(sorted(candidate))
    
    return unique


def generate_candidate_sets(
    decomp_result: DecompositionResult,
    num_removed: int,
    num_targets: int,
    max_size: int = -1
) -> List[List[str]]:
    """
    Generate candidate axiom sets from decomposition components.
    
    For each component, generate subsets of generators up to max_size.
    Only consider subsets from within a single component (not cross-component).
    
    Args:
        decomp_result: Result from decomposition
        num_removed: Number of axioms that were removed
        num_targets: Number of targets
        max_size: Maximum subset size (-1 for default = num_removed + num_targets)
    
    Returns:
        List of candidate sets to test
    """
    if max_size < 0:
        max_size = num_removed + num_targets
    
    all_candidates = []
    
    # Always include empty set (baseline)
    all_candidates.append([])
    
    for component_gens in decomp_result.components:
        if not component_gens:
            continue
        
        # Limit to max_size
        limit = min(max_size, len(component_gens))
        
        # Generate all subsets of size 1 to limit
        for size in range(1, limit + 1):
            for subset in combinations(component_gens, size):
                all_candidates.append(list(subset))
    
    return all_candidates


def run_reasoning_m2(
    variables: List[str],
    remaining_axioms: List[str],
    targets: List[str],
    candidate_sets: List[List[str]],
    measured_per_target: List[List[str]],
    non_measured_per_target: List[List[str]],
    output_dir: str,
    config: Config
) -> Optional[ReasoningResult]:
    """
    Run reasoning using Macaulay2 to test candidate sets.
    
    Args:
        variables: List of variable names
        remaining_axioms: List of remaining axiom equations
        targets: List of target polynomials
        candidate_sets: List of candidate axiom sets to test
        measured_per_target: Per-target measured variables
        non_measured_per_target: Per-target non-measured variables
        output_dir: Directory to save outputs
        config: Configuration object
    
    Returns:
        ReasoningResult or None if failed
    """
    logger = get_logger()
    
    os.makedirs(output_dir, exist_ok=True)
    
    # Output files
    reasoning_output = os.path.join(output_dir, "reasoning_output.txt")
    script_path = os.path.join(output_dir, "reasoning_script.m2")
    
    # Fill template
    script_content = fill_m2_reasoning_template(
        variables=variables,
        remaining_axioms=remaining_axioms,
        targets=targets,
        candidate_sets=candidate_sets,
        measured_per_target=measured_per_target,
        non_measured_per_target=non_measured_per_target,
        require_literal_gb=config.reasoning.require_literal_gb,
        output_file=reasoning_output
    )
    
    # Write script
    with open(script_path, 'w') as f:
        f.write(script_content)
    
    logger.info(f"Running M2 reasoning, script: {script_path}")
    logger.debug(f"Testing {len(candidate_sets)} candidate sets")
    
    # Run Macaulay2
    try:
        result = subprocess.run(
            [config.paths.macaulay2, "--script", script_path],
            capture_output=True,
            text=True,
            timeout=config.execution.timeout_reasoning
        )
        
        log_subprocess_result(
            cmd=f"{config.paths.macaulay2} --script {script_path}",
            returncode=result.returncode,
            stdout=result.stdout,
            stderr=result.stderr,
            context="M2 Reasoning"
        )
        
        # Read output file
        if os.path.exists(reasoning_output):
            with open(reasoning_output, 'r') as f:
                output_content = f.read()
            
            raw_result = parse_m2_reasoning_output(output_content)
            
            # Post-process: remove duplicates and supersets
            saved_unique = remove_duplicates(raw_result.saved_combos)
            saved_minimal = filter_supersets(saved_unique)
            
            strong_unique = remove_duplicates(raw_result.strong_candidates)
            strong_minimal = filter_supersets(strong_unique)
            
            # Write filtered results
            filtered_path = os.path.join(output_dir, "reasoning_filtered.txt")
            with open(filtered_path, 'w') as f:
                f.write("=== Filtered Results (duplicates and supersets removed) ===\n\n")
                f.write("SAVED_COMBOS (minimal):\n")
                for combo in saved_minimal:
                    f.write(f"  {combo}\n")
                f.write(f"\nTotal saved (after filtering): {len(saved_minimal)}\n")
                f.write(f"Total saved (before filtering): {len(raw_result.saved_combos)}\n\n")
                
                f.write("STRONG_CANDIDATES (minimal):\n")
                for combo in strong_minimal:
                    f.write(f"  {combo}\n")
                f.write(f"\nTotal strong (after filtering): {len(strong_minimal)}\n")
                f.write(f"Total strong (before filtering): {len(raw_result.strong_candidates)}\n")
            
            return ReasoningResult(
                saved_combos=saved_minimal,
                strong_candidates=strong_minimal,
                raw_output=output_content
            )
        else:
            logger.error(f"Reasoning output file not found: {reasoning_output}")
            return None
            
    except subprocess.TimeoutExpired:
        logger.error(f"M2 reasoning timed out after {config.execution.timeout_reasoning}s")
        return None
    except Exception as e:
        logger.error(f"M2 reasoning failed: {e}")
        return None


def run_reasoning(
    variables: List[str],
    remaining_axioms: List[str],
    targets: List[str],
    decomp_result: DecompositionResult,
    measured_per_target: List[List[str]],
    non_measured_per_target: List[List[str]],
    num_removed: int,
    output_dir: str,
    config: Config
) -> Optional[ReasoningResult]:
    """
    Complete reasoning pipeline:
    1. Generate candidate sets from decomposition
    2. Run M2 to test each candidate
    3. Filter duplicates and supersets
    
    Args:
        variables: List of variable names
        remaining_axioms: List of remaining axiom equations
        targets: List of target polynomials
        decomp_result: Result from decomposition
        measured_per_target: Per-target measured variables
        non_measured_per_target: Per-target non-measured variables
        num_removed: Number of axioms that were removed
        output_dir: Directory to save outputs
        config: Configuration object
    
    Returns:
        ReasoningResult or None if failed
    """
    logger = get_logger()
    
    # Create output directory
    os.makedirs(output_dir, exist_ok=True)
    
    # Generate candidate sets
    candidate_sets = generate_candidate_sets(
        decomp_result=decomp_result,
        num_removed=num_removed,
        num_targets=len(targets),
        max_size=config.reasoning.max_candidate_size
    )
    
    logger.info(f"Generated {len(candidate_sets)} candidate sets from {decomp_result.num_components} components")
    
    # Save candidate sets for reference
    candidates_path = os.path.join(output_dir, "candidate_sets.txt")
    with open(candidates_path, 'w') as f:
        f.write(f"Number of components: {decomp_result.num_components}\n")
        f.write(f"Number of candidate sets: {len(candidate_sets)}\n\n")
        for i, cs in enumerate(candidate_sets):
            f.write(f"Candidate {i}: {cs}\n")
    
    # Run reasoning
    return run_reasoning_m2(
        variables=variables,
        remaining_axioms=remaining_axioms,
        targets=targets,
        candidate_sets=candidate_sets,
        measured_per_target=measured_per_target,
        non_measured_per_target=non_measured_per_target,
        output_dir=output_dir,
        config=config
    )
