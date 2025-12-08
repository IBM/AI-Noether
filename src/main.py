"""
AI-Noether: Main entry point

This module orchestrates the entire abductive inference pipeline.
"""

import os
import sys
import argparse
from pathlib import Path
from itertools import combinations
from concurrent.futures import ProcessPoolExecutor, TimeoutError as FuturesTimeoutError
from typing import List, Optional, Dict, Any

from .config import Config, load_config, parse_num_axiom_spec, validate_config
from .logging_utils import setup_logger, get_logger
from .parsers import read_problem, vars_in_poly
from .projection import run_projection
from .dimensionality import run_dimensionality_check
from .decomposition import run_decomposition
from .reasoning import run_reasoning
from .numerical import (
    run_witness_set_computation,
    perform_symbolic_regression,
    generate_keymaera_script
)


def process_projection(
    problem_data: Dict[str, Any],
    output_dir: str,
    config: Config
) -> None:
    """Run projection analysis for each target."""
    logger = get_logger()
    logger.info("Running projection analysis")
    
    variables = problem_data['variables']
    axioms = problem_data['equations']
    targets = problem_data['targets']
    measured_vars = problem_data['measured_vars']
    
    projection_dir = os.path.join(output_dir, "projection")
    os.makedirs(projection_dir, exist_ok=True)
    
    for i, target in enumerate(targets, start=1):
        target_vars = vars_in_poly(target, variables)
        measured_subset = [v for v in measured_vars if v in target_vars]
        non_measured_subset = [v for v in variables if v not in measured_subset]
        
        target_dir = os.path.join(projection_dir, f"target_{i}")
        
        result = run_projection(
            variables=variables,
            axioms=axioms,
            measured_variables=measured_subset,
            non_measured_variables=non_measured_subset,
            output_dir=target_dir,
            config=config,
            targets=[target]
        )
        
        if result:
            logger.info(f"Projection for target {i} complete: {result}")
        else:
            logger.warning(f"Projection for target {i} failed")


def process_dimensionality(
    problem_data: Dict[str, Any],
    n_allows: set,
    output_dir: str,
    config: Config
) -> Dict[str, Any]:
    """Run dimensionality checks for all axiom combinations."""
    logger = get_logger()
    logger.info("Running dimensionality checks")
    
    variables = problem_data['variables']
    axioms = problem_data['equations']
    targets = problem_data['targets']
    
    dim_dir = os.path.join(output_dir, "dimensionality_check")
    os.makedirs(dim_dir, exist_ok=True)
    
    all_results = {}
    
    for n in sorted(n_allows):
        if n < 1:
            continue
            
        n_dir = os.path.join(dim_dir, f"{n}_axioms_removed")
        os.makedirs(n_dir, exist_ok=True)
        
        n_results = {
            'total_subsets': 0,
            'dimension_counts': {},
            'equal_dimension': 0,
            'equal_dimension_files': []
        }
        
        all_combos = list(combinations(axioms, n))
        
        for count, subset in enumerate(all_combos, 1):
            removed = list(subset)
            combo_dir = os.path.join(n_dir, f"subset_{count}")
            
            logger.debug(f"Dimensionality check {count}/{len(all_combos)} for n={n}")
            
            result = run_dimensionality_check(
                variables=variables,
                all_axioms=axioms,
                removed_axioms=removed,
                targets=targets,
                output_dir=combo_dir,
                config=config
            )
            
            if result:
                n_results['total_subsets'] += 1
                dim = result.discovered_dim
                n_results['dimension_counts'][dim] = n_results['dimension_counts'].get(dim, 0) + 1
                
                if result.dimensions_equal:
                    n_results['equal_dimension'] += 1
                    n_results['equal_dimension_files'].append(combo_dir)
        
        # Save per-n summary
        summary_path = os.path.join(n_dir, "aggregate_results.txt")
        with open(summary_path, 'w') as f:
            f.write(f"=== Results for removing {n} axioms ===\n")
            f.write(f"Total subsets tested: {n_results['total_subsets']}\n")
            f.write("Dimension distribution:\n")
            for dim, count in sorted(n_results['dimension_counts'].items()):
                f.write(f"  Dimension {dim}: {count} cases\n")
            f.write(f"Cases with equal dimension: {n_results['equal_dimension']}\n")
            
            if n_results['equal_dimension_files']:
                f.write("\nDirectories with equal dimensions:\n")
                for dirname in n_results['equal_dimension_files']:
                    f.write(f"  {dirname}\n")
        
        all_results[n] = n_results
    
    # Save cross-n summary
    if all_results:
        total_subsets = sum(r['total_subsets'] for r in all_results.values())
        total_equal = sum(r['equal_dimension'] for r in all_results.values())
        
        summary_path = os.path.join(dim_dir, "cross_n_aggregate.txt")
        with open(summary_path, 'w') as f:
            f.write("=== Aggregate Results Across All Subset Sizes ===\n\n")
            f.write(f"Total subsets tested: {total_subsets}\n")
            f.write(f"Total cases with equal dimensions: {total_equal}\n")
            if total_subsets > 0:
                f.write(f"Percentage: {total_equal/total_subsets:.1%}\n")
    
    return all_results


def process_algebraic_abduction(
    problem_data: Dict[str, Any],
    n_allows: set,
    output_dir: str,
    config: Config
) -> None:
    """Run noiseless algebraic abduction (decomposition + reasoning)."""
    logger = get_logger()
    logger.info("Running algebraic abduction (noiseless)")
    
    variables = problem_data['variables']
    axioms = problem_data['equations']
    targets = problem_data['targets']
    measured_vars = problem_data['measured_vars']
    
    # Compute per-target variable partitions
    measured_per_target = []
    non_measured_per_target = []
    
    for target in targets:
        target_vars = vars_in_poly(target, variables)
        measured_subset = [v for v in measured_vars if v in target_vars]
        non_measured_subset = [v for v in variables if v not in measured_subset]
        measured_per_target.append(measured_subset)
        non_measured_per_target.append(non_measured_subset)
    
    abduction_dir = os.path.join(output_dir, "abduction", "noiseless")
    
    indices = list(range(len(axioms)))
    
    for n in sorted(n_allows):
        n_dir = os.path.join(abduction_dir, f"{n}_axiom(s)_removed")
        os.makedirs(n_dir, exist_ok=True)
        
        all_combos = list(combinations(indices, n))
        
        for combo_idx, combo_indices in enumerate(all_combos, start=1):
            removed_axioms = [axioms[i] for i in combo_indices]
            remaining_axioms = [axioms[i] for i in indices if i not in combo_indices]
            
            combo_str = '_'.join(str(i + 1) for i in combo_indices) if combo_indices else "none"
            combo_dir = os.path.join(n_dir, f"combo_{combo_str}")
            
            logger.info(f"Processing combo {combo_idx}/{len(all_combos)}: removed indices {combo_indices}")
            
            # Step 1: Decomposition
            decomp_dir = os.path.join(combo_dir, "decomposition")
            decomp_result = run_decomposition(
                variables=variables,
                remaining_axioms=remaining_axioms,
                targets=targets,
                output_dir=decomp_dir,
                config=config
            )
            
            if decomp_result is None:
                logger.warning(f"Decomposition failed for combo {combo_str}")
                continue
            
            logger.info(f"Decomposition found {decomp_result.num_components} components")
            
            # Step 2: Reasoning
            reasoning_dir = os.path.join(combo_dir, "reasoning")
            reasoning_result = run_reasoning(
                variables=variables,
                remaining_axioms=remaining_axioms,
                targets=targets,
                decomp_result=decomp_result,
                measured_per_target=measured_per_target,
                non_measured_per_target=non_measured_per_target,
                num_removed=n,
                output_dir=reasoning_dir,
                config=config
            )
            
            if reasoning_result:
                logger.info(f"Found {len(reasoning_result.saved_combos)} saved, "
                           f"{len(reasoning_result.strong_candidates)} strong")
            else:
                logger.warning(f"Reasoning failed for combo {combo_str}")
            
            # Save summary
            summary_path = os.path.join(combo_dir, "summary.txt")
            with open(summary_path, 'w') as f:
                f.write(f"=== Abduction Summary ===\n")
                f.write(f"Removed axiom indices (1-based): {[i+1 for i in combo_indices]}\n")
                f.write(f"Removed axioms:\n")
                for ax in removed_axioms:
                    f.write(f"  {ax}\n")
                f.write(f"\nDecomposition engine: {config.decomposition.engine}\n")
                f.write(f"Number of components: {decomp_result.num_components if decomp_result else 'N/A'}\n")
                
                if reasoning_result:
                    f.write(f"\nSaved combos (minimal): {len(reasoning_result.saved_combos)}\n")
                    for combo in reasoning_result.saved_combos:
                        f.write(f"  {combo}\n")
                    f.write(f"\nStrong candidates (minimal): {len(reasoning_result.strong_candidates)}\n")
                    for combo in reasoning_result.strong_candidates:
                        f.write(f"  {combo}\n")


def process_numerical_abduction(
    problem_name: str,
    noise_level: str,
    n_allows: set,
    output_dir: str,
    config: Config
) -> None:
    """
    Run numerical abduction (noisy case) for a specific noise level.
    
    Loads problem data from system_noise_<noise_level>.txt
    """
    logger = get_logger()
    logger.info(f"Running numerical abduction (noisy) for noise level: {noise_level}")
    
    # Load problem from noise-specific file
    filepath = os.path.join(config.problems.base_dir, problem_name, f"system_noise_{noise_level}.txt")
    
    if not os.path.exists(filepath):
        logger.error(f"Noise file not found: {filepath}")
        return
    
    problem_data = read_problem(filepath)
    problem_data['problem_name'] = problem_name
    problem_data['noise_level'] = noise_level
    
    variables = problem_data['variables']
    axioms = problem_data['equations']
    targets = problem_data['targets']
    
    logger.info(f"Loaded noisy problem: {len(variables)} variables, {len(axioms)} axioms, {len(targets)} targets")
    
    abduction_dir = os.path.join(output_dir, "abduction", "noisy", f"noise_{noise_level}")
    
    indices = list(range(len(axioms)))
    
    for n in sorted(n_allows):
        n_dir = os.path.join(abduction_dir, f"{n}_axiom(s)_removed")
        os.makedirs(n_dir, exist_ok=True)
        
        all_combos = list(combinations(indices, n))
        
        for combo_idx, combo_indices in enumerate(all_combos, start=1):
            removed_axioms = [axioms[i] for i in combo_indices]
            remaining_axioms = [axioms[i] for i in indices if i not in combo_indices]
            
            combo_str = '_'.join(str(i + 1) for i in combo_indices) if combo_indices else "none"
            combo_dir = os.path.join(n_dir, f"combo_{combo_str}")
            
            logger.info(f"Processing combo {combo_idx}/{len(all_combos)}: removed indices {combo_indices}")
            
            # Step 1: Witness set computation
            witness_dir = os.path.join(combo_dir, "decomposition", "witness_sets")
            witness_result = run_witness_set_computation(
                variables=variables,
                remaining_axioms=remaining_axioms,
                targets=targets,
                output_dir=witness_dir,
                config=config
            )
            
            if witness_result is None:
                logger.warning(f"Witness set computation failed for combo {combo_str}")
                continue
            
            logger.info(f"Witness set found {len(witness_result.components)} components")
            
            # Step 2: Symbolic regression
            regression_dir = os.path.join(combo_dir, "decomposition", "symbolic_regression")
            regression_results = perform_symbolic_regression(
                witness_result=witness_result,
                dropped_axioms=removed_axioms,
                dropped_indices=list(combo_indices),
                all_axioms=axioms,
                output_dir=regression_dir,
                config=config
            )
            
            logger.info(f"Symbolic regression produced {len(regression_results)} results")
            
            # Step 3: Generate KeyMaera scripts for reasoning
            reasoning_dir = os.path.join(combo_dir, "reasoning")
            os.makedirs(reasoning_dir, exist_ok=True)
            
            for target_idx, target in enumerate(targets, start=1):
                script_path = generate_keymaera_script(
                    problem_name=problem_data.get('problem_name', 'unknown'),
                    target_index=target_idx,
                    axiom_combo=combo_str,
                    variables=variables,
                    known_axioms=remaining_axioms,
                    regression_results=regression_results,
                    target=target,
                    output_dir=reasoning_dir,
                    config=config
                )
                
                if script_path:
                    logger.info(f"Generated KeyMaera script: {script_path}")
            
            # Save summary
            summary_path = os.path.join(combo_dir, "summary.txt")
            with open(summary_path, 'w') as f:
                f.write(f"=== Numerical Abduction Summary ===\n")
                f.write(f"Noise level: {noise_level}\n")
                f.write(f"Removed axiom indices (1-based): {[i+1 for i in combo_indices]}\n")
                f.write(f"Removed axioms:\n")
                for ax in removed_axioms:
                    f.write(f"  {ax}\n")
                f.write(f"\nNumerical engine: {config.numerical.engine}\n")
                f.write(f"Samples per component: {config.numerical.samples_per_component}\n")
                f.write(f"Number of witness set components: {len(witness_result.components)}\n")
                f.write(f"Symbolic regression results: {len(regression_results)}\n")
                
                threshold = float(config.numerical.singular_value_threshold)
                f.write(f"\nRegression results below threshold ({threshold}):\n")
                good_fits = [r for r in regression_results 
                            if r.singular_value < threshold]
                for fit in good_fits:
                    f.write(f"  Axiom {fit.axiom_index}, Component {fit.component_index}:\n")
                    f.write(f"    Singular value: {fit.singular_value}\n")
                    f.write(f"    Polynomial: {fit.polynomial_string_normalized}\n")
                    if fit.coefficient_l2_error is not None:
                        f.write(f"    Coefficient L2 error: {fit.coefficient_l2_error}\n")


def process_problem(problem_name: str, config: Config) -> None:
    """Process a single problem through the entire pipeline."""
    logger = get_logger()
    logger.info(f"Processing problem: {problem_name}")
    
    # Load problem
    filepath = os.path.join(config.problems.base_dir, problem_name, "system.txt")
    
    if not os.path.exists(filepath):
        logger.error(f"Problem file not found: {filepath}")
        return
    
    problem_data = read_problem(filepath)
    problem_data['problem_name'] = problem_name
    
    variables = problem_data['variables']
    axioms = problem_data['equations']
    targets = problem_data['targets']
    
    logger.info(f"Loaded problem: {len(variables)} variables, {len(axioms)} axioms, {len(targets)} targets")
    
    # Setup output directory
    output_dir = os.path.join(config.output.base_dir, problem_name)
    os.makedirs(output_dir, exist_ok=True)
    
    # Save problem data
    data_path = os.path.join(output_dir, "data.txt")
    with open(data_path, 'w') as f:
        f.write(f"Variables: {variables}\n")
        f.write(f"Measured Variables: {problem_data['measured_vars']}\n")
        f.write(f"Non-Measured Variables: {problem_data['non_measured_vars']}\n")
        f.write(f"Axioms: {axioms}\n")
        f.write(f"Targets: {targets}\n")
    
    # Determine which axiom removal sizes to use
    n_allows = parse_num_axiom_spec(config.axiom_removal.num_axioms, max_n=len(axioms))
    logger.info(f"Axiom removal sizes: {sorted(n_allows)}")
    
    # Run analyses based on config
    if config.analyses.projection:
        process_projection(problem_data, output_dir, config)
    
    if config.analyses.dimensionality_check:
        process_dimensionality(problem_data, n_allows, output_dir, config)
    
    if config.analyses.algebraic_abduction:
        process_algebraic_abduction(problem_data, n_allows, output_dir, config)
    
    if config.analyses.numerical_abduction:
        # Loop over noise levels
        for noise_level in config.numerical.noise_levels:
            process_numerical_abduction(problem_name, noise_level, n_allows, output_dir, config)
    
    logger.info(f"Completed problem: {problem_name}")


def main(args=None):
    """Main entry point."""
    parser = argparse.ArgumentParser(
        description="AI-Noether: Abductive inference for scientific discovery"
    )
    parser.add_argument(
        "--config", "-c",
        type=str,
        required=True,
        help="Path to configuration YAML file"
    )
    
    cli_args = parser.parse_args(args=args)
    
    # Load configuration
    if not os.path.exists(cli_args.config):
        print(f"ERROR: Config file not found: {cli_args.config}")
        sys.exit(1)
    
    config = load_config(cli_args.config)
    
    # Setup logging
    log_dir = os.path.join(config.output.base_dir, "logs")
    os.makedirs(log_dir, exist_ok=True)
    log_file = os.path.join(log_dir, "ai_noether.log")
    
    setup_logger(
        log_level=config.execution.log_level,
        verbose=config.execution.verbose,
        log_file=log_file
    )
    
    logger = get_logger()
    logger.info("AI-Noether starting")
    logger.info(f"Config loaded from: {cli_args.config}")
    
    # Validate config
    issues = validate_config(config)
    for issue in issues:
        if issue.startswith("ERROR"):
            logger.error(issue)
            sys.exit(1)
        else:
            logger.warning(issue)
    
    # Get problems to process
    problems = config.problems.problem_list
    if not problems:
        # Try to auto-detect problems
        base_dir = config.problems.base_dir
        if os.path.isdir(base_dir):
            problems = [d for d in os.listdir(base_dir) 
                       if os.path.isdir(os.path.join(base_dir, d))
                       and os.path.exists(os.path.join(base_dir, d, "system.txt"))]
    
    if not problems:
        logger.error("No problems found to process")
        sys.exit(1)
    
    logger.info(f"Processing {len(problems)} problems: {problems}")
    
    # Process each problem
    for problem_name in problems:
        try:
            process_problem(problem_name, config)
        except Exception as e:
            logger.error(f"Error processing {problem_name}: {e}")
            import traceback
            logger.debug(traceback.format_exc())
    
    logger.info("AI-Noether complete")


if __name__ == "__main__":
    main()
