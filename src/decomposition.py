"""
AI-Noether: Decomposition functions

This module handles primary decomposition using either Macaulay2 or Singular.
"""

import subprocess
import os
import tempfile
from typing import List, Optional
from pathlib import Path

from .config import Config
from .templates import fill_m2_decomposition_template, fill_singular_decomposition_template
from .parsers import (
    parse_m2_decomposition_output, 
    parse_singular_decomposition_output,
    DecompositionResult
)
from .logging_utils import get_logger, log_subprocess_result


def run_decomposition_m2(
    variables: List[str],
    remaining_axioms: List[str],
    targets: List[str],
    output_dir: str,
    config: Config
) -> Optional[DecompositionResult]:
    """
    Run primary decomposition using Macaulay2.
    
    Args:
        variables: List of variable names
        remaining_axioms: List of remaining axiom equations
        targets: List of target polynomials
        output_dir: Directory to save outputs
        config: Configuration object
    
    Returns:
        DecompositionResult or None if failed
    """
    logger = get_logger()
    
    os.makedirs(output_dir, exist_ok=True)
    
    # Output files
    decomp_output = os.path.join(output_dir, "decomposition_output.txt")
    script_path = os.path.join(output_dir, "decomposition_script.m2")
    
    # Fill template
    script_content = fill_m2_decomposition_template(
        variables=variables,
        remaining_axioms=remaining_axioms,
        targets=targets,
        output_file=decomp_output
    )
    
    # Write script
    with open(script_path, 'w') as f:
        f.write(script_content)
    
    logger.info(f"Running M2 decomposition, script: {script_path}")
    
    # Run Macaulay2
    try:
        result = subprocess.run(
            [config.paths.macaulay2, "--script", script_path],
            capture_output=True,
            text=True,
            timeout=config.execution.timeout_decomposition
        )
        
        log_subprocess_result(
            cmd=f"{config.paths.macaulay2} --script {script_path}",
            returncode=result.returncode,
            stdout=result.stdout,
            stderr=result.stderr,
            context="M2 Decomposition"
        )
        
        # Read output file
        if os.path.exists(decomp_output):
            with open(decomp_output, 'r') as f:
                output_content = f.read()
            
            return parse_m2_decomposition_output(output_content)
        else:
            logger.error(f"Decomposition output file not found: {decomp_output}")
            return None
            
    except subprocess.TimeoutExpired:
        logger.error(f"M2 decomposition timed out after {config.execution.timeout_decomposition}s")
        return None
    except Exception as e:
        logger.error(f"M2 decomposition failed: {e}")
        return None


def run_decomposition_singular(
    variables: List[str],
    remaining_axioms: List[str],
    targets: List[str],
    output_dir: str,
    config: Config
) -> Optional[DecompositionResult]:
    """
    Run primary decomposition using Singular (minAss).
    
    Args:
        variables: List of variable names
        remaining_axioms: List of remaining axiom equations
        targets: List of target polynomials
        output_dir: Directory to save outputs
        config: Configuration object
    
    Returns:
        DecompositionResult or None if failed
    """
    logger = get_logger()
    
    os.makedirs(output_dir, exist_ok=True)
    
    # Output files
    script_path = os.path.join(output_dir, "decomposition_script.sing")
    stdout_path = os.path.join(output_dir, "decomposition_stdout.txt")
    parsed_path = os.path.join(output_dir, "decomposition_parsed.txt")
    
    # Fill template
    script_content = fill_singular_decomposition_template(
        variables=variables,
        remaining_axioms=remaining_axioms,
        targets=targets,
        output_file=""  # Singular outputs to stdout
    )
    
    # Write script
    with open(script_path, 'w') as f:
        f.write(script_content)
    
    logger.info(f"Running Singular decomposition, script: {script_path}")
    
    # Run Singular
    try:
        result = subprocess.run(
            [config.paths.singular, "-q", script_path],  # -q for quiet mode
            capture_output=True,
            text=True,
            timeout=config.execution.timeout_decomposition
        )
        
        log_subprocess_result(
            cmd=f"{config.paths.singular} -q {script_path}",
            returncode=result.returncode,
            stdout=result.stdout,
            stderr=result.stderr,
            context="Singular Decomposition"
        )
        
        # Save stdout
        with open(stdout_path, 'w') as f:
            f.write(result.stdout)
        
        # Parse output
        decomp_result = parse_singular_decomposition_output(result.stdout)
        
        # Save parsed output
        with open(parsed_path, 'w') as f:
            f.write(f"Number of components: {decomp_result.num_components}\n\n")
            for i, comp in enumerate(decomp_result.components, 1):
                f.write(f"COMPONENT_{i}:\n")
                f.write(f"  num_generators: {len(comp)}\n")
                for gen in comp:
                    f.write(f"  GEN: {gen}\n")
                f.write("\n")
        
        return decomp_result
        
    except subprocess.TimeoutExpired:
        logger.error(f"Singular decomposition timed out after {config.execution.timeout_decomposition}s")
        return None
    except Exception as e:
        logger.error(f"Singular decomposition failed: {e}")
        return None


def run_decomposition(
    variables: List[str],
    remaining_axioms: List[str],
    targets: List[str],
    output_dir: str,
    config: Config
) -> Optional[DecompositionResult]:
    """
    Run primary decomposition using configured engine.
    
    Args:
        variables: List of variable names
        remaining_axioms: List of remaining axiom equations
        targets: List of target polynomials
        output_dir: Directory to save outputs
        config: Configuration object
    
    Returns:
        DecompositionResult or None if failed
    """
    if config.decomposition.engine.lower() == "singular":
        return run_decomposition_singular(
            variables, remaining_axioms, targets, output_dir, config
        )
    else:  # Default to M2
        return run_decomposition_m2(
            variables, remaining_axioms, targets, output_dir, config
        )
