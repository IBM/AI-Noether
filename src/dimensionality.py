"""
AI-Noether: Dimensionality check functions

This module handles comparing dimensions of ideals with/without removed axioms.
"""

import subprocess
import os
from typing import List, Optional
from pathlib import Path

from .config import Config
from .templates import fill_m2_dimensionality_template
from .parsers import parse_m2_dimensionality_output, DimensionalityResult
from .logging_utils import get_logger, log_subprocess_result


def run_dimensionality_check(
    variables: List[str],
    all_axioms: List[str],
    removed_axioms: List[str],
    targets: List[str],
    output_dir: str,
    config: Config
) -> Optional[DimensionalityResult]:
    """
    Run dimensionality check using Macaulay2.
    
    Compares:
    - dim(ideal(all_axioms))
    - dim(ideal(remaining_axioms))
    - dim(ideal(remaining_axioms + targets))
    
    Args:
        variables: List of variable names
        all_axioms: List of all axiom equations
        removed_axioms: List of axioms that were removed
        targets: List of target polynomials
        output_dir: Directory to save outputs
        config: Configuration object
    
    Returns:
        DimensionalityResult or None if failed
    """
    logger = get_logger()
    
    os.makedirs(output_dir, exist_ok=True)
    
    # Output files
    dim_output = os.path.join(output_dir, "dimensionality_output.txt")
    script_path = os.path.join(output_dir, "dimensionality_script.m2")
    
    # Fill template
    script_content = fill_m2_dimensionality_template(
        variables=variables,
        all_axioms=all_axioms,
        removed_axioms=removed_axioms,
        targets=targets,
        output_file=dim_output
    )
    
    # Write script
    with open(script_path, 'w') as f:
        f.write(script_content)
    
    logger.info(f"Running dimensionality check, script: {script_path}")
    
    # Run Macaulay2
    try:
        result = subprocess.run(
            [config.paths.macaulay2, "--script", script_path],
            capture_output=True,
            text=True,
            timeout=config.execution.timeout_dimensionality
        )
        
        log_subprocess_result(
            cmd=f"{config.paths.macaulay2} --script {script_path}",
            returncode=result.returncode,
            stdout=result.stdout,
            stderr=result.stderr,
            context="Dimensionality"
        )
        
        # Read output file
        if os.path.exists(dim_output):
            with open(dim_output, 'r') as f:
                output_content = f.read()
            
            return parse_m2_dimensionality_output(output_content)
        else:
            logger.error(f"Dimensionality output file not found: {dim_output}")
            return None
            
    except subprocess.TimeoutExpired:
        logger.error(f"Dimensionality check timed out after {config.execution.timeout_dimensionality}s")
        return None
    except Exception as e:
        logger.error(f"Dimensionality check failed: {e}")
        return None
