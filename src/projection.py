"""
AI-Noether: Projection/Elimination functions

This module handles computing Groebner bases and eliminating non-measured variables.
"""

import subprocess
import os
from typing import List, Optional
from pathlib import Path

from .config import Config
from .templates import fill_m2_projection_template
from .logging_utils import get_logger, log_subprocess_result


def run_projection(
    variables: List[str],
    axioms: List[str],
    measured_variables: List[str],
    non_measured_variables: List[str],
    output_dir: str,
    config: Config,
    targets: Optional[List[str]] = None
) -> Optional[str]:
    """
    Run projection/elimination analysis using Macaulay2.
    
    Computes Groebner basis and eliminates non-measured variables.
    Optionally checks if targets are in the eliminated ideal.
    
    Args:
        variables: List of all variable names
        axioms: List of axiom equations
        measured_variables: Variables to keep
        non_measured_variables: Variables to eliminate
        output_dir: Directory to save outputs
        config: Configuration object
        targets: Optional list of target polynomials to check
    
    Returns:
        Path to output file or None if failed
    """
    logger = get_logger()
    
    os.makedirs(output_dir, exist_ok=True)
    
    # Output files
    projection_output = os.path.join(output_dir, "projection_output.txt")
    script_path = os.path.join(output_dir, "projection_script.m2")
    
    # Fill template
    script_content = fill_m2_projection_template(
        variables=variables,
        axioms=axioms,
        measured_variables=measured_variables,
        non_measured_variables=non_measured_variables,
        output_file=projection_output,
        targets=targets
    )
    
    # Write script
    with open(script_path, 'w') as f:
        f.write(script_content)
    
    logger.info(f"Running projection, script: {script_path}")
    
    # Run Macaulay2
    try:
        result = subprocess.run(
            [config.paths.macaulay2, "--script", script_path],
            capture_output=True,
            text=True,
            timeout=config.execution.timeout_projection
        )
        
        log_subprocess_result(
            cmd=f"{config.paths.macaulay2} --script {script_path}",
            returncode=result.returncode,
            stdout=result.stdout,
            stderr=result.stderr,
            context="Projection"
        )
        
        if os.path.exists(projection_output):
            return projection_output
        else:
            logger.error(f"Projection output file not found: {projection_output}")
            return None
            
    except subprocess.TimeoutExpired:
        logger.error(f"Projection timed out after {config.execution.timeout_projection}s")
        return None
    except Exception as e:
        logger.error(f"Projection failed: {e}")
        return None
