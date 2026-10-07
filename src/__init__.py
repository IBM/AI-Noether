"""
AI-Noether: Abductive inference for scientific discovery

This package provides tools for:
- Algebraic decomposition (via Macaulay2 or Singular)
- Reasoning over candidate axiom sets
- Numerical irreducible decomposition (witness sets)
- Symbolic regression on sampled points
- KeyMaera script generation for noisy reasoning (with Cartesian products and deduplication)
"""

from .config import Config, load_config, parse_num_axiom_spec
from .parsers import read_problem, vars_in_poly
from .decomposition import run_decomposition
from .reasoning import run_reasoning
from .numerical import (
    run_witness_set_computation,
    perform_symbolic_regression,
    generate_keymaera_scripts,  
    generate_keymaera_script,   # Deprecated, kept for backwards compatibility
    get_monomials_from_polynomial,
    SymbolicRegressionResult
)
from .projection import run_projection
from .dimensionality import run_dimensionality_check
from .templates import generate_keymaera_content

__version__ = "2.1.0"
__all__ = [
    "Config",
    "load_config",
    "parse_num_axiom_spec",
    "read_problem",
    "vars_in_poly",
    "run_decomposition",
    "run_reasoning",
    "run_witness_set_computation",
    "perform_symbolic_regression",
    "generate_keymaera_scripts",
    "generate_keymaera_script",
    "generate_keymaera_content",
    "get_monomials_from_polynomial",
    "SymbolicRegressionResult",
    "run_projection",
    "run_dimensionality_check",
]
