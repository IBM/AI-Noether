"""
AI-Noether: Abductive inference for scientific discovery

This package provides tools for:
- Algebraic decomposition (via Macaulay2 or Singular)
- Reasoning over candidate axiom sets
- Numerical irreducible decomposition (witness sets)
- Symbolic regression on sampled points
- KeyMaera script generation for noisy reasoning
"""

from .config import Config, load_config, parse_num_axiom_spec
from .parsers import read_problem, vars_in_poly
from .decomposition import run_decomposition
from .reasoning import run_reasoning
from .numerical import (
    run_witness_set_computation,
    perform_symbolic_regression,
    generate_keymaera_script
)
from .projection import run_projection
from .dimensionality import run_dimensionality_check

__version__ = "2.0.0"
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
    "generate_keymaera_script",
    "run_projection",
    "run_dimensionality_check",
]
