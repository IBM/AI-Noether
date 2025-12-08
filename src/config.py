"""
AI-Noether: Configuration loading and validation
"""

import yaml
import os
from dataclasses import dataclass, field
from typing import List, Optional, Set


@dataclass
class PathsConfig:
    macaulay2: str = "/opt/homebrew/bin/M2"
    singular: str = "/opt/homebrew/bin/Singular"
    bertini: str = "/usr/local/bin/bertini"


@dataclass
class ProblemsConfig:
    base_dir: str = "systems_and_phenomena/real"
    problem_list: List[str] = field(default_factory=list)


@dataclass
class OutputConfig:
    base_dir: str = "results/real"


@dataclass
class AxiomRemovalConfig:
    num_axioms: str = "all"


@dataclass
class AnalysesConfig:
    projection: bool = True
    dimensionality_check: bool = True
    algebraic_abduction: bool = True
    numerical_abduction: bool = True


@dataclass
class DecompositionConfig:
    engine: str = "singular"  # "m2" or "singular"


@dataclass
class ReasoningConfig:
    require_literal_gb: bool = True
    max_candidate_size: int = -1


@dataclass
class NumericalConfig:
    engine: str = "bertini"  # "bertini" or "nag"
    noise_levels: List[str] = field(default_factory=lambda: ["1e-1", "1e-2", "1e-4"])
    samples_per_component: int = 100
    singular_value_threshold: float = 1e-6


@dataclass
class NormalizationConfig:
    normalize_coefficients: bool = True
    complex_threshold: float = 1e-6
    compute_coefficient_error: bool = True


@dataclass
class RobustFittingConfig:
    enabled: bool = True
    outlier_percentile: float = 90.0
    max_iterations: int = 5
    min_points: int = 10


@dataclass
class ExecutionConfig:
    timeout_projection: int = 600
    timeout_dimensionality: int = 600
    timeout_decomposition: int = 1200
    timeout_reasoning: int = 3600
    timeout_witness_set: int = 7200
    verbose: bool = False
    log_level: str = "INFO"


@dataclass
class Config:
    paths: PathsConfig = field(default_factory=PathsConfig)
    problems: ProblemsConfig = field(default_factory=ProblemsConfig)
    output: OutputConfig = field(default_factory=OutputConfig)
    axiom_removal: AxiomRemovalConfig = field(default_factory=AxiomRemovalConfig)
    analyses: AnalysesConfig = field(default_factory=AnalysesConfig)
    decomposition: DecompositionConfig = field(default_factory=DecompositionConfig)
    reasoning: ReasoningConfig = field(default_factory=ReasoningConfig)
    numerical: NumericalConfig = field(default_factory=NumericalConfig)
    normalization: NormalizationConfig = field(default_factory=NormalizationConfig)
    robust_fitting: RobustFittingConfig = field(default_factory=RobustFittingConfig)
    execution: ExecutionConfig = field(default_factory=ExecutionConfig)


def load_config(config_path: str) -> Config:
    """Load configuration from YAML file."""
    with open(config_path, 'r') as f:
        data = yaml.safe_load(f)
    
    config = Config()
    
    if 'paths' in data:
        config.paths = PathsConfig(**data['paths'])
    
    if 'problems' in data:
        config.problems = ProblemsConfig(**data['problems'])
    
    if 'output' in data:
        config.output = OutputConfig(**data['output'])
    
    if 'axiom_removal' in data:
        config.axiom_removal = AxiomRemovalConfig(**data['axiom_removal'])
    
    if 'analyses' in data:
        config.analyses = AnalysesConfig(**data['analyses'])
    
    if 'decomposition' in data:
        config.decomposition = DecompositionConfig(**data['decomposition'])
    
    if 'reasoning' in data:
        config.reasoning = ReasoningConfig(**data['reasoning'])
    
    if 'numerical' in data:
        config.numerical = NumericalConfig(**data['numerical'])
    
    if 'normalization' in data:
        config.normalization = NormalizationConfig(**data['normalization'])
    
    if 'robust_fitting' in data:
        config.robust_fitting = RobustFittingConfig(**data['robust_fitting'])
    
    if 'execution' in data:
        config.execution = ExecutionConfig(**data['execution'])
    
    return config


def parse_num_axiom_spec(spec: str, max_n: int) -> Set[int]:
    """
    Parse axiom removal specification.
    
    Accepts forms:
      - '[a,b]'  inclusive range
      - 'a..b'   inclusive range
      - 'a,b,c'  explicit set
      - 'k'      single n
      - 'all'    {0..max_n}
    
    Returns a set clipped to [0, max_n].
    """
    spec = spec.strip()
    vals = set()
    
    if spec.lower() == "all":
        return set(range(0, max_n + 1))
    
    if spec.startswith("[") and spec.endswith("]"):
        left, right = spec[1:-1].split(",", 1)
        a, b = int(left.strip()), int(right.strip())
        vals = set(range(min(a, b), max(a, b) + 1))
    elif ".." in spec:
        left, right = spec.split("..", 1)
        a, b = int(left.strip()), int(right.strip())
        vals = set(range(min(a, b), max(a, b) + 1))
    elif "," in spec:
        vals = {int(t.strip()) for t in spec.split(",") if t.strip()}
    else:
        vals = {int(spec)}
    
    # Clip to [0, max_n]
    return {n for n in vals if 0 <= n <= max_n}


def validate_config(config: Config) -> List[str]:
    """Validate configuration and return list of warnings/errors."""
    issues = []
    
    # Check paths exist
    if not os.path.exists(config.paths.macaulay2):
        issues.append(f"WARNING: Macaulay2 not found at {config.paths.macaulay2}")
    
    if config.decomposition.engine == "singular" and not os.path.exists(config.paths.singular):
        issues.append(f"WARNING: Singular not found at {config.paths.singular}")
    
    if config.numerical.engine == "bertini" and not os.path.exists(config.paths.bertini):
        issues.append(f"WARNING: Bertini not found at {config.paths.bertini}")
    
    # Check decomposition engine
    if config.decomposition.engine not in ["m2", "singular"]:
        issues.append(f"ERROR: Invalid decomposition engine: {config.decomposition.engine}")
    
    # Check numerical engine
    if config.numerical.engine not in ["bertini", "nag"]:
        issues.append(f"ERROR: Invalid numerical engine: {config.numerical.engine}")
    
    return issues
