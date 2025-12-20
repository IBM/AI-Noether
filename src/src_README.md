# Source Code Documentation

This directory contains the Python source code for AI-Noether.

## Module Overview

```
src/
├── __init__.py           # Package exports
├── main.py               # Entry point and orchestration
├── config.py             # Configuration loading and validation
├── parsers.py            # Parse problem files and tool outputs
├── templates.py          # Fill script templates
├── decomposition.py      # Primary decomposition (M2/Singular)
├── reasoning.py          # Test candidate axiom sets
├── numerical.py          # Witness sets and symbolic regression
├── projection.py         # Gröbner basis and elimination
├── dimensionality.py     # Ideal dimension comparisons
├── poly_utils.py         # Polynomial normalization utilities
└── logging_utils.py      # Logging configuration
```

## Module Details

### main.py

Entry point that orchestrates the entire pipeline:

```python
def main(args=None):
    """Main entry point - parses args, loads config, runs analyses."""

def process_problem(problem_name: str, config: Config) -> None:
    """Process a single problem through the entire pipeline."""

def process_algebraic_abduction(...) -> None:
    """Run noiseless algebraic abduction (decomposition + reasoning)."""

def process_numerical_abduction(...) -> None:
    """Run noisy numerical abduction (witness sets + regression)."""
```

**Usage**:
```bash
python -m src.main --config config.yaml
```

### config.py

Configuration dataclasses and loading:

```python
@dataclass
class Config:
    paths: PathsConfig
    problems: ProblemsConfig
    output: OutputConfig
    axiom_removal: AxiomRemovalConfig
    analyses: AnalysesConfig
    decomposition: DecompositionConfig
    reasoning: ReasoningConfig
    numerical: NumericalConfig
    normalization: NormalizationConfig
    robust_fitting: RobustFittingConfig
    execution: ExecutionConfig

def load_config(config_path: str) -> Config:
    """Load configuration from YAML file."""

def parse_num_axiom_spec(spec: str, max_n: int) -> Set[int]:
    """Parse axiom removal specification (e.g., '[1,3]', 'all', '2')."""

def validate_config(config: Config) -> List[str]:
    """Validate configuration and return warnings/errors."""
```

### parsers.py

Parse problem files and external tool outputs:

```python
# Data classes for results
@dataclass
class DecompositionResult:
    components: List[List[str]]
    num_components: int
    raw_output: str

@dataclass
class ReasoningResult:
    saved_combos: List[List[str]]
    strong_candidates: List[List[str]]
    raw_output: str

@dataclass
class WitnessSetResult:
    variable_order: List[str]
    components: List[WitnessSetComponent]
    raw_output: str

# Parsing functions
def read_problem(file_path: str) -> Dict[str, Any]:
    """Read a physics problem from a structured TXT file."""

def parse_m2_decomposition_output(output: str) -> DecompositionResult:
    """Parse M2 primary decomposition output."""

def parse_singular_decomposition_output(output: str) -> DecompositionResult:
    """Parse Singular minAss output."""

def parse_m2_witness_set_output(output: str) -> WitnessSetResult:
    """Parse M2 witness set output with complex coordinates."""

def vars_in_poly(poly: str, variables: List[str]) -> List[str]:
    """Find which variables appear in a polynomial string."""
```

### templates.py

Fill script templates with problem-specific data:

```python
def fill_m2_decomposition_template(...) -> str:
    """Fill the M2 primary decomposition template."""

def fill_singular_decomposition_template(...) -> str:
    """Fill the Singular decomposition template."""

def fill_m2_reasoning_template(...) -> str:
    """Fill the M2 reasoning template."""

def fill_m2_witness_set_template(...) -> str:
    """Fill the M2 witness set (NAG) template."""

def fill_keymaera_reasoning_template(...) -> str:
    """Fill the KeyMaera reasoning template for noisy case."""
```

### decomposition.py

Primary decomposition of polynomial ideals:

```python
def run_decomposition(
    variables: List[str],
    remaining_axioms: List[str],
    targets: List[str],
    output_dir: str,
    config: Config
) -> Optional[DecompositionResult]:
    """Run primary decomposition using configured engine (M2 or Singular)."""

def run_decomposition_m2(...) -> Optional[DecompositionResult]:
    """Run primary decomposition using Macaulay2."""

def run_decomposition_singular(...) -> Optional[DecompositionResult]:
    """Run primary decomposition using Singular (minAss - faster)."""
```

### reasoning.py

Test if candidate axiom sets prove targets:

```python
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
    """Complete reasoning pipeline with duplicate/superset elimination."""

def generate_candidate_sets(
    decomp_result: DecompositionResult,
    remaining_axioms: List[str],
    targets: List[str],
    variables: List[str],
    m2_path: str,
    num_removed: int,
    max_size: int = -1
) -> List[List[str]]:
    """Generate candidate axiom sets from decomposition components.
    
    Filters out generators that are in ideal(remaining_axioms + targets)
    since they contain no new information.
    """

def filter_supersets(candidates: List[List[str]]) -> List[List[str]]:
    """Keep only minimal sets - if {A} proves Q, don't keep {A, B}."""
```

### numerical.py

Numerical methods for noisy case:

```python
def run_witness_set_computation(
    variables: List[str],
    remaining_axioms: List[str],
    targets: List[str],
    output_dir: str,
    config: Config
) -> Optional[WitnessSetResult]:
    """Compute numerical irreducible decomposition via witness sets."""

def perform_symbolic_regression(
    witness_result: WitnessSetResult,
    dropped_axioms: List[str],
    dropped_indices: List[int],
    all_axioms: List[str],
    output_dir: str,
    config: Config
) -> List[SymbolicRegressionResult]:
    """Fit polynomials to witness set points to recover coefficients."""

def normalize_coefficients(
    coeffs: np.ndarray,
    complex_threshold: float = 1e-6
) -> np.ndarray:
    """Normalize coefficients so largest has magnitude 1."""

def compute_coefficient_error(
    inferred: np.ndarray,
    true_coeffs: np.ndarray,
    monomials_inferred: List[Tuple[int, ...]],
    monomials_true: List[Tuple[int, ...]]
) -> float:
    """Compute L2 error with sign ambiguity handling."""

def fit_nullspace_robust(
    A: np.ndarray,
    outlier_percentile: float = 90.0,
    max_iterations: int = 5,
    min_points: int = 5
) -> Tuple[np.ndarray, float, float, np.ndarray]:
    """Robust null-space fitting with iterative outlier removal."""

def generate_keymaera_script(...) -> Optional[str]:
    """Generate KeyMaera script for formal verification."""
```

### poly_utils.py

Polynomial manipulation using Macaulay2:

```python
def filter_generators_m2(
    generators: List[str],
    remaining_axioms: List[str],
    targets: List[str],
    variables: List[str],
    m2_path: str
) -> List[str]:
    """Filter out generators that are in ideal(axioms + targets).
    
    Uses Gröbner basis reduction: if gen % I == 0, generator is redundant.
    """

def normalize_generators_m2(
    generators: List[str],
    variables: List[str],
    m2_path: str
) -> List[str]:
    """Normalize generators to canonical form using M2."""

def get_canonical_form_m2(
    poly: str,
    variables: List[str],
    m2_path: str
) -> str:
    """Get canonical form with positive leading coefficient."""
```

### projection.py

Gröbner basis and variable elimination:

```python
def run_projection(
    variables: List[str],
    axioms: List[str],
    measured_variables: List[str],
    non_measured_variables: List[str],
    output_dir: str,
    config: Config,
    targets: Optional[List[str]] = None
) -> Optional[str]:
    """Compute Gröbner basis and eliminate non-measured variables."""
```

### dimensionality.py

Ideal dimension comparisons:

```python
def run_dimensionality_check(
    variables: List[str],
    all_axioms: List[str],
    removed_axioms: List[str],
    targets: List[str],
    output_dir: str,
    config: Config
) -> Optional[DimensionalityResult]:
    """Compare dimensions of ideals with/without removed axioms."""
```

### logging_utils.py

Logging configuration:

```python
def setup_logger(
    log_level: str = "INFO",
    verbose: bool = False,
    log_file: Optional[str] = None
) -> logging.Logger:
    """Setup and configure the logger."""

def get_logger() -> logging.Logger:
    """Get the global logger instance."""

def log_subprocess_result(
    cmd: str,
    returncode: int,
    stdout: str,
    stderr: str,
    context: str = ""
):
    """Log the result of a subprocess call."""
```

## Key Algorithms

### Superset Elimination

When multiple candidate axiom sets prove the target, we only keep minimal ones:

```python
# If {A} proves Q, don't save {A, B}
# Uses normalized polynomial comparison to detect equivalence

for candidate in sorted_by_size:
    if not is_superset_of_any(candidate, kept_sets):
        kept_sets.add(candidate)
```

### Ideal Membership Filtering

Generators from decomposition are filtered if they're already implied:

```python
# Generator g is filtered out if g ∈ ideal(remaining_axioms + targets)
# Checked via Gröbner basis: g % I == 0

for gen in component_generators:
    if gen % (remaining_ideal + target_ideal) != 0:
        keep(gen)  # Contains new information
```

### Robust Coefficient Fitting

Symbolic regression with outlier removal:

```python
for iteration in range(max_iterations):
    # Fit nullspace on current inliers
    coeffs = svd_nullspace(design_matrix[inliers])
    
    # Compute residuals on all points
    residuals = abs(design_matrix @ coeffs)
    
    # Update inliers (keep points below percentile threshold)
    threshold = percentile(residuals[inliers], outlier_percentile)
    inliers = residuals <= threshold
```

### Sign Ambiguity Handling

Since p = 0 and -p = 0 are equivalent:

```python
# Compute error both ways and take minimum
error_same = norm(c1 - c2)
error_opposite = norm(c1 + c2)
return min(error_same, error_opposite)
```

## Extending the Code

### Adding a New Analysis Type

1. Create function in appropriate module (e.g., `my_analysis.py`)
2. Add configuration options to `config.py`
3. Add toggle to `analyses` section in config
4. Call from `main.py` in `process_problem()`

### Adding a New External Tool

1. Add path to `PathsConfig` in `config.py`
2. Create template in `templates/` directory
3. Add template filler in `templates.py`
4. Add runner function in appropriate module
5. Add validation in `validate_config()`

### Custom Polynomial Parsers

For domain-specific notation, modify `parsers.py`:

```python
def read_problem(file_path: str) -> Dict[str, Any]:
    # Add custom parsing logic here
    # e.g., handle units, special functions, etc.
```
