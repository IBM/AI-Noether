# AI-Noether: Abductive Inference for Scientific Discovery

A system for discovering missing axioms in physics and mathematics through algebraic and numerical methods. Given a set of known axioms (with some missing) and target consequences, AI-Noether identifies which axioms are needed to derive the targets.

## Overview

AI-Noether implements the abductive inference framework which:

1. **Encodes** axioms and consequences as polynomial equations defining algebraic varieties
2. **Decomposes** varieties via primary decomposition (noiseless) or numerical irreducible decomposition (noisy)
3. **Reasons** by testing if candidate axiom sets prove the target consequences
4. **Recovers** missing axiom coefficients via symbolic regression (noisy case)

The system supports two modes:

- **Algebraic (Noiseless)**: Exact symbolic computation using Groebner bases
- **Numerical (Noisy)**: Handles measurement noise via witness sets and symbolic regression

## Installation

### Required Dependencies

**Python 3.8+** with packages:

```bash
pip install numpy sympy pyyaml matplotlib
```

**Macaulay2** (Required) - Computer algebra system for polynomial computations:

- macOS: `brew install macaulay2`
- Linux: See https://www.macaulay2.com/
- Verify: `M2 --version`

### Optional Dependencies

**Singular** (Recommended) - Faster primary decomposition:

- macOS: `brew install singular`
- Linux: See https://www.singular.uni-kl.de/
- Verify: `Singular --version`
- Note: Singular's `minAss` is significantly faster than M2's `primaryDecomposition` for larger ideals

**Bertini** (For numerical methods) - Numerical algebraic geometry:

- Download from https://bertini.nd.edu/
- Requires compilation; see Bertini documentation
- Note: Some variable names are reserved (see Troubleshooting)

**KeYmaera X** (For formal verification) - Theorem prover for hybrid systems:

- Download from https://www.keymaerax.org/
- Used for formal reasoning with noisy coefficients
- Note: Scripts are generated but not auto-executed

### Environment Setup

We recommend using conda:

```bash
conda create -n ai_noether_env python=3.10
conda activate ai_noether_env
pip install numpy sympy pyyaml matplotlib
```

## Quick Start

### 1. Configure paths

Copy and edit the configuration file:

```bash
cp config.yaml my_config.yaml
```

Edit `my_config.yaml` to set paths to external tools:

```yaml
paths:
  macaulay2: "/path/to/M2"
  singular: "/path/to/Singular"      # optional
  bertini: "/path/to/bertini"        # optional
```

### 2. Prepare your problem

Create a problem directory with a `system.txt` file:

```
systems_and_phenomena/
  my_problem/
    system.txt                    # Required: noiseless axioms
    system_noise_1e-2.txt         # Optional: noisy version
    system_noise_1e-5.txt         # Optional: noisy version
    system_noise_1e-8.txt         # Optional: noisy version
```

See `systems_and_phenomena/README.md` for input format details.

### 3. Run the analysis

```bash
./run.sh my_config.yaml
```

Or directly:

```bash
python -m src.main --config my_config.yaml
```

### 4. View results

Results are written to the configured output directory (default: `results/`).
See `results/README.md` for output structure details.

### 5. Generate plots (for noisy experiments)

```bash
./run_plots.sh
# or
python plot_noise_results.py --results-dir results --output-dir figures
```

## Directory Structure

```
ai_noether/
  README.md                 # This file
  config.yaml               # Configuration template
  run.sh                    # Main execution script
  run_plots.sh              # Plotting script runner
  plot_noise_results.py     # Visualization for noisy experiments

  src/                      # Source code
    __init__.py
    main.py                 # Main orchestration
    config.py               # Configuration loading
    parsers.py              # Parse M2/Singular output
    templates.py            # Template filling utilities
    decomposition.py        # Primary decomposition
    reasoning.py            # Reasoning with superset elimination
    numerical.py            # Witness sets and symbolic regression
    projection.py           # Projection/elimination analysis
    dimensionality.py       # Dimension checking
    poly_utils.py           # Polynomial normalization (M2-based)
    logging_utils.py        # Logging utilities

  templates/                # Script templates
    m2/                     # Macaulay2 templates
      decomposition.m2
      reasoning.m2
      projection.m2
      dimensionality.m2
      witness_set.m2
    singular/               # Singular templates
      decomposition.sing
    keymaera/               # KeYmaera X templates
      reasoning.kyx

  systems_and_phenomena/    # Problem definitions (input)
    <problem_name>/
      system.txt

  results/                  # Output directory
    <problem_name>/
      ...
```

## Configuration Reference

The configuration file (`config.yaml`) has the following sections:

### paths

```yaml
paths:
  macaulay2: "/opt/homebrew/bin/M2"       # Required
  singular: "/opt/homebrew/bin/Singular"  # Optional, for faster decomposition
  bertini: "/path/to/bertini"             # Optional, for numerical methods
```

### problems

```yaml
problems:
  base_dir: "systems_and_phenomena/"   # Directory containing problem subdirectories
  problem_list:                        # List of problems to process
    - "kepler"                         # Leave empty to auto-detect all
    - "time_dilation"
```

### output

```yaml
output:
  base_dir: "results/"                 # Where to write results
```

### axiom_removal

```yaml
axiom_removal:
  # How many axioms to remove. Options:
  # - "all": try all subset sizes from 0 to n
  # - "[1,3]" or "1..3": inclusive range
  # - "1,2,3": explicit list
  # - "2": single value
  num_axioms: "[1,3]"
```

### analyses

```yaml
analyses:
  projection: false              # Groebner basis and variable elimination
  dimensionality_check: false    # Compare ideal dimensions
  algebraic_abduction: true      # Noiseless decomposition + reasoning
  numerical_abduction: false     # Noisy witness sets + symbolic regression
```

### decomposition

```yaml
decomposition:
  engine: "singular"             # "m2" or "singular" (singular is faster)
```

### reasoning

```yaml
reasoning:
  require_literal_gb: true       # Require target to appear literally in Groebner basis
  max_candidate_size: -1         # Max subset size (-1 = num_removed + num_targets)
```

### numerical

```yaml
numerical:
  engine: "bertini"              # "bertini" or "nag" (M2 built-in)
  noise_levels:                  # Which noise levels to process
    - "1e-2"
    - "1e-5"
    - "1e-8"
  samples_per_component: 100     # Points to sample per witness set component
  singular_value_threshold: 200  # Threshold for good fit quality
```

### normalization

```yaml
normalization:
  normalize_coefficients: true   # Normalize max coefficient to 1
  complex_threshold: 1e-6        # Zero out small imaginary parts
  compute_coefficient_error: true  # Compute L2 error vs true coefficients
```

### robust_fitting

```yaml
robust_fitting:
  enabled: true                  # Enable iterative outlier removal
  outlier_percentile: 75.0       # Remove points above this percentile
  max_iterations: 1              # Outlier removal iterations
  min_points: 10                 # Minimum points to keep
```

### execution

```yaml
execution:
  timeout_projection: 600        # Seconds
  timeout_dimensionality: 600
  timeout_decomposition: 1200
  timeout_reasoning: 1200
  timeout_witness_set: 3600
  verbose: true                  # Print to stdout
  log_level: "INFO"              # DEBUG, INFO, WARNING, ERROR
```

## Troubleshooting

### Bertini Reserved Variable Names

Bertini has reserved names that cause cryptic errors. Avoid:

| Avoid | Use Instead | Reason |
|-------|-------------|--------|
| `Pi`, `pi` | `Piconst` | pi constant |
| `E`, `e`, `E1`, `E2` | `Eph1`, `En` | Euler's number / scientific notation |
| `I`, `i` | `Ivar`, `cur` | Imaginary unit |
| `cosTh`, `sinTh` | `cth`, `sth` | Function prefixes |
| `exp...` | `ex...` | exp function prefix |

**Solution**: Rename variables (e.g., `E1` to `Eph1`, `cosTh` to `cth`)

### Singular vs M2 Decomposition

If M2 decomposition times out, try switching to Singular:

```yaml
decomposition:
  engine: "singular"
```

### NAG (M2 Built-in) Issues

The M2 built-in numerical algebraic geometry package may fail with:

- Singular points requiring deflation
- Complex coefficient handling

**Solution**: Use Bertini instead (`numerical.engine: "bertini"`)

### Memory Issues

For large ideals, increase timeouts and consider:

- Reducing `max_candidate_size` in reasoning
- Processing fewer axiom removal sizes
- Using Singular instead of M2

## Citation

If you use AI-Noether in your research, please cite:

```bibtex
@article{ai-noether,
  title={AI-Noether: Abductive Inference for Scientific Discovery},
  author={...},
  journal={...},
  year={2024}
}
```

## License

[Your license here]

## Related Work

- **AI-Descartes**: Combining data and theory for derivable scientific discovery
- **AI-Hilbert**: Unifying data and background knowledge for automated scientific discovery
- **AI-Feynman**: Physics-inspired symbolic regression
