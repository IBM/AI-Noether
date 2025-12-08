# AI-Noether: Abductive Inference for Scientific Discovery

A system for discovering missing axioms in physics and mathematics through algebraic and numerical methods.

## Overview

AI-Noether implements the abductive inference framework from the paper, which:

1. **Encodes** axioms and consequences into algebraic varieties
2. **Decomposes** varieties via primary decomposition (noiseless) or numerical irreducible decomposition (noisy)
3. **Reasons** by testing if candidate axiom sets prove consequences

## Directory Structure

```
ai_noether/
├── config_template.yaml      # Configuration template (copy to config.yaml)
├── run.sh                    # Main entry script
├── templates/
│   ├── m2/
│   │   ├── projection.m2     # Groebner basis and elimination
│   │   ├── decomposition.m2  # Primary decomposition
│   │   ├── reasoning.m2      # Test candidate axiom sets
│   │   ├── dimensionality.m2 # Dimension comparison
│   │   └── witness_set.m2    # Numerical irreducible decomposition
│   ├── singular/
│   │   └── decomposition.sing # Faster primary decomposition via minAss
│   └── keymaera/
│       └── reasoning.kyx      # Existential reasoning template
└── src/
    ├── __init__.py
    ├── main.py               # Main orchestration
    ├── config.py             # Configuration loading
    ├── templates.py          # Template filling utilities
    ├── parsers.py            # Parse M2/Singular output
    ├── decomposition.py      # Primary decomposition (M2 or Singular)
    ├── reasoning.py          # Reasoning with superset elimination
    ├── numerical.py          # Witness sets, symbolic regression, KeyMaera
    ├── projection.py         # Projection/elimination analysis
    ├── dimensionality.py     # Dimension checking
    └── logging_utils.py      # Logging utilities
```

## Installation

### Dependencies

**Python packages:**
```bash
pip install numpy sympy pyyaml
```

**External tools (configure paths in config.yaml):**
- Macaulay2 (required): https://www.macaulay2.com/
- Singular (optional, faster decomposition): https://www.singular.uni-kl.de/
- Bertini (optional, for numerical methods): https://bertini.nd.edu/
- KeyMaera X (optional, for noisy reasoning): https://www.keymaerax.org/

## Usage

1. Copy and customize the configuration:
   ```bash
   cp config_template.yaml config.yaml
   # Edit config.yaml with your paths and settings
   ```

2. Prepare your problem files in the format:
   ```
   systems_and_phenomena/real/problem_name/system.txt
   ```
   
   Each `system.txt` should contain:
   ```
   Variables: [x, y, z, ...]
   
   Equations:
   x^2 - y
   y*z - 1
   ...
   
   Measured Variables: [x, z]
   
   Target Polynomial:
   x^2*z - 1
   ```

3. Run the analysis:
   ```bash
   ./run.sh config.yaml
   ```

## Configuration

Key settings in `config.yaml`:

### Decomposition Engine
```yaml
decomposition:
  engine: "singular"  # "m2" or "singular" (singular is faster)
```

### Analyses to Run
```yaml
analyses:
  projection: true              # Groebner basis and elimination
  dimensionality_check: true    # Compare ideal dimensions
  algebraic_abduction: true     # Noiseless decomposition + reasoning
  numerical_abduction: true     # Noisy witness sets + symbolic regression
```

### Axiom Removal
```yaml
axiom_removal:
  num_axioms: "all"    # "all", "[1,3]", "1..3", "1,2,3", or just "2"
```

### Symbolic Regression (Noisy Case)
```yaml
normalization:
  normalize_coefficients: true   # Normalize max coefficient to 1
  complex_threshold: 1e-6        # Zero out small imaginary parts
  compute_coefficient_error: true # Compute L2 error vs true coefficients
```

## Output Structure

Results are organized as:
```
results/problem_name/
├── projection/                  # (if enabled)
│   └── target_1/
├── dimensionality_check/        # (if enabled)
│   └── 1_axioms_removed/
│       └── subset_1/
├── abduction/
│   ├── noiseless/
│   │   └── 1_axiom(s)_removed/
│   │       └── combo_1/
│   │           ├── decomposition/
│   │           │   ├── decomposition_script.m2 (or .sing)
│   │           │   └── decomposition_output.txt
│   │           └── reasoning/
│   │               ├── reasoning_script.m2
│   │               ├── reasoning_output.txt
│   │               └── reasoning_filtered.txt
│   └── noisy/
│       └── 1_axiom(s)_removed/
│           └── combo_1/
│               ├── decomposition/
│               │   ├── witness_sets/
│               │   │   └── witness_set.txt
│               │   └── symbolic_regression/
│               │       └── fit_axiom1_comp1.txt
│               └── reasoning/
│                   └── reasoning_target1_combo1.kyx
└── logs/
    └── ai_noether.log
```

## Key Features

### Superset Elimination
The reasoning step automatically filters out:
- **Duplicates**: Same axiom set appearing multiple times
- **Supersets**: If `{A}` proves Q, don't save `{A, B}`

### Singular Integration
For faster primary decomposition:
```yaml
decomposition:
  engine: "singular"
```

Singular's `minAss` is significantly faster than M2's `primaryDecomposition` for larger ideals.

### Coefficient Normalization
For noisy symbolic regression:
- Normalizes largest coefficient to 1
- Zeros out imaginary parts below threshold
- Computes L2 error vs true axiom coefficients

### KeyMaera Templates
For noisy reasoning, generates `.kyx` files with:
- Existentially quantified coefficients
- Known axioms as exact equations
- Abducted axioms with symbolic coefficients

Templates are saved but NOT auto-executed (run KeyMaera manually).

## Logging

Configure verbosity in `config.yaml`:
```yaml
execution:
  verbose: false      # Print to stdout
  log_level: "INFO"   # DEBUG, INFO, WARNING, ERROR
```

All logs are saved to `results/*/logs/ai_noether.log`.

## License

[Your license here]
