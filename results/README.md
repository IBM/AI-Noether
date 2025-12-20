# Results Directory Structure

This directory contains the output from AI-Noether analysis runs. Each problem gets its own subdirectory with a consistent structure.

## Directory Layout

```
results/
├── <problem_name>/
│   ├── data.txt                          # Copy of input problem data
│   ├── logs/
│   │   └── ai_noether.log                # Detailed execution log
│   │
│   ├── projection/                       # (if analyses.projection: true)
│   │   └── target_1/
│   │       ├── projection_script.m2
│   │       └── projection_output.txt
│   │
│   ├── dimensionality_check/             # (if analyses.dimensionality_check: true)
│   │   └── 1_axioms_removed/
│   │       ├── subset_1/
│   │       │   ├── dimensionality_script.m2
│   │       │   └── dimensionality_output.txt
│   │       └── aggregate_results.txt
│   │
│   └── abduction/
│       ├── noiseless/                    # (if analyses.algebraic_abduction: true)
│       │   ├── 1_axiom(s)_removed/
│       │   │   ├── combo_1/
│       │   │   │   ├── summary.txt
│       │   │   │   ├── decomposition/
│       │   │   │   │   ├── decomposition_script.m2 (or .sing)
│       │   │   │   │   ├── decomposition_output.txt (or _stdout.txt)
│       │   │   │   │   └── decomposition_parsed.txt
│       │   │   │   └── reasoning/
│       │   │   │       ├── candidate_sets.txt
│       │   │   │       ├── reasoning_script.m2
│       │   │   │       ├── reasoning_output.txt
│       │   │   │       └── reasoning_filtered.txt
│       │   │   ├── combo_2/
│       │   │   └── ...
│       │   ├── 2_axiom(s)_removed/
│       │   └── 3_axiom(s)_removed/
│       │
│       └── noisy/                        # (if analyses.numerical_abduction: true)
│           └── noise_1e-8/
│               ├── 1_axiom(s)_removed/
│               │   └── combo_1/
│               │       ├── summary.txt
│               │       ├── decomposition/
│               │       │   ├── witness_sets/
│               │       │   │   ├── witness_script.m2
│               │       │   │   └── witness_set.txt
│               │       │   └── symbolic_regression/
│               │       │       ├── fit_axiom1_comp1.txt
│               │       │       └── fit_axiom1_comp2.txt
│               │       └── reasoning/
│               │           └── reasoning_target1_combo1.kyx
│               └── ...
│
└── logs/
    └── ai_noether.log                    # Global log file
```

## File Descriptions

### Top-Level Files

#### `data.txt`
Copy of the parsed input problem:
```
Variables: [T, a, G, M, pi, v, r, omega, F, m]
Measured Variables: [T, a, G, M, pi]
Non-Measured Variables: [v, r, omega, F, m]
Axioms: [v - omega*r, omega*T - 2*pi, ...]
Targets: [T^2*a^3 - 4*pi^2*G*M]
```

#### `logs/ai_noether.log`
Detailed execution log with timestamps:
```
2024-01-15 10:23:45 | INFO     | Processing problem: kepler
2024-01-15 10:23:46 | INFO     | Running algebraic abduction (noiseless)
2024-01-15 10:23:47 | DEBUG    | Decomposition found 3 components
```

### Projection Directory

#### `projection_output.txt`
Groebner basis and elimination results:
```
Groebner basis of the ideal:
matrix {{v-omega*r, omega*T-2*pi, ...}}

Groebner basis of the eliminated ideal:
matrix {{T^2*a^3-4*pi^2*G*M}}

Target checks in eliminated ideal:
q = T^2*a^3-4*pi^2*G*M
  remainderZero: true
  appearsLiterallyInGB: true
```

### Dimensionality Check Directory

#### `dimensionality_output.txt`
Dimension comparison:
```
=== Dimension Analysis ===
Original dimension: 4
Reduced dimension: 5
Discovered dimension: 4
Original == Discovered: true
```

#### `aggregate_results.txt`
Summary across all subsets:
```
=== Results for removing 1 axioms ===
Total subsets tested: 6
Dimension distribution:
  Dimension 4: 4 cases
  Dimension 5: 2 cases
Cases with equal dimension: 4
```

### Noiseless Abduction Directory

#### `combo_*/summary.txt`
Summary for each axiom removal combination:
```
=== Abduction Summary ===
Removed axiom indices (1-based): [3]
Removed axioms:
  v^2*r - G*M

Decomposition engine: singular
Number of components: 2

Saved combos (minimal): 1
  [v^2*r-G*M]

Strong candidates (minimal): 1
  [v^2*r-G*M]
```

#### `decomposition/decomposition_parsed.txt`
Parsed primary decomposition:
```
Number of components: 2

COMPONENT_1:
  num_generators: 5
  GEN: v-omega*r
  GEN: omega*T-2*pi
  GEN: v^2*r-G*M
  ...

COMPONENT_2:
  num_generators: 3
  GEN: r
  GEN: v
  ...
```

#### `reasoning/candidate_sets.txt`
Candidates tested during reasoning:
```
Number of components: 2
Number of remaining axioms: 5
Number of targets: 1
Max candidate set size: 2
Number of candidate sets (after filtering): 8

Filtering method: ideal membership test
  Generators g where g ∈ ideal(remaining_axioms + targets) are excluded

Candidate sets to test:
  Candidate 0: [] (empty set / baseline)
  Candidate 1: [v^2*r-G*M]
  ...
```

#### `reasoning/reasoning_filtered.txt`
Final results after duplicate/superset elimination:
```
=== Filtered Results (duplicates and supersets removed) ===

SAVED_COMBOS (minimal):
  [v^2*r-G*M]

Total saved (after filtering): 1
Total saved (before filtering): 3

STRONG_CANDIDATES (minimal):
  [v^2*r-G*M]

Total strong (after filtering): 1
Total strong (before filtering): 3
```

### Noisy Abduction Directory

#### `witness_sets/witness_set.txt`
Numerical irreducible decomposition output:
```
variable ordering: T, a, G, M, pi, v, r, omega, F, m

component_1:
equations:
v-omega*r
omega*T-2*pi
...
points:
1.23+0.01i, 4.56-0.02i, ...
2.34+0.00i, 5.67+0.01i, ...
...
```

#### `symbolic_regression/fit_axiom1_comp1.txt`
Symbolic regression result for one dropped axiom on one component:
```
=== Symbolic Regression Result ===
Dropped axiom index (1-based): 1
Dropped axiom text: v^2*r - G*M
Component index: 1
Variables: [v, r, G, M]
Number of monomials: 2
Total degree: 3
Number of points (total): 100
Number of points (used after outlier removal): 85
Smallest singular value: 1.23e-08
Relative residual: 2.34e-09

Inferred polynomial (raw):
  (0.999998+0.000001i)*v^2*r + (-1.000003-0.000002i)*G*M = 0

Inferred polynomial (normalized):
  1*v^2*r + (-1.000005)*G*M = 0

Coefficient L2 error vs true: 5.12e-06
```

#### `reasoning/reasoning_target1_combo1.kyx`
KeYmaera X proof template (not auto-executed):
```
ArchiveEntry "kepler_target1_combo1"

ProgramVariables
  Real T;
  Real a;
  ...
End.

Problem
  (\exists c1 \exists c2 ...
    (c1 > 0 & c2 > 0 & ...
      (\forall T \forall a ...
        ((T > 0 & a > 0 & ...)
          & (axiom1 = 0)
          & (c1 * v^2*r + c2 * G*M = 0))
        -> (target = 0))))
End.
```

## Interpreting Results

### Successful Recovery (Noiseless)
Look in `reasoning_filtered.txt`:
- **SAVED_COMBOS**: Axiom sets that prove the target (via ideal membership)
- **STRONG_CANDIDATES**: Axiom sets where target appears literally in GB

If the removed axiom appears in STRONG_CANDIDATES, it was successfully recovered.

### Successful Recovery (Noisy)
Check `symbolic_regression/fit_axiom*_comp*.txt`:
- **Coefficient L2 error**: Lower is better (< 1e-3 is excellent)
- **Singular value**: Lower indicates better fit
- Compare inferred polynomial to original axiom

### Component Matching
For noisy case, compare:
- Number of components in noisy `summary.txt`
- Number of components in noiseless `summary.txt` for same combo

Matching component counts indicate the numerical decomposition worked correctly.

## Visualization

Use `plot_noise_results.py` to generate summary plots:

```bash
python plot_noise_results.py \
    --results-dir results \
    --output-dir figures \
    --problems kepler pendulum time_dilation
```

This generates:
- `noisy_experiment_all.png`: Coefficient errors for all completed runs
- `noisy_experiment_filtered.png`: Only runs with correct component counts
- `noisy_experiment_component_heatmap.png`: Recovery rates by problem/noise/axioms
