# AI-Noether: Abductive Inference for Scientific Discovery

A system for discovering missing axioms in physics and mathematics through algebraic and numerical methods. Given a set of known axioms (with some missing) and target consequences, AI-Noether identifies which axioms are needed to derive the targets.

This repository accompanies the paper *Bridging the Gap Between Scientific Laws Derived by AI Systems and Canonical Knowledge via Abductive Inference with AI-Noether*, accepted for publication in **Nature Communications** (see [Citation](#citation)). The accepted manuscript is in [`AI-Noether.pdf`](AI-Noether.pdf) and the Supplementary Information in [`AI-Noether-SI.pdf`](AI-Noether-SI.pdf).

<p align="center">
  <img src="assets/emergence.webp" alt="Illustration: a grey complex of surfaces takes on colour one piece at a time; the red, green, purple and blue pieces settle into a row, and a gold winged surface rises from the gap at the centre and flies toward the light." width="800">
</p>
<p align="center"><em>Illustration (not computed output): a variety separates into its irreducible components, and a new component rises from the gap at the centre.</em></p>

## Overview

AI-Noether implements the abductive inference framework which:

1. **Encodes** axioms and consequences as polynomial equations defining algebraic varieties
2. **Decomposes** varieties via primary decomposition (noiseless) or numerical irreducible decomposition (noisy)
3. **Reasons** by testing if candidate axiom sets prove the target consequences
4. **Recovers** missing axiom coefficients via symbolic regression (noisy case)

The system supports two modes:

- **Algebraic (Noiseless)**: Exact symbolic computation using Groebner bases
- **Numerical (Noisy)**: Handles measurement noise via witness sets and symbolic regression

<p align="center">
  <img src="assets/varieties.gif" alt="A variety, shown in blue, decomposes into three irreducible components, shown in red, green and purple, which then separate." width="800">
</p>
<p align="center"><em>A variety (the solution set of a polynomial system) and its decomposition into irreducible components, whose union is the original variety (Fig. 4a of the paper). AI-Noether searches these components for the missing axioms.</em></p>

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

Copy the template and customize for your environment:

```bash
cp config_template.yaml config.yaml
```

Edit `config.yaml` to set paths to external tools:

```yaml
paths:
  macaulay2: "/path/to/M2"           # Required - find with: which M2
  singular: "/path/to/Singular"      # Optional - find with: which Singular
  bertini: "/path/to/bertini"        # Optional - for numerical methods
```

The template file (`config_template.yaml`) contains detailed comments explaining each parameter.

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
./run.sh config.yaml
```

Or directly:

```bash
python -m src.main --config config.yaml
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
AI-Noether/
  README.md                 # This file
  CITATION.cff              # Citation metadata (paper and software)
  AI-Noether.pdf            # Accepted manuscript
  AI-Noether-SI.pdf         # Supplementary Information
  assets/                   # README figures
  config_template.yaml      # Configuration template (copy to config.yaml)
  config.yaml               # Your local configuration (git-ignored)
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

## Reproducing the Paper

The defaults in `config_template.yaml` match the settings reported in the paper: 1000 samples per witness-set component, a singular-value threshold of 0.5, robust fitting that drops the top 10% of residuals, and a 2-hour (7200 s) witness-set timeout. The experiments were run on an Apple M4 MacBook Pro with 16 GB of memory (Supplementary Information, Implementation and Hardware).

The `results/` directory holds the output tree for the 12 benchmark systems. Compton scattering is left out of Fig. 6 because too few of its noisy runs finish within the timeout (Supplementary Information, Supplementary Note 5).

## Configuration Reference

The configuration file controls all aspects of AI-Noether. See `config_template.yaml` for detailed comments on each parameter.

### Quick Reference

| Section | Key Parameters |
|---------|---------------|
| `paths` | `macaulay2` (required), `singular`, `bertini` |
| `problems` | `base_dir`, `problem_list` |
| `output` | `base_dir` |
| `axiom_removal` | `num_axioms`: "all", "[1,3]", "1..3", "1,2,3", or "2" |
| `analyses` | `projection`, `dimensionality_check`, `algebraic_abduction`, `numerical_abduction` |
| `decomposition` | `engine`: "m2" or "singular" |
| `reasoning` | `require_literal_gb`, `max_candidate_size` |
| `numerical` | `engine`: "bertini" or "nag", `noise_levels`, `samples_per_component` |
| `normalization` | `normalize_coefficients`, `complex_threshold`, `compute_coefficient_error` |
| `robust_fitting` | `enabled`, `outlier_percentile`, `max_iterations`, `min_points` |
| `execution` | `timeout_*`, `verbose`, `log_level` |

### Example: Minimal Configuration

```yaml
paths:
  macaulay2: "/opt/homebrew/bin/M2"

problems:
  base_dir: "systems_and_phenomena/"
  problem_list:
    - "kepler"

output:
  base_dir: "results/"

axiom_removal:
  num_axioms: "[1,2]"

analyses:
  algebraic_abduction: true

decomposition:
  engine: "singular"

execution:
  verbose: true
  log_level: "INFO"
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

If you use AI-Noether in your research, please cite the paper:

```bibtex
@article{srivastava2026ainoether,
  title   = {Bridging the Gap Between Scientific Laws Derived by {AI} Systems and Canonical Knowledge via Abductive Inference with {AI-Noether}},
  author  = {Srivastava, Karan and Dash, Sanjeeb and Cory-Wright, Ryan and Trager, Barry and Cornelio, Cristina and Horesh, Lior},
  journal = {Nature Communications},
  year    = {2026},
  note    = {Accepted; in press}
}
```

The preprint is available as [arXiv:2509.23004](https://arxiv.org/abs/2509.23004). GitHub's "Cite this repository" button gives citation metadata for both the paper and this software, generated from [`CITATION.cff`](CITATION.cff).

## Authors

- Karan Srivastava (University of Wisconsin-Madison; IBM Research), corresponding author
- Sanjeeb Dash (IBM Research)
- Ryan Cory-Wright (Imperial Business School)
- Barry Trager (IBM Research)
- Cristina Cornelio (Samsung AI, Cambridge)
- Lior Horesh (IBM Research)

Karan Srivastava wrote the codebase during his 2025 graduate research internship at IBM Research. Cristina Cornelio designed the formal-logic verification framework and its KeYmaera X code.

## License

This project is licensed under the MIT License - see the [LICENSE](LICENSE) file for details.

## Related Work

- **AI-Descartes**: C. Cornelio et al., "Combining data and theory for derivable scientific discovery with AI-Descartes," *Nature Communications* 14, 1777 (2023). [doi:10.1038/s41467-023-37236-y](https://doi.org/10.1038/s41467-023-37236-y)
- **AI-Hilbert**: R. Cory-Wright et al., "Evolving scientific discovery by unifying data and background knowledge with AI Hilbert," *Nature Communications* 15, 5922 (2024). [doi:10.1038/s41467-024-50074-w](https://doi.org/10.1038/s41467-024-50074-w)
- **AI Feynman**: S.-M. Udrescu and M. Tegmark, "AI Feynman: A physics-inspired method for symbolic regression," *Science Advances* 6, eaay2631 (2020). [doi:10.1126/sciadv.aay2631](https://doi.org/10.1126/sciadv.aay2631)
