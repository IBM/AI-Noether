# AI-Noether

**AI-Noether** is a Python/Macaulay2 pipeline for **abductive inference of axioms** in algebraic physics systems from our paper: [AI Noether (arXiv:2509.23004)](https://arxiv.org/abs/2509.23004)
Given a system of polynomial axioms and a *target polynomial* (a "consequence"), the framework automatically analyzes which combinations of axioms explain the target, projects ideals onto measured variables, and checks dimensional consistency.

This project is inspired by the spirit of Emmy Noether’s algebraic approach to invariants and conservation laws, bringing those ideas into computational abductive reasoning.

---

## Features

- **Projection**: Eliminates non-measured variables to obtain reduced Gröbner bases.  
- **Abductive Inference**: Tests subsets of removed axioms to infer candidate axioms explaining the target.  
- **Dimensionality Checks**: Compares ideal dimensions before/after removing axioms to test explanatory power.  
- **Timeout-Safe Parallelism**: Uses `ProcessPoolExecutor` to manage Macaulay2 runs with configurable timeouts.

---

## Installation

### Prerequisites

1. **Python 3.9+** (earlier versions may work but are untested).  
   Recommended: create a virtual environment:

   ```bash
   python3 -m venv venv
   source venv/bin/activate
   ```

2. **Macaulay2** installed and accessible via command line.  
   On macOS with Homebrew:

   ```bash
   brew install macaulay2
   ```

   This project assumes the Macaulay2 binary is located at:

   ```
   /opt/homebrew/bin/M2
   ```

   If your system uses a different path, update the variable `macaulay2_path` in `m2_functions.py`.

3. **Python dependencies**:  
   Install required libraries:

   ```bash
   pip install -r requirements.txt
   ```

   The main dependencies are:
   - `concurrent.futures` (built-in with Python 3)
   - `itertools` (built-in)
   - `re` (built-in)

   No external Python packages are strictly required.

---

## Repository Structure

```
AI-Noether/
│
├── model.py                # Main pipeline
├── m2_functions.py         # Python↔Macaulay2 function wrappers
├── systems_and_phenomena/  # Input systems
│   └── real/
│       └── kepler/
│           └── system.txt  # Example system definition
└── results/                # Auto-generated results will be stored here
```

---

## Input Format

Each problem system is stored in `systems_and_phenomena/<domain>/<problem>/system.txt`.  

Example (`systems_and_phenomena/real/kepler/system.txt`):

```
Variables: ["Fc", "Fg", "w", "m1", "m2", "d1", "d2", "p"]
Equations:
Fg*(d1+d2)^2 - m1*m2
Fc - m2*d2*w^2
Fc - Fg
w*p - 1

Measured Variables: ["m1", "m2", "d1", "d2", "p"]

Target Polynomial:
p^2*m1*m2 - d1^2*d2*m2 - 2*d1*d2^2*m2 - d2^3*m2
```

Sections:
- **Variables**: Full list of symbolic variables.
- **Equations**: Axioms defining the system (one per line).
- **Measured Variables**: Subset of variables considered observable.
- **Target Polynomial**: The consequence to test for abductive explanation.

---

## Usage

1. Place your system files under `systems_and_phenomena/<domain>/<problem>/system.txt`.

2. Edit `model.py` to include your problem names in `problems_list`. Example:

   ```python
   problems_list = [
       'kepler',
       'light_2',
   ]
   ```

3. Run the pipeline:

   ```bash
   python model.py
   ```

4. Results will appear in:

   ```
   results/<domain>/<problem>/
   ```

   Inside, you’ll find:
   - `projection.txt` — Gröbner basis analysis of eliminated variables.
   - `abduction_*.txt` — Subset-based abduction inference logs.
   - `dimensionality_check/` — Dimension analysis for each axiom removal subset.

---

## Example Workflow

Running with the provided **Kepler system**:

```bash
python model.py
```

Produces outputs such as:

- **Projection Analysis**: reduced Gröbner bases for measurable variables.  
- **Abduction Results**: candidate combinations of axioms that explain the target polynomial.  
- **Dimension Checks**: confirmation of when removed axioms plus the target yield the original ideal’s dimension.

---

## Notes

- **Timeouts**: Each abductive inference and dimension check has a configurable timeout (`TIMEOUT_SECONDS = 60`).  
- **Parallelism**: Subset computations are parallelized using `ProcessPoolExecutor`.  
- **Path Adjustments**: If your Macaulay2 binary is not at `/opt/homebrew/bin/M2`, edit `macaulay2_path` in `m2_functions.py`.

---

## License

MIT License. See [LICENSE](LICENSE) for details.
