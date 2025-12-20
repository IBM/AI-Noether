# Systems and Phenomena: Input Format

This directory contains problem definitions for AI-Noether. Each problem is defined in its own subdirectory with a `system.txt` file (and optional noisy variants).

## Directory Structure

```
systems_and_phenomena/
├── README.md                     # This file
├── kepler/
│   ├── system.txt                # Noiseless axiom system
│   ├── system_noise_1e-2.txt     # Noisy variant (σ = 0.01)
│   ├── system_noise_1e-5.txt     # Noisy variant (σ = 0.00001)
│   └── system_noise_1e-8.txt     # Noisy variant (σ = 1e-8)
├── time_dilation/
│   └── system.txt
├── pendulum/
│   └── system.txt
└── ...
```

## Input File Format

Each `system.txt` file must contain four sections:

### 1. Variables

A comma-separated list of all variable names in the polynomial ring:

```
Variables: [T, a, G, M, r, v, Pi]
```

**Important**: Variable names must be valid polynomial ring identifiers:
- Alphanumeric characters and underscores only
- Cannot start with a number
- Avoid reserved names (see below)

### 2. Equations (Axioms)

One polynomial equation per line. Each equation is implicitly set equal to zero:

```
Equations:
T^2*v^3 - 4*Pi^2*a^3
a - r
v^2*r - G*M
T*v - 2*Pi*r
```

**Polynomial syntax**:
- Use `*` for multiplication: `2*x*y` not `2xy`
- Use `^` for exponents: `x^2` not `x**2`
- Coefficients can be integers or rationals: `3`, `-1`, `1/2`
- Each line is one polynomial = 0

### 3. Measured Variables

Variables that can be directly observed/measured. These are NOT eliminated during projection:

```
Measured Variables: [T, a, G, M, Pi]
```

Non-measured variables are computed as: `Variables - Measured Variables`

### 4. Target Polynomial

The consequence(s) to be derived from the axioms. Can be multi-line for multiple targets:

```
Target Polynomial:
T^2*G*M - 4*Pi^2*a^3
```

## Complete Example: Kepler's Third Law

```
Variables: [T, a, G, M, r, v, Pi]

Equations:
T^2*v^3 - 4*Pi^2*a^3
a - r
v^2*r - G*M
T*v - 2*Pi*r

Measured Variables: [T, a, G, M, Pi]

Target Polynomial:
T^2*G*M - 4*Pi^2*a^3
```

**Interpretation**:
- Variables: orbital period (T), semi-major axis (a), gravitational constant (G), mass (M), radius (r), velocity (v), π (Pi)
- Axioms encode: Kepler's law, r=a for circular orbit, centripetal force = gravity, circumference relation
- Target: Kepler's third law T² ∝ a³

## Noisy Input Files

For numerical abduction experiments, create noisy variants by perturbing the coefficients:

**Naming convention**: `system_noise_<level>.txt`

Examples:
- `system_noise_1e-2.txt` → 1% relative noise (σ = 0.01)
- `system_noise_1e-5.txt` → 0.001% relative noise
- `system_noise_1e-8.txt` → essentially exact

**Format**: Same as `system.txt`, but with perturbed coefficients:

```
Variables: [T, a, G, M, r, v, Pi]

Equations:
1.00234*T^2*v^3 - 3.99876*Pi^2*a^3
0.99987*a - 1.00012*r
1.00045*v^2*r - 0.99956*G*M
0.99989*T*v - 2.00023*Pi*r

Measured Variables: [T, a, G, M, Pi]

Target Polynomial:
T^2*G*M - 4*Pi^2*a^3
```

The numerical abduction pipeline will attempt to recover the true (integer) coefficients from the noisy measurements.

## Reserved Variable Names

Avoid these names as they conflict with external tools:

### Bertini Reserved Names
| Avoid | Use Instead | Reason |
|-------|-------------|--------|
| `Pi`, `pi` | `Piconst`, `PI` | π constant |
| `E`, `e` | `En`, `Eph` | Euler's number |
| `E1`, `E2` | `Eph1`, `Eph2` | Scientific notation |
| `I`, `i` | `Ivar`, `cur` | Imaginary unit |
| `cosTh` | `cth` | `cos` function prefix |
| `sinTh` | `sth` | `sin` function prefix |
| `exp...` | `ex...` | `exp` function prefix |

### General Best Practices
- Use descriptive but short names: `omega` → `w`, `theta` → `th`
- Avoid single-letter names that are common constants: `e`, `i`, `c`
- When in doubt, use longer unique names: `mass_electron` → `mel`

## Example Problems

### Simple Harmonic Pendulum
```
Variables: [ad, T, omega, theta, sintheta, d, g, L, j, Piconst, Tj]

Equations:
ad - g*sintheta
d - L*theta
T*omega - 2*Piconst
d*omega^2 - ad
Tj - j*T
sintheta - theta

Measured Variables: [L, g, T, Piconst, j, Tj]

Target Polynomial:
d*g*Tj^2 - 4*d*L*j^2*Piconst^2
```

### Time Dilation
```
Variables: [dt, dt0, L, d, v, c, L0, L1]

Equations:
2*L1 - L
L^2 + 2*d^2
dt*c - 2*L
dt0*c - 2*d
L0 - d
c^2 - v^2

Measured Variables: [dt, dt0, v, c]

Target Polynomial:
dt^2*c^2 - dt^2*v^2 - dt0^2*c^2
```

## Troubleshooting

### "No equations found"
- Ensure there's a blank line between sections
- Check that "Equations:" header is present (singular or plural works)

### "Variable not in ring"
- All variables in equations must be listed in the Variables section
- Check for typos in variable names

### "Decomposition timeout"
- Reduce number of variables if possible
- Try using Singular instead of M2 (`decomposition.engine: "singular"`)
- Simplify polynomial degrees

### Bertini crashes with no output
- Check for reserved variable names
- Try renaming problematic variables (especially `E`, `Pi`, `cos*` prefixes)
