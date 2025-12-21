# Systems and Phenomena: Input Format

This directory contains problem definitions for AI-Noether. Each problem is defined in its own subdirectory with a `system.txt` file (and optional noisy variants).

## Directory Structure

```
systems_and_phenomena/
├── README.md                     # This file
├── kepler/
│   ├── system.txt                # Noiseless axiom system
│   ├── system_noise_1e-2.txt     # Noisy variant (ε = 1e-2)
│   ├── system_noise_1e-5.txt     # Noisy variant (ε = 1e-5)
│   └── system_noise_1e-8.txt     # Noisy variant (ε = 1e-8)
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
- Coefficients must be integers or rationals in fractional form: `3`, `-1`, `1/2`, `10001/10000`
- **Important**: Decimal coefficients like `0.023` will cause errors in Macaulay2. Use rational form instead: `23/1000`
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

For numerical abduction experiments, create noisy variants by perturbing the coefficients. Noise is typically added to the target polynomial to simulate imprecise measurements of the consequence.

**Naming convention**: `system_noise_<level>.txt`

The file naming is purely conventional—you can name files however you like and specify the exact filename in your `config.yaml` under `numerical.noise_levels`.

Examples:
- `system_noise_1e-2.txt` → noise level ε = 1e-2
- `system_noise_1e-5.txt` → noise level ε = 1e-5
- `system_noise_1e-8.txt` → noise level ε = 1e-8

**Format**: Same as `system.txt`, but with perturbed coefficients expressed as **rational numbers**:

```
Variables: [Fc, Fg, w, m1, d1, m2, d2, p]

Equations:
m1*d1 - m2*d2
Fg*(d1+d2)^2 - m1*m2
Fc - m2*d2*w^2
Fc - Fg
w*p - 1

Measured Variables: [m1, d1, m2, d2, p]

Target Polynomial:
(10000217/10000000)*m1*m2*p^2 - (9999922/10000000)*m1*d1*d2^2 - (9999853/10000000)*m2*d1^2*d2 - (19989624/10000000)*m2*d1*d2^2
```

**Important**: Since AI-Noether interfaces with Macaulay2, all coefficients must be expressed as rational numbers in fractional form. Decimal notation like `1.00234` will cause parsing errors—use `100234/100000` instead.

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
- Avoid single-letter names that are common constants: `e`, `i`
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

### Relativistic Laws (Time Dilation, Mass-Energy, Length Contraction)
```
Variables: [c, dt, v, F0, F, dt0, L0, L, m0, u0, m, u]

Equations:
F0*dt0 - 1
F*dt - 1
c*dt0 - 2*L0
c^2*dt^2 - 4*L0^2 - v^2*dt^2
m0*u0 - m*u
u0*dt0 - u*dt
dt*(c^2 - v^2) - 2*L*c

Measured Variables: [L, L0, v, c, F0, F, m, m0, u0, dt]

Target Polynomial:
c^2*F0^2 - c^2*F^2 - F0^2*v^2
c^2*m0^2*u0 - c^2*u0*m^2 + v^2*u0*m^2
c^2*L0^2 - c^2*L^2 - v^2*L0^2
```

**Interpretation**:
- Variables: speed of light (c), time intervals (dt, dt0), velocity (v), frequencies (F0, F), lengths (L0, L), rest mass (m0), relativistic mass (m), velocities (u0, u)
- Three target polynomials encoding: relativistic Doppler effect, relativistic momentum, and length contraction

## Troubleshooting

### "No equations found"
- Ensure there's a blank line between sections
- Check that "Equations:" header is present (singular or plural works)

### "Variable not in ring"
- All variables in equations must be listed in the Variables section
- Check for typos in variable names

### "Coefficient parsing error" or Macaulay2 errors
- Ensure all coefficients are integers or rationals in fractional form
- Convert decimals to fractions: `0.99987` → `99987/100000`

### "Decomposition timeout"
- Reduce number of variables if possible
- Try using Singular instead of M2 (`decomposition.engine: "singular"`)
- Simplify polynomial degrees

### Bertini crashes with no output
- Check for reserved variable names
- Try renaming problematic variables (especially `E`, `Pi`, `cos*` prefixes)
