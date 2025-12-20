-- AI-Noether: Dimensionality Check Template
-- Compares dimensions of ideals with/without removed axioms

needsPackage("PrimaryDecomposition");

R = QQ[c, dt, v, F0, F, dt0, L0, L, m0, u0, m, u, MonomialOrder => Lex];

allAxioms = {F0*dt0 - 1, F*dt - 1, c*dt0 - 2*L0, c^2*dt^2 - 4*L0^2 - v^2*dt^2, m0*u0 - m*u, u0*dt0 - u*dt, dt*(c^2 - v^2) - 2*L*c};
targetList = {c^2*F0^2-c^2*F^2-F0^2*v^2, c^2*m0^2*u0-c^2*u0*m^2+v^2*u0*m^2, c^2*L0^2-c^2*L^2-v^2*L0^2};

-- Original dimension (all axioms)
origIdeal = ideal(allAxioms);
originalDim = dim origIdeal;

-- Compute remaining axioms by removing specified ones
remainingAxioms = allAxioms;
remainingAxioms = delete(F*dt - 1, remainingAxioms);
remainingAxioms = delete(dt*(c^2 - v^2) - 2*L*c, remainingAxioms);

-- Reduced dimension (remaining axioms only)
Ireduced = ideal(remainingAxioms);
reducedDim = dim Ireduced;

-- Discovered dimension (remaining axioms + targets)
remainingWithTargets = join(remainingAxioms, targetList);
Idiscovered = ideal(remainingWithTargets);
discoveredDim = dim Idiscovered;

-- Output
f = openOut "results/relativistic_laws_updated/dimensionality_check/2_axioms_removed/subset_11/dimensionality_output.txt";
f << "=== Dimension Analysis ===" << endl;
f << "Original dimension: " << originalDim << endl;
f << "Reduced dimension: " << reducedDim << endl;
f << "Discovered dimension: " << discoveredDim << endl;
f << "Removed axioms: " << toString({F*dt - 1, dt*(c^2 - v^2) - 2*L*c}) << endl;
f << "Remaining axioms: " << toString(remainingAxioms) << endl;
f << "Targets: " << toString(targetList) << endl;
f << "Original == Discovered: " << toString(originalDim == discoveredDim) << endl;
close f;
