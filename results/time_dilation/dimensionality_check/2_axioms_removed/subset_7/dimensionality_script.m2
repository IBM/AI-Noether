-- AI-Noether: Dimensionality Check Template
-- Compares dimensions of ideals with/without removed axioms

needsPackage("PrimaryDecomposition");

R = QQ[d, dt, dt0, L, c, F0, F, v, MonomialOrder => Lex];

allAxioms = {c*dt0 - 2*d, 4*L^2 - 4*d^2 - v^2*dt^2, F0*dt0 - 1, F*dt - 1, c*dt - 2*L};
targetList = {c^2*F0^2-c^2*F^2-F0^2*v^2};

-- Original dimension (all axioms)
origIdeal = ideal(allAxioms);
originalDim = dim origIdeal;

-- Compute remaining axioms by removing specified ones
remainingAxioms = allAxioms;
remainingAxioms = delete(4*L^2 - 4*d^2 - v^2*dt^2, remainingAxioms);
remainingAxioms = delete(c*dt - 2*L, remainingAxioms);

-- Reduced dimension (remaining axioms only)
Ireduced = ideal(remainingAxioms);
reducedDim = dim Ireduced;

-- Discovered dimension (remaining axioms + targets)
remainingWithTargets = join(remainingAxioms, targetList);
Idiscovered = ideal(remainingWithTargets);
discoveredDim = dim Idiscovered;

-- Output
f = openOut "results/time_dilation/dimensionality_check/2_axioms_removed/subset_7/dimensionality_output.txt";
f << "=== Dimension Analysis ===" << endl;
f << "Original dimension: " << originalDim << endl;
f << "Reduced dimension: " << reducedDim << endl;
f << "Discovered dimension: " << discoveredDim << endl;
f << "Removed axioms: " << toString({4*L^2 - 4*d^2 - v^2*dt^2, c*dt - 2*L}) << endl;
f << "Remaining axioms: " << toString(remainingAxioms) << endl;
f << "Targets: " << toString(targetList) << endl;
f << "Original == Discovered: " << toString(originalDim == discoveredDim) << endl;
close f;
