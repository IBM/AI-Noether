-- AI-Noether: Dimensionality Check Template
-- Compares dimensions of ideals with/without removed axioms

needsPackage("PrimaryDecomposition");

R = QQ[Eki, Ekf, Ugi, Ugf, G, M, m, ve, r, MonomialOrder => Lex];

allAxioms = {Eki - 1/2 * m * ve^2, Ekf - 0, Ugi * r + G * M * m, Ugf - 0, Eki + Ugi - Ekf - Ugf};
targetList = {2*G*M*m - m*ve^2*r};

-- Original dimension (all axioms)
origIdeal = ideal(allAxioms);
originalDim = dim origIdeal;

-- Compute remaining axioms by removing specified ones
remainingAxioms = allAxioms;
remainingAxioms = delete(Ekf - 0, remainingAxioms);
remainingAxioms = delete(Ugi * r + G * M * m, remainingAxioms);
remainingAxioms = delete(Eki + Ugi - Ekf - Ugf, remainingAxioms);

-- Reduced dimension (remaining axioms only)
Ireduced = ideal(remainingAxioms);
reducedDim = dim Ireduced;

-- Discovered dimension (remaining axioms + targets)
remainingWithTargets = join(remainingAxioms, targetList);
Idiscovered = ideal(remainingWithTargets);
discoveredDim = dim Idiscovered;

-- Output
f = openOut "results/escape_velocity/dimensionality_check/3_axioms_removed/subset_8/dimensionality_output.txt";
f << "=== Dimension Analysis ===" << endl;
f << "Original dimension: " << originalDim << endl;
f << "Reduced dimension: " << reducedDim << endl;
f << "Discovered dimension: " << discoveredDim << endl;
f << "Removed axioms: " << toString({Ekf - 0, Ugi * r + G * M * m, Eki + Ugi - Ekf - Ugf}) << endl;
f << "Remaining axioms: " << toString(remainingAxioms) << endl;
f << "Targets: " << toString(targetList) << endl;
f << "Original == Discovered: " << toString(originalDim == discoveredDim) << endl;
close f;
