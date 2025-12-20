-- AI-Noether: Dimensionality Check Template
-- Compares dimensions of ideals with/without removed axioms

needsPackage("PrimaryDecomposition");

R = QQ[c0, c2, dp, r, Rad, u, L, mu, delP, MonomialOrder => Lex];

allAxioms = {4*r*c2*mu - r*dp, delP + L*dp, c0 + c2*Rad^2, u - c0 - r^2*c2};
targetList = {r^3*delP - r*Rad^2*delP + 4*r*u*L*mu};

-- Original dimension (all axioms)
origIdeal = ideal(allAxioms);
originalDim = dim origIdeal;

-- Compute remaining axioms by removing specified ones
remainingAxioms = allAxioms;
remainingAxioms = delete(4*r*c2*mu - r*dp, remainingAxioms);
remainingAxioms = delete(delP + L*dp, remainingAxioms);
remainingAxioms = delete(u - c0 - r^2*c2, remainingAxioms);

-- Reduced dimension (remaining axioms only)
Ireduced = ideal(remainingAxioms);
reducedDim = dim Ireduced;

-- Discovered dimension (remaining axioms + targets)
remainingWithTargets = join(remainingAxioms, targetList);
Idiscovered = ideal(remainingWithTargets);
discoveredDim = dim Idiscovered;

-- Output
f = openOut "results/hagen/dimensionality_check/3_axioms_removed/subset_2/dimensionality_output.txt";
f << "=== Dimension Analysis ===" << endl;
f << "Original dimension: " << originalDim << endl;
f << "Reduced dimension: " << reducedDim << endl;
f << "Discovered dimension: " << discoveredDim << endl;
f << "Removed axioms: " << toString({4*r*c2*mu - r*dp, delP + L*dp, u - c0 - r^2*c2}) << endl;
f << "Remaining axioms: " << toString(remainingAxioms) << endl;
f << "Targets: " << toString(targetList) << endl;
f << "Original == Discovered: " << toString(originalDim == discoveredDim) << endl;
close f;
