-- AI-Noether: Dimensionality Check Template
-- Compares dimensions of ideals with/without removed axioms

needsPackage("PrimaryDecomposition");

R = QQ[Fc, Fg, w, m1, d1, m2, d2, p, MonomialOrder => Lex];

allAxioms = {m1*d1-m2*d2, Fg*(d1+d2)^2 - m1*m2, Fc - m2*d2*w^2, Fc - Fg, w*p - 1};
targetList = {m1*m2*p^2-m1*d1*d2^2-m2*d1^2*d2-2*m2*d1*d2^2};

-- Original dimension (all axioms)
I = ideal(allAxioms);
originalDim = dim I;

-- Compute remaining axioms by removing specified ones
remainingAxioms = allAxioms;
remainingAxioms = delete(Fg*(d1+d2)^2 - m1*m2, remainingAxioms);

-- Reduced dimension (remaining axioms only)
Ireduced = ideal(remainingAxioms);
reducedDim = dim Ireduced;

-- Discovered dimension (remaining axioms + targets)
remainingWithTargets = join(remainingAxioms, targetList);
Idiscovered = ideal(remainingWithTargets);
discoveredDim = dim Idiscovered;

-- Output
f = openOut "results/real/kepler/dimensionality_check/1_axioms_removed/subset_2/dimensionality_output.txt";
f << "=== Dimension Analysis ===" << endl;
f << "Original dimension: " << originalDim << endl;
f << "Reduced dimension: " << reducedDim << endl;
f << "Discovered dimension: " << discoveredDim << endl;
f << "Removed axioms: " << toString({Fg*(d1+d2)^2 - m1*m2}) << endl;
f << "Remaining axioms: " << toString(remainingAxioms) << endl;
f << "Targets: " << toString(targetList) << endl;
f << "Original == Discovered: " << toString(originalDim == discoveredDim) << endl;
close f;
