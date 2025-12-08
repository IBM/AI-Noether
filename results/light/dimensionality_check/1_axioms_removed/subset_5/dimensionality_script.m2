-- AI-Noether: Dimensionality Check Template
-- Compares dimensions of ideals with/without removed axioms

needsPackage("PrimaryDecomposition");

R = QQ[S, ap, sintheta, dA, dtheta, r, P, qc, x0, w, MonomialOrder => Lex];

allAxioms = {S * r^2 - qc^2 * ap^2 * sintheta^2, 100*dA - 2*(314)*(r^2)*sintheta*dtheta, P - S * dA, 4 - 3*sintheta^3 * dtheta, 2*ap^2 - w^4 * x0^2};
targetList = {75*P - 314*qc^2*w^4*x0^2};

-- Original dimension (all axioms)
origIdeal = ideal(allAxioms);
originalDim = dim origIdeal;

-- Compute remaining axioms by removing specified ones
remainingAxioms = allAxioms;
remainingAxioms = delete(2*ap^2 - w^4 * x0^2, remainingAxioms);

-- Reduced dimension (remaining axioms only)
Ireduced = ideal(remainingAxioms);
reducedDim = dim Ireduced;

-- Discovered dimension (remaining axioms + targets)
remainingWithTargets = join(remainingAxioms, targetList);
Idiscovered = ideal(remainingWithTargets);
discoveredDim = dim Idiscovered;

-- Output
f = openOut "results/light/dimensionality_check/1_axioms_removed/subset_5/dimensionality_output.txt";
f << "=== Dimension Analysis ===" << endl;
f << "Original dimension: " << originalDim << endl;
f << "Reduced dimension: " << reducedDim << endl;
f << "Discovered dimension: " << discoveredDim << endl;
f << "Removed axioms: " << toString({2*ap^2 - w^4 * x0^2}) << endl;
f << "Remaining axioms: " << toString(remainingAxioms) << endl;
f << "Targets: " << toString(targetList) << endl;
f << "Original == Discovered: " << toString(originalDim == discoveredDim) << endl;
close f;
