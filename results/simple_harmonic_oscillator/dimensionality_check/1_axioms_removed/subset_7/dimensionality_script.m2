-- AI-Noether: Dimensionality Check Template
-- Compares dimensions of ideals with/without removed axioms

needsPackage("PrimaryDecomposition");

R = QQ[F, ad, T, Fd, omega, theta, sintheta, m, d, g, L, j, Pi, Tj, MonomialOrder => Lex];

allAxioms = {ad-g*sintheta, Fd - m*ad, d-L*theta, T*omega-2*Pi, d*omega^2-ad, Tj-j*T, sintheta - theta};
targetList = {d*g*Tj^2-4*d*L*j^2*Pi^2};

-- Original dimension (all axioms)
origIdeal = ideal(allAxioms);
originalDim = dim origIdeal;

-- Compute remaining axioms by removing specified ones
remainingAxioms = allAxioms;
remainingAxioms = delete(sintheta - theta, remainingAxioms);

-- Reduced dimension (remaining axioms only)
Ireduced = ideal(remainingAxioms);
reducedDim = dim Ireduced;

-- Discovered dimension (remaining axioms + targets)
remainingWithTargets = join(remainingAxioms, targetList);
Idiscovered = ideal(remainingWithTargets);
discoveredDim = dim Idiscovered;

-- Output
f = openOut "results/pendulum/dimensionality_check/1_axioms_removed/subset_7/dimensionality_output.txt";
f << "=== Dimension Analysis ===" << endl;
f << "Original dimension: " << originalDim << endl;
f << "Reduced dimension: " << reducedDim << endl;
f << "Discovered dimension: " << discoveredDim << endl;
f << "Removed axioms: " << toString({sintheta - theta}) << endl;
f << "Remaining axioms: " << toString(remainingAxioms) << endl;
f << "Targets: " << toString(targetList) << endl;
f << "Original == Discovered: " << toString(originalDim == discoveredDim) << endl;
close f;
