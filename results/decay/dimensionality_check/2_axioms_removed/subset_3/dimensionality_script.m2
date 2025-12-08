-- AI-Noether: Dimensionality Check Template
-- Compares dimensions of ideals with/without removed axioms

needsPackage("PrimaryDecomposition");

R = QQ[pp, pmu, Ev, Emu, Ep, pv, mp, mmu, MonomialOrder => Lex];

allAxioms = {pv - pmu, Ep - mp, Ev - pv, Ep - Emu - Ev, Emu^2 - pmu^2 - mmu^2};
targetList = {2*pv*mp - mp^2 + mmu^2};

-- Original dimension (all axioms)
I = ideal(allAxioms);
originalDim = dim I;

-- Compute remaining axioms by removing specified ones
remainingAxioms = allAxioms;
remainingAxioms = delete(pv - pmu, remainingAxioms);
remainingAxioms = delete(Ep - Emu - Ev, remainingAxioms);

-- Reduced dimension (remaining axioms only)
Ireduced = ideal(remainingAxioms);
reducedDim = dim Ireduced;

-- Discovered dimension (remaining axioms + targets)
remainingWithTargets = join(remainingAxioms, targetList);
Idiscovered = ideal(remainingWithTargets);
discoveredDim = dim Idiscovered;

-- Output
f = openOut "results/decay/dimensionality_check/2_axioms_removed/subset_3/dimensionality_output.txt";
f << "=== Dimension Analysis ===" << endl;
f << "Original dimension: " << originalDim << endl;
f << "Reduced dimension: " << reducedDim << endl;
f << "Discovered dimension: " << discoveredDim << endl;
f << "Removed axioms: " << toString({pv - pmu, Ep - Emu - Ev}) << endl;
f << "Remaining axioms: " << toString(remainingAxioms) << endl;
f << "Targets: " << toString(targetList) << endl;
f << "Original == Discovered: " << toString(originalDim == discoveredDim) << endl;
close f;
