-- AI-Noether: Dimensionality Check Template
-- Compares dimensions of ideals with/without removed axioms

needsPackage("PrimaryDecomposition");

R = QQ[mr, vm, vc, pc, Em, Er, Ec, mc, mm, pm, c, MonomialOrder => Lex];

allAxioms = {pm^2*(c^2 - vm^2) - mm^2*vm^2*c^2, Em^2 - (mm*c^2)^2 - (pm*c)^2, Er - mr*c^2, Ec^2 - (mc*c)^2 - (pc*c)^2, 2*Em*Er - Ec^2 + Em^2 + Er^2, pc - pm, vm - 4/5*c, mr - mm, pc^2*(c^2 - vc^2) - mc^2*vc^2*c^2};
targetList = {16*mm^2*c^4 - 9*pm^2*c^2};

-- Original dimension (all axioms)
I = ideal(allAxioms);
originalDim = dim I;

-- Compute remaining axioms by removing specified ones
remainingAxioms = allAxioms;
remainingAxioms = delete(Em^2 - (mm*c^2)^2 - (pm*c)^2, remainingAxioms);
remainingAxioms = delete(vm - 4/5*c, remainingAxioms);

-- Reduced dimension (remaining axioms only)
Ireduced = ideal(remainingAxioms);
reducedDim = dim Ireduced;

-- Discovered dimension (remaining axioms + targets)
remainingWithTargets = join(remainingAxioms, targetList);
Idiscovered = ideal(remainingWithTargets);
discoveredDim = dim Idiscovered;

-- Output
f = openOut "results/inelastic_collision/dimensionality_check/2_axioms_removed/subset_13/dimensionality_output.txt";
f << "=== Dimension Analysis ===" << endl;
f << "Original dimension: " << originalDim << endl;
f << "Reduced dimension: " << reducedDim << endl;
f << "Discovered dimension: " << discoveredDim << endl;
f << "Removed axioms: " << toString({Em^2 - (mm*c^2)^2 - (pm*c)^2, vm - 4/5*c}) << endl;
f << "Remaining axioms: " << toString(remainingAxioms) << endl;
f << "Targets: " << toString(targetList) << endl;
f << "Original == Discovered: " << toString(originalDim == discoveredDim) << endl;
close f;
