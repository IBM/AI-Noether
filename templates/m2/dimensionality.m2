-- AI-Noether: Dimensionality Check Template
-- Compares dimensions of ideals with/without removed axioms

needsPackage("PrimaryDecomposition");

R = QQ[{variables}, MonomialOrder => Lex];

allAxioms = {{all_axioms}};
targetList = {{targets}};

-- Original dimension (all axioms)
origIdeal = ideal(allAxioms);
originalDim = dim origIdeal;

-- Compute remaining axioms by removing specified ones
remainingAxioms = allAxioms;
{remove_axioms_code}

-- Reduced dimension (remaining axioms only)
Ireduced = ideal(remainingAxioms);
reducedDim = dim Ireduced;

-- Discovered dimension (remaining axioms + targets)
remainingWithTargets = join(remainingAxioms, targetList);
Idiscovered = ideal(remainingWithTargets);
discoveredDim = dim Idiscovered;

-- Output
f = openOut "{output_file}";
f << "=== Dimension Analysis ===" << endl;
f << "Original dimension: " << originalDim << endl;
f << "Reduced dimension: " << reducedDim << endl;
f << "Discovered dimension: " << discoveredDim << endl;
f << "Removed axioms: " << toString({{removed_axioms_list}}) << endl;
f << "Remaining axioms: " << toString(remainingAxioms) << endl;
f << "Targets: " << toString(targetList) << endl;
f << "Original == Discovered: " << toString(originalDim == discoveredDim) << endl;
close f;
