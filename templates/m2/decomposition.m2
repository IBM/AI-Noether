-- AI-Noether: Primary Decomposition Template (Noiseless)
-- Computes primary decomposition of ideal(remaining_axioms + targets)
-- Outputs generators of each component for reasoning step

needsPackage("PrimaryDecomposition", Reload => true)

-- Ring definition
R = QQ[{variables}, MonomialOrder => Lex];
print("Ring defined: " | toString R);

-- Input data
remainingAxioms = toList([{remaining_axioms}]);
qList = toList([{targets}]);

print("Remaining axioms: " | toString remainingAxioms);
print("Targets: " | toString qList);

-- Form ideal with remaining axioms and all targets
axiomIdeal = ideal(join(remainingAxioms, qList));
print("Ideal defined: " | toString axiomIdeal);

-- Compute primary decomposition
PD = primaryDecomposition axiomIdeal;
print("Primary decomposition computed with " | toString(#PD) | " components");

-- Output file
f = openOut "{output_file}";
f << "=== Primary Decomposition Results ===" << endl;
f << "Remaining Axioms:" << endl;
scan(remainingAxioms, a -> f << "  " << toString a << endl);
f << endl;
f << "Targets:" << endl;
scan(qList, q -> f << "  " << toString q << endl);
f << endl;
f << "Number of components: " << toString(#PD) << endl;
f << endl;

-- Extract generators from each component
f << "=== Component Generators ===" << endl;
componentIndex = 0;
scan(PD, J -> (
    componentIndex = componentIndex + 1;
    f << "COMPONENT_" << toString componentIndex << ":" << endl;
    idealGens = flatten entries gens J;
    idealGensList = toList idealGens;
    f << "  num_generators: " << toString(#idealGensList) << endl;
    scan(idealGensList, g -> (
        f << "  GEN: " << toString g << endl;
    ));
    f << endl;
));

f << "=== END ===" << endl;
close f;

print("Decomposition complete. Output written to {output_file}");
