-- AI-Noether: Witness Set Template (Numerical Algebraic Geometry)
-- Computes numerical irreducible decomposition and samples points

needsPackage("NumericalAlgebraicGeometry", Reload => true)
needsPackage("Bertini", Reload => true, Configuration => {"BERTINIexecutable" => "/Users/ksrivastava/opt/bertini-1.7-openmpi/BertiniApple_OpenMPI_v1.7/bertini"})

-- Work over CC for numerical algebraic geometry
R = CC[pp, pmu, Ev, Emu, Ep, pv, mp, mmu, MonomialOrder => Lex];

remainingAxioms = toList([pv - pmu, Emu^2 - pmu^2 - mmu^2]);
qList = toList([(201/100)*pv*mp - (98/100)*mp^2 + (99/100)*mmu^2]);

axiomIdeal = ideal(join(remainingAxioms, qList));

-- Numerical irreducible decomposition
W = bertiniPosDimSolve axiomIdeal;
Ws = components W;

-- Variables in ring order
varList = flatten entries vars R;

-- Target number of points per component
targetCount = 100;

f = openOut "results/decay/abduction/noisy/noise_1e-2/3_axiom(s)_removed/combo_2_3_4/decomposition/witness_sets/witness_set.txt";
f << "variable ordering: ";
for i from 0 to #varList - 1 do (
    f << toString(varList#i);
    if i < #varList - 1 then f << ", ";
);
f << endl << endl;

for i from 0 to #Ws - 1 do (
    Wi = Ws#i;
    f << "component_" << toString(i+1) << ":" << endl;

    -- Equations
    f << "equations:" << endl;
    eqsList = equations Wi;
    scan(eqsList, e -> f << toString e << endl);

    -- Collect witness points (if available)
    ptsList = {{}};
    try (
        pts0 = points Wi;
        ptsList = toList pts0;
    ) else (
        ptsList = {{}};
    );

    -- Top up to targetCount by sampling additional points on Wi
    added = 0;
    attempts = 0;
    maxAttempts = 5 * targetCount;
    while (#ptsList < targetCount and attempts < maxAttempts) do (
        attempts = attempts + 1;
        try (
            p = sample Wi;
            ptsList = append(ptsList, p);
            added = added + 1;
        ) else (
            1;
        );
    );

    -- Points as CSV of coordinates
    f << "points:" << endl;
    scan(ptsList, P -> (
        C = coordinates P;
        for j from 0 to #C - 1 do (
            f << toString(C#j);
            if j < #C - 1 then f << ", ";
        );
        f << endl;
    ));
    f << endl;
);

close f;
print("Witness set computation complete. Output written to results/decay/abduction/noisy/noise_1e-2/3_axiom(s)_removed/combo_2_3_4/decomposition/witness_sets/witness_set.txt");
