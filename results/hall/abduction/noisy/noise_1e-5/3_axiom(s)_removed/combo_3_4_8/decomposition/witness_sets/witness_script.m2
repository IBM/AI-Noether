-- AI-Noether: Witness Set Template (Numerical Algebraic Geometry)
-- Computes numerical irreducible decomposition and samples points

needsPackage("NumericalAlgebraicGeometry", Reload => true)
needsPackage("Bertini", Reload => true, Configuration => {"BERTINIexecutable" => "/Users/ksrivastava/opt/bertini-1.7-openmpi/BertiniApple_OpenMPI_v1.7/bertini"})

-- Work over CC for numerical algebraic geometry
R = CC[Fm, d, v, Fe, E, dt, Q, N, V, i, n, qe, B, h, L, UH, MonomialOrder => Lex];

remainingAxioms = toList([Fm - qe*v*B, Fe - qe*E, v*dt - L, i*dt - Q, Q - N*qe, V - L*h*d]);
qList = toList([(9978/10000)*N*qe*UH - (10032/10000)*i*B*h*L]);

axiomIdeal = ideal(join(remainingAxioms, qList));

-- Numerical irreducible decomposition
W = bertiniPosDimSolve axiomIdeal;
Ws = components W;

-- Variables in ring order
varList = flatten entries vars R;

-- Target number of points per component
targetCount = 100;

f = openOut "results/hall/abduction/noisy/noise_1e-5/3_axiom(s)_removed/combo_3_4_8/decomposition/witness_sets/witness_set.txt";
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
print("Witness set computation complete. Output written to results/hall/abduction/noisy/noise_1e-5/3_axiom(s)_removed/combo_3_4_8/decomposition/witness_sets/witness_set.txt");
