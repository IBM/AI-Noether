-- AI-Noether: Witness Set Template (Numerical Algebraic Geometry)
-- Computes numerical irreducible decomposition and samples points

needsPackage("NumericalAlgebraicGeometry", Reload => true)
-- Using built-in NAG

-- Work over CC for numerical algebraic geometry
R = CC[f1, f2, Eph1, Eph2, Eel1, Eel2, p1, p2, pel2, lambda1, lambda2, h, mel, c, cosTh, MonomialOrder => Lex];

remainingAxioms = toList([Eph1 + Eel1 - Eph2- Eel2, Eph1 - h*f1, p1*c - h*f1, lambda2*f2 - c, Eel1 - mel*c^2, Eel2^2 - pel2^2*c^2 - mel^2*c^4, pel2^2 - p1^2 - p2^2 + 2*p1*p2*cosTh]);
qList = toList([(9981/10000)*lambda1*mel*c - (10045/10000)*lambda2*mel*c - (9955/10000)*cosTh*h + (10089/10000)*h]);

axiomIdeal = ideal(join(remainingAxioms, qList));

-- Numerical irreducible decomposition
W = numericalIrreducibleDecomposition axiomIdeal;
Ws = components W;

-- Variables in ring order
varList = flatten entries vars R;

-- Target number of points per component
targetCount = 100;

f = openOut "results/compton/abduction/noisy/noise_1e-5/3_axiom(s)_removed/combo_3_5_6/decomposition/witness_sets/witness_set.txt";
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
print("Witness set computation complete. Output written to results/compton/abduction/noisy/noise_1e-5/3_axiom(s)_removed/combo_3_5_6/decomposition/witness_sets/witness_set.txt");
