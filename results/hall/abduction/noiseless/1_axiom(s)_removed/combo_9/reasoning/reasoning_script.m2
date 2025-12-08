-- AI-Noether: Reasoning Template (Noiseless)
-- Tests if candidate axiom sets, when added to remaining axioms, prove targets

needsPackage("PrimaryDecomposition", Reload => true)

-- Ring definition
R = QQ[Fm, d, v, Fe, E, dt, Q, N, V, i, n, qe, B, h, L, UH, MonomialOrder => Lex];

-- Input data
remainingAxioms = toList([Fm - qe*v*B, Fe - qe*E, Fm - Fe, E*h - UH, v*dt - L, i*dt - Q, Q - N*qe, n*V - N]);
qList = toList([N*qe*UH - i*B*h*L]);
k = #qList;

-- Per-target variable partitions
measuredPerTarget = {{UH, h, L, i, B, N, qe}};
nonMeasuredPerTarget = {{Fm, d, v, Fe, E, dt, Q, V, n}};

-- Candidate axiom sets to test (list of lists)
candidateSets = {{}, {-V*n*qe+dt*i}, {v*B-E}, {-E*h+UH}, {-v*dt+L}, {-V*n+N}, {-dt*i+Q}, {-E*qe+Fe}, {-v*qe*B+Fm}, {-V*n*qe+dt*i, v*B-E}, {-V*n*qe+dt*i, -E*h+UH}, {-V*n*qe+dt*i, -v*dt+L}, {-V*n*qe+dt*i, -V*n+N}, {-V*n*qe+dt*i, -dt*i+Q}, {-V*n*qe+dt*i, -E*qe+Fe}, {-V*n*qe+dt*i, -v*qe*B+Fm}, {v*B-E, -E*h+UH}, {v*B-E, -v*dt+L}, {v*B-E, -V*n+N}, {v*B-E, -dt*i+Q}, {v*B-E, -E*qe+Fe}, {v*B-E, -v*qe*B+Fm}, {-E*h+UH, -v*dt+L}, {-E*h+UH, -V*n+N}, {-E*h+UH, -dt*i+Q}, {-E*h+UH, -E*qe+Fe}, {-E*h+UH, -v*qe*B+Fm}, {-v*dt+L, -V*n+N}, {-v*dt+L, -dt*i+Q}, {-v*dt+L, -E*qe+Fe}, {-v*dt+L, -v*qe*B+Fm}, {-V*n+N, -dt*i+Q}, {-V*n+N, -E*qe+Fe}, {-V*n+N, -v*qe*B+Fm}, {-dt*i+Q, -E*qe+Fe}, {-dt*i+Q, -v*qe*B+Fm}, {-E*qe+Fe, -v*qe*B+Fm}, {-E*h+UH}, {-v*dt+L}, {qe}, {i}, {-V*n+N}, {-dt*i+Q}, {-E*qe+Fe}, {-v*qe*B+Fm}, {-E*h+UH, -v*dt+L}, {-E*h+UH, qe}, {-E*h+UH, i}, {-E*h+UH, -V*n+N}, {-E*h+UH, -dt*i+Q}, {-E*h+UH, -E*qe+Fe}, {-E*h+UH, -v*qe*B+Fm}, {-v*dt+L, qe}, {-v*dt+L, i}, {-v*dt+L, -V*n+N}, {-v*dt+L, -dt*i+Q}, {-v*dt+L, -E*qe+Fe}, {-v*dt+L, -v*qe*B+Fm}, {qe, i}, {qe, -V*n+N}, {qe, -dt*i+Q}, {qe, -E*qe+Fe}, {qe, -v*qe*B+Fm}, {i, -V*n+N}, {i, -dt*i+Q}, {i, -E*qe+Fe}, {i, -v*qe*B+Fm}, {-V*n+N, -dt*i+Q}, {-V*n+N, -E*qe+Fe}, {-V*n+N, -v*qe*B+Fm}, {-dt*i+Q, -E*qe+Fe}, {-dt*i+Q, -v*qe*B+Fm}, {-E*qe+Fe, -v*qe*B+Fm}, {-E*h+UH}, {-v*dt+L}, {qe}, {-V*n+N}, {-dt*i+Q}, {dt}, {-E*qe+Fe}, {-v*qe*B+Fm}, {-E*h+UH, -v*dt+L}, {-E*h+UH, qe}, {-E*h+UH, -V*n+N}, {-E*h+UH, -dt*i+Q}, {-E*h+UH, dt}, {-E*h+UH, -E*qe+Fe}, {-E*h+UH, -v*qe*B+Fm}, {-v*dt+L, qe}, {-v*dt+L, -V*n+N}, {-v*dt+L, -dt*i+Q}, {-v*dt+L, dt}, {-v*dt+L, -E*qe+Fe}, {-v*dt+L, -v*qe*B+Fm}, {qe, -V*n+N}, {qe, -dt*i+Q}, {qe, dt}, {qe, -E*qe+Fe}, {qe, -v*qe*B+Fm}, {-V*n+N, -dt*i+Q}, {-V*n+N, dt}, {-V*n+N, -E*qe+Fe}, {-V*n+N, -v*qe*B+Fm}, {-dt*i+Q, dt}, {-dt*i+Q, -E*qe+Fe}, {-dt*i+Q, -v*qe*B+Fm}, {dt, -E*qe+Fe}, {dt, -v*qe*B+Fm}, {-E*qe+Fe, -v*qe*B+Fm}};

-- Configuration
requireLiteralGB = true;

-- Helper functions
isInIdeal = (poly, base) -> (
    if #base == 0 then return false;
    M = ideal(base);
    G = gens gb M;
    poly % ideal(G) == 0
);

-- Check if target i is in eliminated ideal for given combo
inEliminatedIdealIdx = (i, combo) -> (
    M = ideal(join(remainingAxioms, combo));
    eliminatedIdeal = eliminate(nonMeasuredPerTarget#i, M);
    GBproj = gens gb eliminatedIdeal;
    (qList#i) % ideal(GBproj) == 0
);

-- Check if target i appears literally in eliminated GB
appearsInGBExactlyIdx = (i, combo) -> (
    M = ideal(join(remainingAxioms, combo));
    eliminatedIdeal = eliminate(nonMeasuredPerTarget#i, M);
    GBproj = gens gb eliminatedIdeal;
    member(true, toList apply(flatten entries GBproj, g -> g == (qList#i)))
);

-- Check all targets for membership
allInEliminatedIdealPT = (combo) ->
    all(toList(0..(k-1)), i -> inEliminatedIdealIdx(i, combo));

-- Check all targets for literal appearance
allAppearInGBExactlyPT = (combo) ->
    all(toList(0..(k-1)), i -> appearsInGBExactlyIdx(i, combo));

-- Output file
f = openOut "results/hall/abduction/noiseless/1_axiom(s)_removed/combo_9/reasoning/reasoning_output.txt";
f << "=== Reasoning Results ===" << endl;
f << "Remaining Axioms:" << endl;
scan(remainingAxioms, a -> f << "  " << toString a << endl);
f << endl;
f << "Targets:" << endl;
scan(qList, q -> f << "  " << toString q << endl);
f << endl;
f << "Require literal GB appearance: " << toString requireLiteralGB << endl;
f << "Number of candidate sets to test: " << toString(#candidateSets) << endl;
f << endl;

-- Track saved combos and strong candidates (start with empty lists)
savedCombos = {};
strongCandidates = {};

-- Test each candidate set
f << "=== Testing Candidate Sets ===" << endl;
scan(candidateSets, combo -> (
    f << "CANDIDATE_SET: " << toString combo << endl;
    
    -- Filter out polynomials already implied by remaining axioms
    filteredCombo = select(combo, p -> not isInIdeal(p, remainingAxioms));
    f << "  filtered: " << toString filteredCombo << endl;
    
    if #filteredCombo == 0 then (
        if #combo == 0 then (
            -- Empty combo: test if remaining axioms alone suffice
            if allInEliminatedIdealPT({}) then (
                f << "  SAVED: true (base case - remaining axioms alone)" << endl;
                if not member({}, savedCombos) then savedCombos = append(savedCombos, {});
                if requireLiteralGB then (
                    if allAppearInGBExactlyPT({}) then (
                        f << "  STRONG: true" << endl;
                        if not member({}, strongCandidates) then strongCandidates = append(strongCandidates, {});
                    ) else (
                        f << "  STRONG: false" << endl;
                    );
                ) else (
                    f << "  STRONG: true (by membership)" << endl;
                    if not member({}, strongCandidates) then strongCandidates = append(strongCandidates, {});
                );
            ) else (
                f << "  SAVED: false (base case fails)" << endl;
            );
        ) else (
            f << "  SKIPPED: all elements already implied by remaining axioms" << endl;
        );
    ) else (
        -- Test filtered combo
        if allInEliminatedIdealPT(filteredCombo) then (
            sortedCombo = sort filteredCombo;
            f << "  SAVED: true" << endl;
            if not member(sortedCombo, savedCombos) then (
                savedCombos = append(savedCombos, sortedCombo);
            );
            if requireLiteralGB then (
                if allAppearInGBExactlyPT(filteredCombo) then (
                    f << "  STRONG: true" << endl;
                    if not member(sortedCombo, strongCandidates) then (
                        strongCandidates = append(strongCandidates, sortedCombo);
                    );
                ) else (
                    f << "  STRONG: false" << endl;
                );
            ) else (
                f << "  STRONG: true (by membership)" << endl;
                if not member(sortedCombo, strongCandidates) then (
                    strongCandidates = append(strongCandidates, sortedCombo);
                );
            );
        ) else (
            f << "  SAVED: false (does not imply all targets)" << endl;
        );
    );
    f << endl;
));

f << "=== Summary ===" << endl;
f << "SAVED_COMBOS:" << endl;
scan(savedCombos, c -> f << "  " << toString c << endl);
f << endl;
f << "STRONG_CANDIDATES:" << endl;
scan(strongCandidates, c -> f << "  " << toString c << endl);

close f;

print("Reasoning complete. Output written to results/hall/abduction/noiseless/1_axiom(s)_removed/combo_9/reasoning/reasoning_output.txt");
