-- AI-Noether: Reasoning Template (Noiseless)
-- Tests if candidate axiom sets, when added to remaining axioms, prove targets

needsPackage("PrimaryDecomposition", Reload => true)

-- Ring definition
R = QQ[Fm, d, v, Fe, E, dt, Q, N, V, i, n, qe, B, h, L, UH, MonomialOrder => Lex];

-- Input data
remainingAxioms = toList([Fm - qe*v*B, Fe - qe*E, E*h - UH, v*dt - L, Q - N*qe, V - L*h*d]);
qList = toList([N*qe*UH - i*B*h*L]);
k = #qList;

-- Per-target variable partitions
measuredPerTarget = {{UH, h, L, i, B, N, qe}};
nonMeasuredPerTarget = {{Fm, d, v, Fe, E, dt, Q, V, n}};

-- Candidate axiom sets to test (list of lists)
candidateSets = {{}, {-E*h+UH}, {-v*dt+L}, {h}, {-d*h*L+V}, {-N*qe+Q}, {-E*qe+Fe}, {-v*qe*B+Fm}, {-E*h+UH, -v*dt+L}, {-E*h+UH, h}, {-E*h+UH, -d*h*L+V}, {-E*h+UH, -N*qe+Q}, {-E*h+UH, -E*qe+Fe}, {-E*h+UH, -v*qe*B+Fm}, {-v*dt+L, h}, {-v*dt+L, -d*h*L+V}, {-v*dt+L, -N*qe+Q}, {-v*dt+L, -E*qe+Fe}, {-v*dt+L, -v*qe*B+Fm}, {h, -d*h*L+V}, {h, -N*qe+Q}, {h, -E*qe+Fe}, {h, -v*qe*B+Fm}, {-d*h*L+V, -N*qe+Q}, {-d*h*L+V, -E*qe+Fe}, {-d*h*L+V, -v*qe*B+Fm}, {-N*qe+Q, -E*qe+Fe}, {-N*qe+Q, -v*qe*B+Fm}, {-E*qe+Fe, -v*qe*B+Fm}, {-E*h+UH, -v*dt+L, h}, {-E*h+UH, -v*dt+L, -d*h*L+V}, {-E*h+UH, -v*dt+L, -N*qe+Q}, {-E*h+UH, -v*dt+L, -E*qe+Fe}, {-E*h+UH, -v*dt+L, -v*qe*B+Fm}, {-E*h+UH, h, -d*h*L+V}, {-E*h+UH, h, -N*qe+Q}, {-E*h+UH, h, -E*qe+Fe}, {-E*h+UH, h, -v*qe*B+Fm}, {-E*h+UH, -d*h*L+V, -N*qe+Q}, {-E*h+UH, -d*h*L+V, -E*qe+Fe}, {-E*h+UH, -d*h*L+V, -v*qe*B+Fm}, {-E*h+UH, -N*qe+Q, -E*qe+Fe}, {-E*h+UH, -N*qe+Q, -v*qe*B+Fm}, {-E*h+UH, -E*qe+Fe, -v*qe*B+Fm}, {-v*dt+L, h, -d*h*L+V}, {-v*dt+L, h, -N*qe+Q}, {-v*dt+L, h, -E*qe+Fe}, {-v*dt+L, h, -v*qe*B+Fm}, {-v*dt+L, -d*h*L+V, -N*qe+Q}, {-v*dt+L, -d*h*L+V, -E*qe+Fe}, {-v*dt+L, -d*h*L+V, -v*qe*B+Fm}, {-v*dt+L, -N*qe+Q, -E*qe+Fe}, {-v*dt+L, -N*qe+Q, -v*qe*B+Fm}, {-v*dt+L, -E*qe+Fe, -v*qe*B+Fm}, {h, -d*h*L+V, -N*qe+Q}, {h, -d*h*L+V, -E*qe+Fe}, {h, -d*h*L+V, -v*qe*B+Fm}, {h, -N*qe+Q, -E*qe+Fe}, {h, -N*qe+Q, -v*qe*B+Fm}, {h, -E*qe+Fe, -v*qe*B+Fm}, {-d*h*L+V, -N*qe+Q, -E*qe+Fe}, {-d*h*L+V, -N*qe+Q, -v*qe*B+Fm}, {-d*h*L+V, -E*qe+Fe, -v*qe*B+Fm}, {-N*qe+Q, -E*qe+Fe, -v*qe*B+Fm}, {-E*h+UH, -v*dt+L, h, -d*h*L+V}, {-E*h+UH, -v*dt+L, h, -N*qe+Q}, {-E*h+UH, -v*dt+L, h, -E*qe+Fe}, {-E*h+UH, -v*dt+L, h, -v*qe*B+Fm}, {-E*h+UH, -v*dt+L, -d*h*L+V, -N*qe+Q}, {-E*h+UH, -v*dt+L, -d*h*L+V, -E*qe+Fe}, {-E*h+UH, -v*dt+L, -d*h*L+V, -v*qe*B+Fm}, {-E*h+UH, -v*dt+L, -N*qe+Q, -E*qe+Fe}, {-E*h+UH, -v*dt+L, -N*qe+Q, -v*qe*B+Fm}, {-E*h+UH, -v*dt+L, -E*qe+Fe, -v*qe*B+Fm}, {-E*h+UH, h, -d*h*L+V, -N*qe+Q}, {-E*h+UH, h, -d*h*L+V, -E*qe+Fe}, {-E*h+UH, h, -d*h*L+V, -v*qe*B+Fm}, {-E*h+UH, h, -N*qe+Q, -E*qe+Fe}, {-E*h+UH, h, -N*qe+Q, -v*qe*B+Fm}, {-E*h+UH, h, -E*qe+Fe, -v*qe*B+Fm}, {-E*h+UH, -d*h*L+V, -N*qe+Q, -E*qe+Fe}, {-E*h+UH, -d*h*L+V, -N*qe+Q, -v*qe*B+Fm}, {-E*h+UH, -d*h*L+V, -E*qe+Fe, -v*qe*B+Fm}, {-E*h+UH, -N*qe+Q, -E*qe+Fe, -v*qe*B+Fm}, {-v*dt+L, h, -d*h*L+V, -N*qe+Q}, {-v*dt+L, h, -d*h*L+V, -E*qe+Fe}, {-v*dt+L, h, -d*h*L+V, -v*qe*B+Fm}, {-v*dt+L, h, -N*qe+Q, -E*qe+Fe}, {-v*dt+L, h, -N*qe+Q, -v*qe*B+Fm}, {-v*dt+L, h, -E*qe+Fe, -v*qe*B+Fm}, {-v*dt+L, -d*h*L+V, -N*qe+Q, -E*qe+Fe}, {-v*dt+L, -d*h*L+V, -N*qe+Q, -v*qe*B+Fm}, {-v*dt+L, -d*h*L+V, -E*qe+Fe, -v*qe*B+Fm}, {-v*dt+L, -N*qe+Q, -E*qe+Fe, -v*qe*B+Fm}, {h, -d*h*L+V, -N*qe+Q, -E*qe+Fe}, {h, -d*h*L+V, -N*qe+Q, -v*qe*B+Fm}, {h, -d*h*L+V, -E*qe+Fe, -v*qe*B+Fm}, {h, -N*qe+Q, -E*qe+Fe, -v*qe*B+Fm}, {-d*h*L+V, -N*qe+Q, -E*qe+Fe, -v*qe*B+Fm}, {v*dt*i*B-E*N*qe}, {-E*h+UH}, {-v*dt+L}, {-d*h*L+V}, {-N*qe+Q}, {-E*qe+Fe}, {-v*qe*B+Fm}, {v*dt*i*B-E*N*qe, -E*h+UH}, {v*dt*i*B-E*N*qe, -v*dt+L}, {v*dt*i*B-E*N*qe, -d*h*L+V}, {v*dt*i*B-E*N*qe, -N*qe+Q}, {v*dt*i*B-E*N*qe, -E*qe+Fe}, {v*dt*i*B-E*N*qe, -v*qe*B+Fm}, {-E*h+UH, -v*dt+L}, {-E*h+UH, -d*h*L+V}, {-E*h+UH, -N*qe+Q}, {-E*h+UH, -E*qe+Fe}, {-E*h+UH, -v*qe*B+Fm}, {-v*dt+L, -d*h*L+V}, {-v*dt+L, -N*qe+Q}, {-v*dt+L, -E*qe+Fe}, {-v*dt+L, -v*qe*B+Fm}, {-d*h*L+V, -N*qe+Q}, {-d*h*L+V, -E*qe+Fe}, {-d*h*L+V, -v*qe*B+Fm}, {-N*qe+Q, -E*qe+Fe}, {-N*qe+Q, -v*qe*B+Fm}, {-E*qe+Fe, -v*qe*B+Fm}, {v*dt*i*B-E*N*qe, -E*h+UH, -v*dt+L}, {v*dt*i*B-E*N*qe, -E*h+UH, -d*h*L+V}, {v*dt*i*B-E*N*qe, -E*h+UH, -N*qe+Q}, {v*dt*i*B-E*N*qe, -E*h+UH, -E*qe+Fe}, {v*dt*i*B-E*N*qe, -E*h+UH, -v*qe*B+Fm}, {v*dt*i*B-E*N*qe, -v*dt+L, -d*h*L+V}, {v*dt*i*B-E*N*qe, -v*dt+L, -N*qe+Q}, {v*dt*i*B-E*N*qe, -v*dt+L, -E*qe+Fe}, {v*dt*i*B-E*N*qe, -v*dt+L, -v*qe*B+Fm}, {v*dt*i*B-E*N*qe, -d*h*L+V, -N*qe+Q}, {v*dt*i*B-E*N*qe, -d*h*L+V, -E*qe+Fe}, {v*dt*i*B-E*N*qe, -d*h*L+V, -v*qe*B+Fm}, {v*dt*i*B-E*N*qe, -N*qe+Q, -E*qe+Fe}, {v*dt*i*B-E*N*qe, -N*qe+Q, -v*qe*B+Fm}, {v*dt*i*B-E*N*qe, -E*qe+Fe, -v*qe*B+Fm}, {-E*h+UH, -v*dt+L, -d*h*L+V}, {-E*h+UH, -v*dt+L, -N*qe+Q}, {-E*h+UH, -v*dt+L, -E*qe+Fe}, {-E*h+UH, -v*dt+L, -v*qe*B+Fm}, {-E*h+UH, -d*h*L+V, -N*qe+Q}, {-E*h+UH, -d*h*L+V, -E*qe+Fe}, {-E*h+UH, -d*h*L+V, -v*qe*B+Fm}, {-E*h+UH, -N*qe+Q, -E*qe+Fe}, {-E*h+UH, -N*qe+Q, -v*qe*B+Fm}, {-E*h+UH, -E*qe+Fe, -v*qe*B+Fm}, {-v*dt+L, -d*h*L+V, -N*qe+Q}, {-v*dt+L, -d*h*L+V, -E*qe+Fe}, {-v*dt+L, -d*h*L+V, -v*qe*B+Fm}, {-v*dt+L, -N*qe+Q, -E*qe+Fe}, {-v*dt+L, -N*qe+Q, -v*qe*B+Fm}, {-v*dt+L, -E*qe+Fe, -v*qe*B+Fm}, {-d*h*L+V, -N*qe+Q, -E*qe+Fe}, {-d*h*L+V, -N*qe+Q, -v*qe*B+Fm}, {-d*h*L+V, -E*qe+Fe, -v*qe*B+Fm}, {-N*qe+Q, -E*qe+Fe, -v*qe*B+Fm}, {v*dt*i*B-E*N*qe, -E*h+UH, -v*dt+L, -d*h*L+V}, {v*dt*i*B-E*N*qe, -E*h+UH, -v*dt+L, -N*qe+Q}, {v*dt*i*B-E*N*qe, -E*h+UH, -v*dt+L, -E*qe+Fe}, {v*dt*i*B-E*N*qe, -E*h+UH, -v*dt+L, -v*qe*B+Fm}, {v*dt*i*B-E*N*qe, -E*h+UH, -d*h*L+V, -N*qe+Q}, {v*dt*i*B-E*N*qe, -E*h+UH, -d*h*L+V, -E*qe+Fe}, {v*dt*i*B-E*N*qe, -E*h+UH, -d*h*L+V, -v*qe*B+Fm}, {v*dt*i*B-E*N*qe, -E*h+UH, -N*qe+Q, -E*qe+Fe}, {v*dt*i*B-E*N*qe, -E*h+UH, -N*qe+Q, -v*qe*B+Fm}, {v*dt*i*B-E*N*qe, -E*h+UH, -E*qe+Fe, -v*qe*B+Fm}, {v*dt*i*B-E*N*qe, -v*dt+L, -d*h*L+V, -N*qe+Q}, {v*dt*i*B-E*N*qe, -v*dt+L, -d*h*L+V, -E*qe+Fe}, {v*dt*i*B-E*N*qe, -v*dt+L, -d*h*L+V, -v*qe*B+Fm}, {v*dt*i*B-E*N*qe, -v*dt+L, -N*qe+Q, -E*qe+Fe}, {v*dt*i*B-E*N*qe, -v*dt+L, -N*qe+Q, -v*qe*B+Fm}, {v*dt*i*B-E*N*qe, -v*dt+L, -E*qe+Fe, -v*qe*B+Fm}, {v*dt*i*B-E*N*qe, -d*h*L+V, -N*qe+Q, -E*qe+Fe}, {v*dt*i*B-E*N*qe, -d*h*L+V, -N*qe+Q, -v*qe*B+Fm}, {v*dt*i*B-E*N*qe, -d*h*L+V, -E*qe+Fe, -v*qe*B+Fm}, {v*dt*i*B-E*N*qe, -N*qe+Q, -E*qe+Fe, -v*qe*B+Fm}, {-E*h+UH, -v*dt+L, -d*h*L+V, -N*qe+Q}, {-E*h+UH, -v*dt+L, -d*h*L+V, -E*qe+Fe}, {-E*h+UH, -v*dt+L, -d*h*L+V, -v*qe*B+Fm}, {-E*h+UH, -v*dt+L, -N*qe+Q, -E*qe+Fe}, {-E*h+UH, -v*dt+L, -N*qe+Q, -v*qe*B+Fm}, {-E*h+UH, -v*dt+L, -E*qe+Fe, -v*qe*B+Fm}, {-E*h+UH, -d*h*L+V, -N*qe+Q, -E*qe+Fe}, {-E*h+UH, -d*h*L+V, -N*qe+Q, -v*qe*B+Fm}, {-E*h+UH, -d*h*L+V, -E*qe+Fe, -v*qe*B+Fm}, {-E*h+UH, -N*qe+Q, -E*qe+Fe, -v*qe*B+Fm}, {-v*dt+L, -d*h*L+V, -N*qe+Q, -E*qe+Fe}, {-v*dt+L, -d*h*L+V, -N*qe+Q, -v*qe*B+Fm}, {-v*dt+L, -d*h*L+V, -E*qe+Fe, -v*qe*B+Fm}, {-v*dt+L, -N*qe+Q, -E*qe+Fe, -v*qe*B+Fm}, {-d*h*L+V, -N*qe+Q, -E*qe+Fe, -v*qe*B+Fm}};

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
f = openOut "results/hall/abduction/noiseless/3_axiom(s)_removed/combo_3_6_8/reasoning/reasoning_output.txt";
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

print("Reasoning complete. Output written to results/hall/abduction/noiseless/3_axiom(s)_removed/combo_3_6_8/reasoning/reasoning_output.txt");
