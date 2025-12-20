-- AI-Noether: Reasoning Template (Noiseless)
-- Tests if candidate axiom sets, when added to remaining axioms, prove targets

needsPackage("PrimaryDecomposition", Reload => true)

-- Ring definition
R = QQ[F, ad, T, Fd, omega, theta, sintheta, m, d, g, L, j, Pi, Tj, MonomialOrder => Lex];

-- Input data
remainingAxioms = toList([ad-g*sintheta, Fd - m*ad, Tj-j*T, sintheta - theta]);
qList = toList([d*g*Tj^2-4*d*L*j^2*Pi^2]);
k = #qList;

-- Per-target variable partitions
measuredPerTarget = {{d, g, L, j, Pi, Tj}};
nonMeasuredPerTarget = {{F, ad, T, Fd, omega, theta, sintheta, m}};

-- Candidate axiom sets to test (list of lists)
candidateSets = {{}, {d}, {theta-sintheta}, {T*j-Tj}, {sintheta*g-ad}, {ad*m-Fd}, {d, theta-sintheta}, {d, T*j-Tj}, {d, sintheta*g-ad}, {d, ad*m-Fd}, {theta-sintheta, T*j-Tj}, {theta-sintheta, sintheta*g-ad}, {theta-sintheta, ad*m-Fd}, {T*j-Tj, sintheta*g-ad}, {T*j-Tj, ad*m-Fd}, {sintheta*g-ad, ad*m-Fd}, {d, theta-sintheta, T*j-Tj}, {d, theta-sintheta, sintheta*g-ad}, {d, theta-sintheta, ad*m-Fd}, {d, T*j-Tj, sintheta*g-ad}, {d, T*j-Tj, ad*m-Fd}, {d, sintheta*g-ad, ad*m-Fd}, {theta-sintheta, T*j-Tj, sintheta*g-ad}, {theta-sintheta, T*j-Tj, ad*m-Fd}, {theta-sintheta, sintheta*g-ad, ad*m-Fd}, {T*j-Tj, sintheta*g-ad, ad*m-Fd}, {d, theta-sintheta, T*j-Tj, sintheta*g-ad}, {d, theta-sintheta, T*j-Tj, ad*m-Fd}, {d, theta-sintheta, sintheta*g-ad, ad*m-Fd}, {d, T*j-Tj, sintheta*g-ad, ad*m-Fd}, {theta-sintheta, T*j-Tj, sintheta*g-ad, ad*m-Fd}, {Tj}, {j}, {theta-sintheta}, {sintheta*g-ad}, {ad*m-Fd}, {Tj, j}, {Tj, theta-sintheta}, {Tj, sintheta*g-ad}, {Tj, ad*m-Fd}, {j, theta-sintheta}, {j, sintheta*g-ad}, {j, ad*m-Fd}, {theta-sintheta, sintheta*g-ad}, {theta-sintheta, ad*m-Fd}, {sintheta*g-ad, ad*m-Fd}, {Tj, j, theta-sintheta}, {Tj, j, sintheta*g-ad}, {Tj, j, ad*m-Fd}, {Tj, theta-sintheta, sintheta*g-ad}, {Tj, theta-sintheta, ad*m-Fd}, {Tj, sintheta*g-ad, ad*m-Fd}, {j, theta-sintheta, sintheta*g-ad}, {j, theta-sintheta, ad*m-Fd}, {j, sintheta*g-ad, ad*m-Fd}, {theta-sintheta, sintheta*g-ad, ad*m-Fd}, {Tj, j, theta-sintheta, sintheta*g-ad}, {Tj, j, theta-sintheta, ad*m-Fd}, {Tj, j, sintheta*g-ad, ad*m-Fd}, {Tj, theta-sintheta, sintheta*g-ad, ad*m-Fd}, {j, theta-sintheta, sintheta*g-ad, ad*m-Fd}, {theta-sintheta}, {T*j-Tj}, {sintheta*g-ad}, {ad*m-Fd}, {T^2*g-4*L*Pi^2}, {4*L*j*Pi^2-T*g*Tj}, {4*sintheta*L*Pi^2-ad*T^2}, {theta-sintheta, T*j-Tj}, {theta-sintheta, sintheta*g-ad}, {theta-sintheta, ad*m-Fd}, {theta-sintheta, T^2*g-4*L*Pi^2}, {theta-sintheta, 4*L*j*Pi^2-T*g*Tj}, {theta-sintheta, 4*sintheta*L*Pi^2-ad*T^2}, {T*j-Tj, sintheta*g-ad}, {T*j-Tj, ad*m-Fd}, {T*j-Tj, T^2*g-4*L*Pi^2}, {T*j-Tj, 4*L*j*Pi^2-T*g*Tj}, {T*j-Tj, 4*sintheta*L*Pi^2-ad*T^2}, {sintheta*g-ad, ad*m-Fd}, {sintheta*g-ad, T^2*g-4*L*Pi^2}, {sintheta*g-ad, 4*L*j*Pi^2-T*g*Tj}, {sintheta*g-ad, 4*sintheta*L*Pi^2-ad*T^2}, {ad*m-Fd, T^2*g-4*L*Pi^2}, {ad*m-Fd, 4*L*j*Pi^2-T*g*Tj}, {ad*m-Fd, 4*sintheta*L*Pi^2-ad*T^2}, {T^2*g-4*L*Pi^2, 4*L*j*Pi^2-T*g*Tj}, {T^2*g-4*L*Pi^2, 4*sintheta*L*Pi^2-ad*T^2}, {4*L*j*Pi^2-T*g*Tj, 4*sintheta*L*Pi^2-ad*T^2}, {theta-sintheta, T*j-Tj, sintheta*g-ad}, {theta-sintheta, T*j-Tj, ad*m-Fd}, {theta-sintheta, T*j-Tj, T^2*g-4*L*Pi^2}, {theta-sintheta, T*j-Tj, 4*L*j*Pi^2-T*g*Tj}, {theta-sintheta, T*j-Tj, 4*sintheta*L*Pi^2-ad*T^2}, {theta-sintheta, sintheta*g-ad, ad*m-Fd}, {theta-sintheta, sintheta*g-ad, T^2*g-4*L*Pi^2}, {theta-sintheta, sintheta*g-ad, 4*L*j*Pi^2-T*g*Tj}, {theta-sintheta, sintheta*g-ad, 4*sintheta*L*Pi^2-ad*T^2}, {theta-sintheta, ad*m-Fd, T^2*g-4*L*Pi^2}, {theta-sintheta, ad*m-Fd, 4*L*j*Pi^2-T*g*Tj}, {theta-sintheta, ad*m-Fd, 4*sintheta*L*Pi^2-ad*T^2}, {theta-sintheta, T^2*g-4*L*Pi^2, 4*L*j*Pi^2-T*g*Tj}, {theta-sintheta, T^2*g-4*L*Pi^2, 4*sintheta*L*Pi^2-ad*T^2}, {theta-sintheta, 4*L*j*Pi^2-T*g*Tj, 4*sintheta*L*Pi^2-ad*T^2}, {T*j-Tj, sintheta*g-ad, ad*m-Fd}, {T*j-Tj, sintheta*g-ad, T^2*g-4*L*Pi^2}, {T*j-Tj, sintheta*g-ad, 4*L*j*Pi^2-T*g*Tj}, {T*j-Tj, sintheta*g-ad, 4*sintheta*L*Pi^2-ad*T^2}, {T*j-Tj, ad*m-Fd, T^2*g-4*L*Pi^2}, {T*j-Tj, ad*m-Fd, 4*L*j*Pi^2-T*g*Tj}, {T*j-Tj, ad*m-Fd, 4*sintheta*L*Pi^2-ad*T^2}, {T*j-Tj, T^2*g-4*L*Pi^2, 4*L*j*Pi^2-T*g*Tj}, {T*j-Tj, T^2*g-4*L*Pi^2, 4*sintheta*L*Pi^2-ad*T^2}, {T*j-Tj, 4*L*j*Pi^2-T*g*Tj, 4*sintheta*L*Pi^2-ad*T^2}, {sintheta*g-ad, ad*m-Fd, T^2*g-4*L*Pi^2}, {sintheta*g-ad, ad*m-Fd, 4*L*j*Pi^2-T*g*Tj}, {sintheta*g-ad, ad*m-Fd, 4*sintheta*L*Pi^2-ad*T^2}, {sintheta*g-ad, T^2*g-4*L*Pi^2, 4*L*j*Pi^2-T*g*Tj}, {sintheta*g-ad, T^2*g-4*L*Pi^2, 4*sintheta*L*Pi^2-ad*T^2}, {sintheta*g-ad, 4*L*j*Pi^2-T*g*Tj, 4*sintheta*L*Pi^2-ad*T^2}, {ad*m-Fd, T^2*g-4*L*Pi^2, 4*L*j*Pi^2-T*g*Tj}, {ad*m-Fd, T^2*g-4*L*Pi^2, 4*sintheta*L*Pi^2-ad*T^2}, {ad*m-Fd, 4*L*j*Pi^2-T*g*Tj, 4*sintheta*L*Pi^2-ad*T^2}, {T^2*g-4*L*Pi^2, 4*L*j*Pi^2-T*g*Tj, 4*sintheta*L*Pi^2-ad*T^2}, {theta-sintheta, T*j-Tj, sintheta*g-ad, ad*m-Fd}, {theta-sintheta, T*j-Tj, sintheta*g-ad, T^2*g-4*L*Pi^2}, {theta-sintheta, T*j-Tj, sintheta*g-ad, 4*L*j*Pi^2-T*g*Tj}, {theta-sintheta, T*j-Tj, sintheta*g-ad, 4*sintheta*L*Pi^2-ad*T^2}, {theta-sintheta, T*j-Tj, ad*m-Fd, T^2*g-4*L*Pi^2}, {theta-sintheta, T*j-Tj, ad*m-Fd, 4*L*j*Pi^2-T*g*Tj}, {theta-sintheta, T*j-Tj, ad*m-Fd, 4*sintheta*L*Pi^2-ad*T^2}, {theta-sintheta, T*j-Tj, T^2*g-4*L*Pi^2, 4*L*j*Pi^2-T*g*Tj}, {theta-sintheta, T*j-Tj, T^2*g-4*L*Pi^2, 4*sintheta*L*Pi^2-ad*T^2}, {theta-sintheta, T*j-Tj, 4*L*j*Pi^2-T*g*Tj, 4*sintheta*L*Pi^2-ad*T^2}, {theta-sintheta, sintheta*g-ad, ad*m-Fd, T^2*g-4*L*Pi^2}, {theta-sintheta, sintheta*g-ad, ad*m-Fd, 4*L*j*Pi^2-T*g*Tj}, {theta-sintheta, sintheta*g-ad, ad*m-Fd, 4*sintheta*L*Pi^2-ad*T^2}, {theta-sintheta, sintheta*g-ad, T^2*g-4*L*Pi^2, 4*L*j*Pi^2-T*g*Tj}, {theta-sintheta, sintheta*g-ad, T^2*g-4*L*Pi^2, 4*sintheta*L*Pi^2-ad*T^2}, {theta-sintheta, sintheta*g-ad, 4*L*j*Pi^2-T*g*Tj, 4*sintheta*L*Pi^2-ad*T^2}, {theta-sintheta, ad*m-Fd, T^2*g-4*L*Pi^2, 4*L*j*Pi^2-T*g*Tj}, {theta-sintheta, ad*m-Fd, T^2*g-4*L*Pi^2, 4*sintheta*L*Pi^2-ad*T^2}, {theta-sintheta, ad*m-Fd, 4*L*j*Pi^2-T*g*Tj, 4*sintheta*L*Pi^2-ad*T^2}, {theta-sintheta, T^2*g-4*L*Pi^2, 4*L*j*Pi^2-T*g*Tj, 4*sintheta*L*Pi^2-ad*T^2}, {T*j-Tj, sintheta*g-ad, ad*m-Fd, T^2*g-4*L*Pi^2}, {T*j-Tj, sintheta*g-ad, ad*m-Fd, 4*L*j*Pi^2-T*g*Tj}, {T*j-Tj, sintheta*g-ad, ad*m-Fd, 4*sintheta*L*Pi^2-ad*T^2}, {T*j-Tj, sintheta*g-ad, T^2*g-4*L*Pi^2, 4*L*j*Pi^2-T*g*Tj}, {T*j-Tj, sintheta*g-ad, T^2*g-4*L*Pi^2, 4*sintheta*L*Pi^2-ad*T^2}, {T*j-Tj, sintheta*g-ad, 4*L*j*Pi^2-T*g*Tj, 4*sintheta*L*Pi^2-ad*T^2}, {T*j-Tj, ad*m-Fd, T^2*g-4*L*Pi^2, 4*L*j*Pi^2-T*g*Tj}, {T*j-Tj, ad*m-Fd, T^2*g-4*L*Pi^2, 4*sintheta*L*Pi^2-ad*T^2}, {T*j-Tj, ad*m-Fd, 4*L*j*Pi^2-T*g*Tj, 4*sintheta*L*Pi^2-ad*T^2}, {T*j-Tj, T^2*g-4*L*Pi^2, 4*L*j*Pi^2-T*g*Tj, 4*sintheta*L*Pi^2-ad*T^2}, {sintheta*g-ad, ad*m-Fd, T^2*g-4*L*Pi^2, 4*L*j*Pi^2-T*g*Tj}, {sintheta*g-ad, ad*m-Fd, T^2*g-4*L*Pi^2, 4*sintheta*L*Pi^2-ad*T^2}, {sintheta*g-ad, ad*m-Fd, 4*L*j*Pi^2-T*g*Tj, 4*sintheta*L*Pi^2-ad*T^2}, {sintheta*g-ad, T^2*g-4*L*Pi^2, 4*L*j*Pi^2-T*g*Tj, 4*sintheta*L*Pi^2-ad*T^2}, {ad*m-Fd, T^2*g-4*L*Pi^2, 4*L*j*Pi^2-T*g*Tj, 4*sintheta*L*Pi^2-ad*T^2}};

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
f = openOut "results/pendulum/abduction/noiseless/3_axiom(s)_removed/combo_3_4_5/reasoning/reasoning_output.txt";
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

print("Reasoning complete. Output written to results/pendulum/abduction/noiseless/3_axiom(s)_removed/combo_3_4_5/reasoning/reasoning_output.txt");
