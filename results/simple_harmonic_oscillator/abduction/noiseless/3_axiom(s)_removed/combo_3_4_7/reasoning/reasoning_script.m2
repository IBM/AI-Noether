-- AI-Noether: Reasoning Template (Noiseless)
-- Tests if candidate axiom sets, when added to remaining axioms, prove targets

needsPackage("PrimaryDecomposition", Reload => true)

-- Ring definition
R = QQ[F, ad, T, Fd, omega, theta, sintheta, m, d, g, L, j, Pi, Tj, MonomialOrder => Lex];

-- Input data
remainingAxioms = toList([ad-g*sintheta, Fd - m*ad, d*omega^2-ad, Tj-j*T]);
qList = toList([d*g*Tj^2-4*d*L*j^2*Pi^2]);
k = #qList;

-- Per-target variable partitions
measuredPerTarget = {{d, g, L, j, Pi, Tj}};
nonMeasuredPerTarget = {{F, ad, T, Fd, omega, theta, sintheta, m}};

-- Candidate axiom sets to test (list of lists)
candidateSets = {{}, {T*j-Tj}, {sintheta*g-ad}, {ad*m-Fd}, {T^2*g-4*L*Pi^2}, {omega^2*d-ad}, {4*L*j*Pi^2-T*g*Tj}, {4*sintheta*L*Pi^2-ad*T^2}, {T*j-Tj, sintheta*g-ad}, {T*j-Tj, ad*m-Fd}, {T*j-Tj, T^2*g-4*L*Pi^2}, {T*j-Tj, omega^2*d-ad}, {T*j-Tj, 4*L*j*Pi^2-T*g*Tj}, {T*j-Tj, 4*sintheta*L*Pi^2-ad*T^2}, {sintheta*g-ad, ad*m-Fd}, {sintheta*g-ad, T^2*g-4*L*Pi^2}, {sintheta*g-ad, omega^2*d-ad}, {sintheta*g-ad, 4*L*j*Pi^2-T*g*Tj}, {sintheta*g-ad, 4*sintheta*L*Pi^2-ad*T^2}, {ad*m-Fd, T^2*g-4*L*Pi^2}, {ad*m-Fd, omega^2*d-ad}, {ad*m-Fd, 4*L*j*Pi^2-T*g*Tj}, {ad*m-Fd, 4*sintheta*L*Pi^2-ad*T^2}, {T^2*g-4*L*Pi^2, omega^2*d-ad}, {T^2*g-4*L*Pi^2, 4*L*j*Pi^2-T*g*Tj}, {T^2*g-4*L*Pi^2, 4*sintheta*L*Pi^2-ad*T^2}, {omega^2*d-ad, 4*L*j*Pi^2-T*g*Tj}, {omega^2*d-ad, 4*sintheta*L*Pi^2-ad*T^2}, {4*L*j*Pi^2-T*g*Tj, 4*sintheta*L*Pi^2-ad*T^2}, {T*j-Tj, sintheta*g-ad, ad*m-Fd}, {T*j-Tj, sintheta*g-ad, T^2*g-4*L*Pi^2}, {T*j-Tj, sintheta*g-ad, omega^2*d-ad}, {T*j-Tj, sintheta*g-ad, 4*L*j*Pi^2-T*g*Tj}, {T*j-Tj, sintheta*g-ad, 4*sintheta*L*Pi^2-ad*T^2}, {T*j-Tj, ad*m-Fd, T^2*g-4*L*Pi^2}, {T*j-Tj, ad*m-Fd, omega^2*d-ad}, {T*j-Tj, ad*m-Fd, 4*L*j*Pi^2-T*g*Tj}, {T*j-Tj, ad*m-Fd, 4*sintheta*L*Pi^2-ad*T^2}, {T*j-Tj, T^2*g-4*L*Pi^2, omega^2*d-ad}, {T*j-Tj, T^2*g-4*L*Pi^2, 4*L*j*Pi^2-T*g*Tj}, {T*j-Tj, T^2*g-4*L*Pi^2, 4*sintheta*L*Pi^2-ad*T^2}, {T*j-Tj, omega^2*d-ad, 4*L*j*Pi^2-T*g*Tj}, {T*j-Tj, omega^2*d-ad, 4*sintheta*L*Pi^2-ad*T^2}, {T*j-Tj, 4*L*j*Pi^2-T*g*Tj, 4*sintheta*L*Pi^2-ad*T^2}, {sintheta*g-ad, ad*m-Fd, T^2*g-4*L*Pi^2}, {sintheta*g-ad, ad*m-Fd, omega^2*d-ad}, {sintheta*g-ad, ad*m-Fd, 4*L*j*Pi^2-T*g*Tj}, {sintheta*g-ad, ad*m-Fd, 4*sintheta*L*Pi^2-ad*T^2}, {sintheta*g-ad, T^2*g-4*L*Pi^2, omega^2*d-ad}, {sintheta*g-ad, T^2*g-4*L*Pi^2, 4*L*j*Pi^2-T*g*Tj}, {sintheta*g-ad, T^2*g-4*L*Pi^2, 4*sintheta*L*Pi^2-ad*T^2}, {sintheta*g-ad, omega^2*d-ad, 4*L*j*Pi^2-T*g*Tj}, {sintheta*g-ad, omega^2*d-ad, 4*sintheta*L*Pi^2-ad*T^2}, {sintheta*g-ad, 4*L*j*Pi^2-T*g*Tj, 4*sintheta*L*Pi^2-ad*T^2}, {ad*m-Fd, T^2*g-4*L*Pi^2, omega^2*d-ad}, {ad*m-Fd, T^2*g-4*L*Pi^2, 4*L*j*Pi^2-T*g*Tj}, {ad*m-Fd, T^2*g-4*L*Pi^2, 4*sintheta*L*Pi^2-ad*T^2}, {ad*m-Fd, omega^2*d-ad, 4*L*j*Pi^2-T*g*Tj}, {ad*m-Fd, omega^2*d-ad, 4*sintheta*L*Pi^2-ad*T^2}, {ad*m-Fd, 4*L*j*Pi^2-T*g*Tj, 4*sintheta*L*Pi^2-ad*T^2}, {T^2*g-4*L*Pi^2, omega^2*d-ad, 4*L*j*Pi^2-T*g*Tj}, {T^2*g-4*L*Pi^2, omega^2*d-ad, 4*sintheta*L*Pi^2-ad*T^2}, {T^2*g-4*L*Pi^2, 4*L*j*Pi^2-T*g*Tj, 4*sintheta*L*Pi^2-ad*T^2}, {omega^2*d-ad, 4*L*j*Pi^2-T*g*Tj, 4*sintheta*L*Pi^2-ad*T^2}, {T*j-Tj, sintheta*g-ad, ad*m-Fd, T^2*g-4*L*Pi^2}, {T*j-Tj, sintheta*g-ad, ad*m-Fd, omega^2*d-ad}, {T*j-Tj, sintheta*g-ad, ad*m-Fd, 4*L*j*Pi^2-T*g*Tj}, {T*j-Tj, sintheta*g-ad, ad*m-Fd, 4*sintheta*L*Pi^2-ad*T^2}, {T*j-Tj, sintheta*g-ad, T^2*g-4*L*Pi^2, omega^2*d-ad}, {T*j-Tj, sintheta*g-ad, T^2*g-4*L*Pi^2, 4*L*j*Pi^2-T*g*Tj}, {T*j-Tj, sintheta*g-ad, T^2*g-4*L*Pi^2, 4*sintheta*L*Pi^2-ad*T^2}, {T*j-Tj, sintheta*g-ad, omega^2*d-ad, 4*L*j*Pi^2-T*g*Tj}, {T*j-Tj, sintheta*g-ad, omega^2*d-ad, 4*sintheta*L*Pi^2-ad*T^2}, {T*j-Tj, sintheta*g-ad, 4*L*j*Pi^2-T*g*Tj, 4*sintheta*L*Pi^2-ad*T^2}, {T*j-Tj, ad*m-Fd, T^2*g-4*L*Pi^2, omega^2*d-ad}, {T*j-Tj, ad*m-Fd, T^2*g-4*L*Pi^2, 4*L*j*Pi^2-T*g*Tj}, {T*j-Tj, ad*m-Fd, T^2*g-4*L*Pi^2, 4*sintheta*L*Pi^2-ad*T^2}, {T*j-Tj, ad*m-Fd, omega^2*d-ad, 4*L*j*Pi^2-T*g*Tj}, {T*j-Tj, ad*m-Fd, omega^2*d-ad, 4*sintheta*L*Pi^2-ad*T^2}, {T*j-Tj, ad*m-Fd, 4*L*j*Pi^2-T*g*Tj, 4*sintheta*L*Pi^2-ad*T^2}, {T*j-Tj, T^2*g-4*L*Pi^2, omega^2*d-ad, 4*L*j*Pi^2-T*g*Tj}, {T*j-Tj, T^2*g-4*L*Pi^2, omega^2*d-ad, 4*sintheta*L*Pi^2-ad*T^2}, {T*j-Tj, T^2*g-4*L*Pi^2, 4*L*j*Pi^2-T*g*Tj, 4*sintheta*L*Pi^2-ad*T^2}, {T*j-Tj, omega^2*d-ad, 4*L*j*Pi^2-T*g*Tj, 4*sintheta*L*Pi^2-ad*T^2}, {sintheta*g-ad, ad*m-Fd, T^2*g-4*L*Pi^2, omega^2*d-ad}, {sintheta*g-ad, ad*m-Fd, T^2*g-4*L*Pi^2, 4*L*j*Pi^2-T*g*Tj}, {sintheta*g-ad, ad*m-Fd, T^2*g-4*L*Pi^2, 4*sintheta*L*Pi^2-ad*T^2}, {sintheta*g-ad, ad*m-Fd, omega^2*d-ad, 4*L*j*Pi^2-T*g*Tj}, {sintheta*g-ad, ad*m-Fd, omega^2*d-ad, 4*sintheta*L*Pi^2-ad*T^2}, {sintheta*g-ad, ad*m-Fd, 4*L*j*Pi^2-T*g*Tj, 4*sintheta*L*Pi^2-ad*T^2}, {sintheta*g-ad, T^2*g-4*L*Pi^2, omega^2*d-ad, 4*L*j*Pi^2-T*g*Tj}, {sintheta*g-ad, T^2*g-4*L*Pi^2, omega^2*d-ad, 4*sintheta*L*Pi^2-ad*T^2}, {sintheta*g-ad, T^2*g-4*L*Pi^2, 4*L*j*Pi^2-T*g*Tj, 4*sintheta*L*Pi^2-ad*T^2}, {sintheta*g-ad, omega^2*d-ad, 4*L*j*Pi^2-T*g*Tj, 4*sintheta*L*Pi^2-ad*T^2}, {ad*m-Fd, T^2*g-4*L*Pi^2, omega^2*d-ad, 4*L*j*Pi^2-T*g*Tj}, {ad*m-Fd, T^2*g-4*L*Pi^2, omega^2*d-ad, 4*sintheta*L*Pi^2-ad*T^2}, {ad*m-Fd, T^2*g-4*L*Pi^2, 4*L*j*Pi^2-T*g*Tj, 4*sintheta*L*Pi^2-ad*T^2}, {ad*m-Fd, omega^2*d-ad, 4*L*j*Pi^2-T*g*Tj, 4*sintheta*L*Pi^2-ad*T^2}, {T^2*g-4*L*Pi^2, omega^2*d-ad, 4*L*j*Pi^2-T*g*Tj, 4*sintheta*L*Pi^2-ad*T^2}, {d}, {sintheta}, {Fd}, {ad}, {T*j-Tj}, {d, sintheta}, {d, Fd}, {d, ad}, {d, T*j-Tj}, {sintheta, Fd}, {sintheta, ad}, {sintheta, T*j-Tj}, {Fd, ad}, {Fd, T*j-Tj}, {ad, T*j-Tj}, {d, sintheta, Fd}, {d, sintheta, ad}, {d, sintheta, T*j-Tj}, {d, Fd, ad}, {d, Fd, T*j-Tj}, {d, ad, T*j-Tj}, {sintheta, Fd, ad}, {sintheta, Fd, T*j-Tj}, {sintheta, ad, T*j-Tj}, {Fd, ad, T*j-Tj}, {d, sintheta, Fd, ad}, {d, sintheta, Fd, T*j-Tj}, {d, sintheta, ad, T*j-Tj}, {d, Fd, ad, T*j-Tj}, {sintheta, Fd, ad, T*j-Tj}, {g}, {d}, {Fd}, {ad}, {T*j-Tj}, {g, d}, {g, Fd}, {g, ad}, {g, T*j-Tj}, {d, Fd}, {d, ad}, {d, T*j-Tj}, {Fd, ad}, {Fd, T*j-Tj}, {ad, T*j-Tj}, {g, d, Fd}, {g, d, ad}, {g, d, T*j-Tj}, {g, Fd, ad}, {g, Fd, T*j-Tj}, {g, ad, T*j-Tj}, {d, Fd, ad}, {d, Fd, T*j-Tj}, {d, ad, T*j-Tj}, {Fd, ad, T*j-Tj}, {g, d, Fd, ad}, {g, d, Fd, T*j-Tj}, {g, d, ad, T*j-Tj}, {g, Fd, ad, T*j-Tj}, {d, Fd, ad, T*j-Tj}, {Tj}, {j}, {sintheta*g-ad}, {ad*m-Fd}, {omega^2*d-ad}, {Tj, j}, {Tj, sintheta*g-ad}, {Tj, ad*m-Fd}, {Tj, omega^2*d-ad}, {j, sintheta*g-ad}, {j, ad*m-Fd}, {j, omega^2*d-ad}, {sintheta*g-ad, ad*m-Fd}, {sintheta*g-ad, omega^2*d-ad}, {ad*m-Fd, omega^2*d-ad}, {Tj, j, sintheta*g-ad}, {Tj, j, ad*m-Fd}, {Tj, j, omega^2*d-ad}, {Tj, sintheta*g-ad, ad*m-Fd}, {Tj, sintheta*g-ad, omega^2*d-ad}, {Tj, ad*m-Fd, omega^2*d-ad}, {j, sintheta*g-ad, ad*m-Fd}, {j, sintheta*g-ad, omega^2*d-ad}, {j, ad*m-Fd, omega^2*d-ad}, {sintheta*g-ad, ad*m-Fd, omega^2*d-ad}, {Tj, j, sintheta*g-ad, ad*m-Fd}, {Tj, j, sintheta*g-ad, omega^2*d-ad}, {Tj, j, ad*m-Fd, omega^2*d-ad}, {Tj, sintheta*g-ad, ad*m-Fd, omega^2*d-ad}, {j, sintheta*g-ad, ad*m-Fd, omega^2*d-ad}};

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
f = openOut "results/pendulum/abduction/noiseless/3_axiom(s)_removed/combo_3_4_7/reasoning/reasoning_output.txt";
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

print("Reasoning complete. Output written to results/pendulum/abduction/noiseless/3_axiom(s)_removed/combo_3_4_7/reasoning/reasoning_output.txt");
