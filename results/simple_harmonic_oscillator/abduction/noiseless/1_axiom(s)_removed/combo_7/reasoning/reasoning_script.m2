-- AI-Noether: Reasoning Template (Noiseless)
-- Tests if candidate axiom sets, when added to remaining axioms, prove targets

needsPackage("PrimaryDecomposition", Reload => true)

-- Ring definition
R = QQ[F, ad, T, Fd, omega, theta, sintheta, m, d, g, L, j, Pi, Tj, MonomialOrder => Lex];

-- Input data
remainingAxioms = toList([ad-g*sintheta, Fd - m*ad, d-L*theta, T*omega-2*Pi, d*omega^2-ad, Tj-j*T]);
qList = toList([d*g*Tj^2-4*d*L*j^2*Pi^2]);
k = #qList;

-- Per-target variable partitions
measuredPerTarget = {{d, g, L, j, Pi, Tj}};
nonMeasuredPerTarget = {{F, ad, T, Fd, omega, theta, sintheta, m}};

-- Candidate axiom sets to test (list of lists)
candidateSets = {{}, {theta-sintheta}, {2*j*Pi-omega*Tj}, {T*j-Tj}, {sintheta*L-d}, {d*g-ad*L}, {sintheta*g-ad}, {ad*m-Fd}, {T*omega-2*Pi}, {2*omega*L*Pi-T*g}, {2*omega*d*Pi-ad*T}, {omega^2*L-g}, {T^2*g-4*L*Pi^2}, {omega^2*d-ad}, {ad*T^2-4*d*Pi^2}, {4*m*d*Pi^2-T^2*Fd}, {theta-sintheta, 2*j*Pi-omega*Tj}, {theta-sintheta, T*j-Tj}, {theta-sintheta, sintheta*L-d}, {theta-sintheta, d*g-ad*L}, {theta-sintheta, sintheta*g-ad}, {theta-sintheta, ad*m-Fd}, {theta-sintheta, T*omega-2*Pi}, {theta-sintheta, 2*omega*L*Pi-T*g}, {theta-sintheta, 2*omega*d*Pi-ad*T}, {theta-sintheta, omega^2*L-g}, {theta-sintheta, T^2*g-4*L*Pi^2}, {theta-sintheta, omega^2*d-ad}, {theta-sintheta, ad*T^2-4*d*Pi^2}, {theta-sintheta, 4*m*d*Pi^2-T^2*Fd}, {2*j*Pi-omega*Tj, T*j-Tj}, {2*j*Pi-omega*Tj, sintheta*L-d}, {2*j*Pi-omega*Tj, d*g-ad*L}, {2*j*Pi-omega*Tj, sintheta*g-ad}, {2*j*Pi-omega*Tj, ad*m-Fd}, {2*j*Pi-omega*Tj, T*omega-2*Pi}, {2*j*Pi-omega*Tj, 2*omega*L*Pi-T*g}, {2*j*Pi-omega*Tj, 2*omega*d*Pi-ad*T}, {2*j*Pi-omega*Tj, omega^2*L-g}, {2*j*Pi-omega*Tj, T^2*g-4*L*Pi^2}, {2*j*Pi-omega*Tj, omega^2*d-ad}, {2*j*Pi-omega*Tj, ad*T^2-4*d*Pi^2}, {2*j*Pi-omega*Tj, 4*m*d*Pi^2-T^2*Fd}, {T*j-Tj, sintheta*L-d}, {T*j-Tj, d*g-ad*L}, {T*j-Tj, sintheta*g-ad}, {T*j-Tj, ad*m-Fd}, {T*j-Tj, T*omega-2*Pi}, {T*j-Tj, 2*omega*L*Pi-T*g}, {T*j-Tj, 2*omega*d*Pi-ad*T}, {T*j-Tj, omega^2*L-g}, {T*j-Tj, T^2*g-4*L*Pi^2}, {T*j-Tj, omega^2*d-ad}, {T*j-Tj, ad*T^2-4*d*Pi^2}, {T*j-Tj, 4*m*d*Pi^2-T^2*Fd}, {sintheta*L-d, d*g-ad*L}, {sintheta*L-d, sintheta*g-ad}, {sintheta*L-d, ad*m-Fd}, {sintheta*L-d, T*omega-2*Pi}, {sintheta*L-d, 2*omega*L*Pi-T*g}, {sintheta*L-d, 2*omega*d*Pi-ad*T}, {sintheta*L-d, omega^2*L-g}, {sintheta*L-d, T^2*g-4*L*Pi^2}, {sintheta*L-d, omega^2*d-ad}, {sintheta*L-d, ad*T^2-4*d*Pi^2}, {sintheta*L-d, 4*m*d*Pi^2-T^2*Fd}, {d*g-ad*L, sintheta*g-ad}, {d*g-ad*L, ad*m-Fd}, {d*g-ad*L, T*omega-2*Pi}, {d*g-ad*L, 2*omega*L*Pi-T*g}, {d*g-ad*L, 2*omega*d*Pi-ad*T}, {d*g-ad*L, omega^2*L-g}, {d*g-ad*L, T^2*g-4*L*Pi^2}, {d*g-ad*L, omega^2*d-ad}, {d*g-ad*L, ad*T^2-4*d*Pi^2}, {d*g-ad*L, 4*m*d*Pi^2-T^2*Fd}, {sintheta*g-ad, ad*m-Fd}, {sintheta*g-ad, T*omega-2*Pi}, {sintheta*g-ad, 2*omega*L*Pi-T*g}, {sintheta*g-ad, 2*omega*d*Pi-ad*T}, {sintheta*g-ad, omega^2*L-g}, {sintheta*g-ad, T^2*g-4*L*Pi^2}, {sintheta*g-ad, omega^2*d-ad}, {sintheta*g-ad, ad*T^2-4*d*Pi^2}, {sintheta*g-ad, 4*m*d*Pi^2-T^2*Fd}, {ad*m-Fd, T*omega-2*Pi}, {ad*m-Fd, 2*omega*L*Pi-T*g}, {ad*m-Fd, 2*omega*d*Pi-ad*T}, {ad*m-Fd, omega^2*L-g}, {ad*m-Fd, T^2*g-4*L*Pi^2}, {ad*m-Fd, omega^2*d-ad}, {ad*m-Fd, ad*T^2-4*d*Pi^2}, {ad*m-Fd, 4*m*d*Pi^2-T^2*Fd}, {T*omega-2*Pi, 2*omega*L*Pi-T*g}, {T*omega-2*Pi, 2*omega*d*Pi-ad*T}, {T*omega-2*Pi, omega^2*L-g}, {T*omega-2*Pi, T^2*g-4*L*Pi^2}, {T*omega-2*Pi, omega^2*d-ad}, {T*omega-2*Pi, ad*T^2-4*d*Pi^2}, {T*omega-2*Pi, 4*m*d*Pi^2-T^2*Fd}, {2*omega*L*Pi-T*g, 2*omega*d*Pi-ad*T}, {2*omega*L*Pi-T*g, omega^2*L-g}, {2*omega*L*Pi-T*g, T^2*g-4*L*Pi^2}, {2*omega*L*Pi-T*g, omega^2*d-ad}, {2*omega*L*Pi-T*g, ad*T^2-4*d*Pi^2}, {2*omega*L*Pi-T*g, 4*m*d*Pi^2-T^2*Fd}, {2*omega*d*Pi-ad*T, omega^2*L-g}, {2*omega*d*Pi-ad*T, T^2*g-4*L*Pi^2}, {2*omega*d*Pi-ad*T, omega^2*d-ad}, {2*omega*d*Pi-ad*T, ad*T^2-4*d*Pi^2}, {2*omega*d*Pi-ad*T, 4*m*d*Pi^2-T^2*Fd}, {omega^2*L-g, T^2*g-4*L*Pi^2}, {omega^2*L-g, omega^2*d-ad}, {omega^2*L-g, ad*T^2-4*d*Pi^2}, {omega^2*L-g, 4*m*d*Pi^2-T^2*Fd}, {T^2*g-4*L*Pi^2, omega^2*d-ad}, {T^2*g-4*L*Pi^2, ad*T^2-4*d*Pi^2}, {T^2*g-4*L*Pi^2, 4*m*d*Pi^2-T^2*Fd}, {omega^2*d-ad, ad*T^2-4*d*Pi^2}, {omega^2*d-ad, 4*m*d*Pi^2-T^2*Fd}, {ad*T^2-4*d*Pi^2, 4*m*d*Pi^2-T^2*Fd}, {d}, {sintheta}, {theta}, {Fd}, {ad}, {2*j*Pi-omega*Tj}, {T*j-Tj}, {T*omega-2*Pi}, {d, sintheta}, {d, theta}, {d, Fd}, {d, ad}, {d, 2*j*Pi-omega*Tj}, {d, T*j-Tj}, {d, T*omega-2*Pi}, {sintheta, theta}, {sintheta, Fd}, {sintheta, ad}, {sintheta, 2*j*Pi-omega*Tj}, {sintheta, T*j-Tj}, {sintheta, T*omega-2*Pi}, {theta, Fd}, {theta, ad}, {theta, 2*j*Pi-omega*Tj}, {theta, T*j-Tj}, {theta, T*omega-2*Pi}, {Fd, ad}, {Fd, 2*j*Pi-omega*Tj}, {Fd, T*j-Tj}, {Fd, T*omega-2*Pi}, {ad, 2*j*Pi-omega*Tj}, {ad, T*j-Tj}, {ad, T*omega-2*Pi}, {2*j*Pi-omega*Tj, T*j-Tj}, {2*j*Pi-omega*Tj, T*omega-2*Pi}, {T*j-Tj, T*omega-2*Pi}, {L}, {d}, {sintheta}, {Fd}, {ad}, {2*j*Pi-omega*Tj}, {T*j-Tj}, {T*omega-2*Pi}, {L, d}, {L, sintheta}, {L, Fd}, {L, ad}, {L, 2*j*Pi-omega*Tj}, {L, T*j-Tj}, {L, T*omega-2*Pi}, {d, sintheta}, {d, Fd}, {d, ad}, {d, 2*j*Pi-omega*Tj}, {d, T*j-Tj}, {d, T*omega-2*Pi}, {sintheta, Fd}, {sintheta, ad}, {sintheta, 2*j*Pi-omega*Tj}, {sintheta, T*j-Tj}, {sintheta, T*omega-2*Pi}, {Fd, ad}, {Fd, 2*j*Pi-omega*Tj}, {Fd, T*j-Tj}, {Fd, T*omega-2*Pi}, {ad, 2*j*Pi-omega*Tj}, {ad, T*j-Tj}, {ad, T*omega-2*Pi}, {2*j*Pi-omega*Tj, T*j-Tj}, {2*j*Pi-omega*Tj, T*omega-2*Pi}, {T*j-Tj, T*omega-2*Pi}, {L}, {g}, {d}, {Fd}, {ad}, {2*j*Pi-omega*Tj}, {T*j-Tj}, {T*omega-2*Pi}, {L, g}, {L, d}, {L, Fd}, {L, ad}, {L, 2*j*Pi-omega*Tj}, {L, T*j-Tj}, {L, T*omega-2*Pi}, {g, d}, {g, Fd}, {g, ad}, {g, 2*j*Pi-omega*Tj}, {g, T*j-Tj}, {g, T*omega-2*Pi}, {d, Fd}, {d, ad}, {d, 2*j*Pi-omega*Tj}, {d, T*j-Tj}, {d, T*omega-2*Pi}, {Fd, ad}, {Fd, 2*j*Pi-omega*Tj}, {Fd, T*j-Tj}, {Fd, T*omega-2*Pi}, {ad, 2*j*Pi-omega*Tj}, {ad, T*j-Tj}, {ad, T*omega-2*Pi}, {2*j*Pi-omega*Tj, T*j-Tj}, {2*j*Pi-omega*Tj, T*omega-2*Pi}, {T*j-Tj, T*omega-2*Pi}, {g}, {d}, {theta}, {Fd}, {ad}, {2*j*Pi-omega*Tj}, {T*j-Tj}, {T*omega-2*Pi}, {g, d}, {g, theta}, {g, Fd}, {g, ad}, {g, 2*j*Pi-omega*Tj}, {g, T*j-Tj}, {g, T*omega-2*Pi}, {d, theta}, {d, Fd}, {d, ad}, {d, 2*j*Pi-omega*Tj}, {d, T*j-Tj}, {d, T*omega-2*Pi}, {theta, Fd}, {theta, ad}, {theta, 2*j*Pi-omega*Tj}, {theta, T*j-Tj}, {theta, T*omega-2*Pi}, {Fd, ad}, {Fd, 2*j*Pi-omega*Tj}, {Fd, T*j-Tj}, {Fd, T*omega-2*Pi}, {ad, 2*j*Pi-omega*Tj}, {ad, T*j-Tj}, {ad, T*omega-2*Pi}, {2*j*Pi-omega*Tj, T*j-Tj}, {2*j*Pi-omega*Tj, T*omega-2*Pi}, {T*j-Tj, T*omega-2*Pi}, {Pi}, {g}, {omega}, {Fd}, {ad}, {T*j-Tj}, {theta*L-d}, {Pi, g}, {Pi, omega}, {Pi, Fd}, {Pi, ad}, {Pi, T*j-Tj}, {Pi, theta*L-d}, {g, omega}, {g, Fd}, {g, ad}, {g, T*j-Tj}, {g, theta*L-d}, {omega, Fd}, {omega, ad}, {omega, T*j-Tj}, {omega, theta*L-d}, {Fd, ad}, {Fd, T*j-Tj}, {Fd, theta*L-d}, {ad, T*j-Tj}, {ad, theta*L-d}, {T*j-Tj, theta*L-d}, {Tj}, {Pi}, {T}, {theta*L-d}, {sintheta*g-ad}, {ad*m-Fd}, {omega^2*d-ad}, {Tj, Pi}, {Tj, T}, {Tj, theta*L-d}, {Tj, sintheta*g-ad}, {Tj, ad*m-Fd}, {Tj, omega^2*d-ad}, {Pi, T}, {Pi, theta*L-d}, {Pi, sintheta*g-ad}, {Pi, ad*m-Fd}, {Pi, omega^2*d-ad}, {T, theta*L-d}, {T, sintheta*g-ad}, {T, ad*m-Fd}, {T, omega^2*d-ad}, {theta*L-d, sintheta*g-ad}, {theta*L-d, ad*m-Fd}, {theta*L-d, omega^2*d-ad}, {sintheta*g-ad, ad*m-Fd}, {sintheta*g-ad, omega^2*d-ad}, {ad*m-Fd, omega^2*d-ad}, {Tj}, {j}, {theta*L-d}, {sintheta*g-ad}, {ad*m-Fd}, {T*omega-2*Pi}, {2*omega*d*Pi-ad*T}, {omega^2*d-ad}, {ad*T^2-4*d*Pi^2}, {4*m*d*Pi^2-T^2*Fd}, {Tj, j}, {Tj, theta*L-d}, {Tj, sintheta*g-ad}, {Tj, ad*m-Fd}, {Tj, T*omega-2*Pi}, {Tj, 2*omega*d*Pi-ad*T}, {Tj, omega^2*d-ad}, {Tj, ad*T^2-4*d*Pi^2}, {Tj, 4*m*d*Pi^2-T^2*Fd}, {j, theta*L-d}, {j, sintheta*g-ad}, {j, ad*m-Fd}, {j, T*omega-2*Pi}, {j, 2*omega*d*Pi-ad*T}, {j, omega^2*d-ad}, {j, ad*T^2-4*d*Pi^2}, {j, 4*m*d*Pi^2-T^2*Fd}, {theta*L-d, sintheta*g-ad}, {theta*L-d, ad*m-Fd}, {theta*L-d, T*omega-2*Pi}, {theta*L-d, 2*omega*d*Pi-ad*T}, {theta*L-d, omega^2*d-ad}, {theta*L-d, ad*T^2-4*d*Pi^2}, {theta*L-d, 4*m*d*Pi^2-T^2*Fd}, {sintheta*g-ad, ad*m-Fd}, {sintheta*g-ad, T*omega-2*Pi}, {sintheta*g-ad, 2*omega*d*Pi-ad*T}, {sintheta*g-ad, omega^2*d-ad}, {sintheta*g-ad, ad*T^2-4*d*Pi^2}, {sintheta*g-ad, 4*m*d*Pi^2-T^2*Fd}, {ad*m-Fd, T*omega-2*Pi}, {ad*m-Fd, 2*omega*d*Pi-ad*T}, {ad*m-Fd, omega^2*d-ad}, {ad*m-Fd, ad*T^2-4*d*Pi^2}, {ad*m-Fd, 4*m*d*Pi^2-T^2*Fd}, {T*omega-2*Pi, 2*omega*d*Pi-ad*T}, {T*omega-2*Pi, omega^2*d-ad}, {T*omega-2*Pi, ad*T^2-4*d*Pi^2}, {T*omega-2*Pi, 4*m*d*Pi^2-T^2*Fd}, {2*omega*d*Pi-ad*T, omega^2*d-ad}, {2*omega*d*Pi-ad*T, ad*T^2-4*d*Pi^2}, {2*omega*d*Pi-ad*T, 4*m*d*Pi^2-T^2*Fd}, {omega^2*d-ad, ad*T^2-4*d*Pi^2}, {omega^2*d-ad, 4*m*d*Pi^2-T^2*Fd}, {ad*T^2-4*d*Pi^2, 4*m*d*Pi^2-T^2*Fd}};

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
f = openOut "results/pendulum/abduction/noiseless/1_axiom(s)_removed/combo_7/reasoning/reasoning_output.txt";
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

print("Reasoning complete. Output written to results/pendulum/abduction/noiseless/1_axiom(s)_removed/combo_7/reasoning/reasoning_output.txt");
