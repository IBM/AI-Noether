-- AI-Noether: Reasoning Template (Noiseless)
-- Tests if candidate axiom sets, when added to remaining axioms, prove targets

needsPackage("PrimaryDecomposition", Reload => true)

-- Ring definition
R = QQ[F, ad, T, Fd, omega, theta, sintheta, m, d, g, L, j, Pi, Tj, MonomialOrder => Lex];

-- Input data
remainingAxioms = toList([ad-g*sintheta, d-L*theta, d*omega^2-ad, Tj-j*T]);
qList = toList([d*g*Tj^2-4*d*L*j^2*Pi^2]);
k = #qList;

-- Per-target variable partitions
measuredPerTarget = {{d, g, L, j, Pi, Tj}};
nonMeasuredPerTarget = {{F, ad, T, Fd, omega, theta, sintheta, m}};

-- Candidate axiom sets to test (list of lists)
candidateSets = {{}, {omega^2*theta*L-sintheta*g}, {-T*j+Tj}, {j}, {-theta*L+d}, {-sintheta*g+ad}, {omega^2*theta*L-sintheta*g, -T*j+Tj}, {omega^2*theta*L-sintheta*g, j}, {omega^2*theta*L-sintheta*g, -theta*L+d}, {omega^2*theta*L-sintheta*g, -sintheta*g+ad}, {-T*j+Tj, j}, {-T*j+Tj, -theta*L+d}, {-T*j+Tj, -sintheta*g+ad}, {j, -theta*L+d}, {j, -sintheta*g+ad}, {-theta*L+d, -sintheta*g+ad}, {omega^2*theta*L-sintheta*g, -T*j+Tj, j}, {omega^2*theta*L-sintheta*g, -T*j+Tj, -theta*L+d}, {omega^2*theta*L-sintheta*g, -T*j+Tj, -sintheta*g+ad}, {omega^2*theta*L-sintheta*g, j, -theta*L+d}, {omega^2*theta*L-sintheta*g, j, -sintheta*g+ad}, {omega^2*theta*L-sintheta*g, -theta*L+d, -sintheta*g+ad}, {-T*j+Tj, j, -theta*L+d}, {-T*j+Tj, j, -sintheta*g+ad}, {-T*j+Tj, -theta*L+d, -sintheta*g+ad}, {j, -theta*L+d, -sintheta*g+ad}, {omega^2*theta*L-sintheta*g, -T*j+Tj, j, -theta*L+d}, {omega^2*theta*L-sintheta*g, -T*j+Tj, j, -sintheta*g+ad}, {omega^2*theta*L-sintheta*g, -T*j+Tj, -theta*L+d, -sintheta*g+ad}, {omega^2*theta*L-sintheta*g, j, -theta*L+d, -sintheta*g+ad}, {-T*j+Tj, j, -theta*L+d, -sintheta*g+ad}, {L}, {g}, {-T*j+Tj}, {-theta*L+d}, {-sintheta*g+ad}, {L, g}, {L, -T*j+Tj}, {L, -theta*L+d}, {L, -sintheta*g+ad}, {g, -T*j+Tj}, {g, -theta*L+d}, {g, -sintheta*g+ad}, {-T*j+Tj, -theta*L+d}, {-T*j+Tj, -sintheta*g+ad}, {-theta*L+d, -sintheta*g+ad}, {L, g, -T*j+Tj}, {L, g, -theta*L+d}, {L, g, -sintheta*g+ad}, {L, -T*j+Tj, -theta*L+d}, {L, -T*j+Tj, -sintheta*g+ad}, {L, -theta*L+d, -sintheta*g+ad}, {g, -T*j+Tj, -theta*L+d}, {g, -T*j+Tj, -sintheta*g+ad}, {g, -theta*L+d, -sintheta*g+ad}, {-T*j+Tj, -theta*L+d, -sintheta*g+ad}, {L, g, -T*j+Tj, -theta*L+d}, {L, g, -T*j+Tj, -sintheta*g+ad}, {L, g, -theta*L+d, -sintheta*g+ad}, {L, -T*j+Tj, -theta*L+d, -sintheta*g+ad}, {g, -T*j+Tj, -theta*L+d, -sintheta*g+ad}, {omega^2*theta*L-sintheta*g}, {T^2*g-4*L*Pi^2}, {T^2*omega^2*theta-4*sintheta*Pi^2}, {-T*j+Tj}, {-theta*L+d}, {-sintheta*g+ad}, {omega^2*theta*L-sintheta*g, T^2*g-4*L*Pi^2}, {omega^2*theta*L-sintheta*g, T^2*omega^2*theta-4*sintheta*Pi^2}, {omega^2*theta*L-sintheta*g, -T*j+Tj}, {omega^2*theta*L-sintheta*g, -theta*L+d}, {omega^2*theta*L-sintheta*g, -sintheta*g+ad}, {T^2*g-4*L*Pi^2, T^2*omega^2*theta-4*sintheta*Pi^2}, {T^2*g-4*L*Pi^2, -T*j+Tj}, {T^2*g-4*L*Pi^2, -theta*L+d}, {T^2*g-4*L*Pi^2, -sintheta*g+ad}, {T^2*omega^2*theta-4*sintheta*Pi^2, -T*j+Tj}, {T^2*omega^2*theta-4*sintheta*Pi^2, -theta*L+d}, {T^2*omega^2*theta-4*sintheta*Pi^2, -sintheta*g+ad}, {-T*j+Tj, -theta*L+d}, {-T*j+Tj, -sintheta*g+ad}, {-theta*L+d, -sintheta*g+ad}, {omega^2*theta*L-sintheta*g, T^2*g-4*L*Pi^2, T^2*omega^2*theta-4*sintheta*Pi^2}, {omega^2*theta*L-sintheta*g, T^2*g-4*L*Pi^2, -T*j+Tj}, {omega^2*theta*L-sintheta*g, T^2*g-4*L*Pi^2, -theta*L+d}, {omega^2*theta*L-sintheta*g, T^2*g-4*L*Pi^2, -sintheta*g+ad}, {omega^2*theta*L-sintheta*g, T^2*omega^2*theta-4*sintheta*Pi^2, -T*j+Tj}, {omega^2*theta*L-sintheta*g, T^2*omega^2*theta-4*sintheta*Pi^2, -theta*L+d}, {omega^2*theta*L-sintheta*g, T^2*omega^2*theta-4*sintheta*Pi^2, -sintheta*g+ad}, {omega^2*theta*L-sintheta*g, -T*j+Tj, -theta*L+d}, {omega^2*theta*L-sintheta*g, -T*j+Tj, -sintheta*g+ad}, {omega^2*theta*L-sintheta*g, -theta*L+d, -sintheta*g+ad}, {T^2*g-4*L*Pi^2, T^2*omega^2*theta-4*sintheta*Pi^2, -T*j+Tj}, {T^2*g-4*L*Pi^2, T^2*omega^2*theta-4*sintheta*Pi^2, -theta*L+d}, {T^2*g-4*L*Pi^2, T^2*omega^2*theta-4*sintheta*Pi^2, -sintheta*g+ad}, {T^2*g-4*L*Pi^2, -T*j+Tj, -theta*L+d}, {T^2*g-4*L*Pi^2, -T*j+Tj, -sintheta*g+ad}, {T^2*g-4*L*Pi^2, -theta*L+d, -sintheta*g+ad}, {T^2*omega^2*theta-4*sintheta*Pi^2, -T*j+Tj, -theta*L+d}, {T^2*omega^2*theta-4*sintheta*Pi^2, -T*j+Tj, -sintheta*g+ad}, {T^2*omega^2*theta-4*sintheta*Pi^2, -theta*L+d, -sintheta*g+ad}, {-T*j+Tj, -theta*L+d, -sintheta*g+ad}, {omega^2*theta*L-sintheta*g, T^2*g-4*L*Pi^2, T^2*omega^2*theta-4*sintheta*Pi^2, -T*j+Tj}, {omega^2*theta*L-sintheta*g, T^2*g-4*L*Pi^2, T^2*omega^2*theta-4*sintheta*Pi^2, -theta*L+d}, {omega^2*theta*L-sintheta*g, T^2*g-4*L*Pi^2, T^2*omega^2*theta-4*sintheta*Pi^2, -sintheta*g+ad}, {omega^2*theta*L-sintheta*g, T^2*g-4*L*Pi^2, -T*j+Tj, -theta*L+d}, {omega^2*theta*L-sintheta*g, T^2*g-4*L*Pi^2, -T*j+Tj, -sintheta*g+ad}, {omega^2*theta*L-sintheta*g, T^2*g-4*L*Pi^2, -theta*L+d, -sintheta*g+ad}, {omega^2*theta*L-sintheta*g, T^2*omega^2*theta-4*sintheta*Pi^2, -T*j+Tj, -theta*L+d}, {omega^2*theta*L-sintheta*g, T^2*omega^2*theta-4*sintheta*Pi^2, -T*j+Tj, -sintheta*g+ad}, {omega^2*theta*L-sintheta*g, T^2*omega^2*theta-4*sintheta*Pi^2, -theta*L+d, -sintheta*g+ad}, {omega^2*theta*L-sintheta*g, -T*j+Tj, -theta*L+d, -sintheta*g+ad}, {T^2*g-4*L*Pi^2, T^2*omega^2*theta-4*sintheta*Pi^2, -T*j+Tj, -theta*L+d}, {T^2*g-4*L*Pi^2, T^2*omega^2*theta-4*sintheta*Pi^2, -T*j+Tj, -sintheta*g+ad}, {T^2*g-4*L*Pi^2, T^2*omega^2*theta-4*sintheta*Pi^2, -theta*L+d, -sintheta*g+ad}, {T^2*g-4*L*Pi^2, -T*j+Tj, -theta*L+d, -sintheta*g+ad}, {T^2*omega^2*theta-4*sintheta*Pi^2, -T*j+Tj, -theta*L+d, -sintheta*g+ad}, {-T*j+Tj}, {L}, {-theta*L+d}, {sintheta}, {-sintheta*g+ad}, {-T*j+Tj, L}, {-T*j+Tj, -theta*L+d}, {-T*j+Tj, sintheta}, {-T*j+Tj, -sintheta*g+ad}, {L, -theta*L+d}, {L, sintheta}, {L, -sintheta*g+ad}, {-theta*L+d, sintheta}, {-theta*L+d, -sintheta*g+ad}, {sintheta, -sintheta*g+ad}, {-T*j+Tj, L, -theta*L+d}, {-T*j+Tj, L, sintheta}, {-T*j+Tj, L, -sintheta*g+ad}, {-T*j+Tj, -theta*L+d, sintheta}, {-T*j+Tj, -theta*L+d, -sintheta*g+ad}, {-T*j+Tj, sintheta, -sintheta*g+ad}, {L, -theta*L+d, sintheta}, {L, -theta*L+d, -sintheta*g+ad}, {L, sintheta, -sintheta*g+ad}, {-theta*L+d, sintheta, -sintheta*g+ad}, {-T*j+Tj, L, -theta*L+d, sintheta}, {-T*j+Tj, L, -theta*L+d, -sintheta*g+ad}, {-T*j+Tj, L, sintheta, -sintheta*g+ad}, {-T*j+Tj, -theta*L+d, sintheta, -sintheta*g+ad}, {L, -theta*L+d, sintheta, -sintheta*g+ad}, {-T*j+Tj}, {g}, {-theta*L+d}, {theta}, {-sintheta*g+ad}, {-T*j+Tj, g}, {-T*j+Tj, -theta*L+d}, {-T*j+Tj, theta}, {-T*j+Tj, -sintheta*g+ad}, {g, -theta*L+d}, {g, theta}, {g, -sintheta*g+ad}, {-theta*L+d, theta}, {-theta*L+d, -sintheta*g+ad}, {theta, -sintheta*g+ad}, {-T*j+Tj, g, -theta*L+d}, {-T*j+Tj, g, theta}, {-T*j+Tj, g, -sintheta*g+ad}, {-T*j+Tj, -theta*L+d, theta}, {-T*j+Tj, -theta*L+d, -sintheta*g+ad}, {-T*j+Tj, theta, -sintheta*g+ad}, {g, -theta*L+d, theta}, {g, -theta*L+d, -sintheta*g+ad}, {g, theta, -sintheta*g+ad}, {-theta*L+d, theta, -sintheta*g+ad}, {-T*j+Tj, g, -theta*L+d, theta}, {-T*j+Tj, g, -theta*L+d, -sintheta*g+ad}, {-T*j+Tj, g, theta, -sintheta*g+ad}, {-T*j+Tj, -theta*L+d, theta, -sintheta*g+ad}, {g, -theta*L+d, theta, -sintheta*g+ad}, {-T*j+Tj}, {-theta*L+d}, {sintheta}, {theta}, {-sintheta*g+ad}, {-T*j+Tj, -theta*L+d}, {-T*j+Tj, sintheta}, {-T*j+Tj, theta}, {-T*j+Tj, -sintheta*g+ad}, {-theta*L+d, sintheta}, {-theta*L+d, theta}, {-theta*L+d, -sintheta*g+ad}, {sintheta, theta}, {sintheta, -sintheta*g+ad}, {theta, -sintheta*g+ad}, {-T*j+Tj, -theta*L+d, sintheta}, {-T*j+Tj, -theta*L+d, theta}, {-T*j+Tj, -theta*L+d, -sintheta*g+ad}, {-T*j+Tj, sintheta, theta}, {-T*j+Tj, sintheta, -sintheta*g+ad}, {-T*j+Tj, theta, -sintheta*g+ad}, {-theta*L+d, sintheta, theta}, {-theta*L+d, sintheta, -sintheta*g+ad}, {-theta*L+d, theta, -sintheta*g+ad}, {sintheta, theta, -sintheta*g+ad}, {-T*j+Tj, -theta*L+d, sintheta, theta}, {-T*j+Tj, -theta*L+d, sintheta, -sintheta*g+ad}, {-T*j+Tj, -theta*L+d, theta, -sintheta*g+ad}, {-T*j+Tj, sintheta, theta, -sintheta*g+ad}, {-theta*L+d, sintheta, theta, -sintheta*g+ad}};

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
f = openOut "results/pendulum/abduction/noiseless/3_axiom(s)_removed/combo_2_4_7/reasoning/reasoning_output.txt";
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

print("Reasoning complete. Output written to results/pendulum/abduction/noiseless/3_axiom(s)_removed/combo_2_4_7/reasoning/reasoning_output.txt");
