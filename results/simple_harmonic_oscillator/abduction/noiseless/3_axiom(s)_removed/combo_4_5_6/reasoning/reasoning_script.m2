-- AI-Noether: Reasoning Template (Noiseless)
-- Tests if candidate axiom sets, when added to remaining axioms, prove targets

needsPackage("PrimaryDecomposition", Reload => true)

-- Ring definition
R = QQ[F, ad, T, Fd, omega, theta, sintheta, m, d, g, L, j, Pi, Tj, MonomialOrder => Lex];

-- Input data
remainingAxioms = toList([ad-g*sintheta, Fd - m*ad, d-L*theta, sintheta - theta]);
qList = toList([d*g*Tj^2-4*d*L*j^2*Pi^2]);
k = #qList;

-- Per-target variable partitions
measuredPerTarget = {{d, g, L, j, Pi, Tj}};
nonMeasuredPerTarget = {{F, ad, T, Fd, omega, theta, sintheta, m}};

-- Candidate axiom sets to test (list of lists)
candidateSets = {{}, {L}, {d}, {theta-sintheta}, {sintheta*g-ad}, {ad*m-Fd}, {L, d}, {L, theta-sintheta}, {L, sintheta*g-ad}, {L, ad*m-Fd}, {d, theta-sintheta}, {d, sintheta*g-ad}, {d, ad*m-Fd}, {theta-sintheta, sintheta*g-ad}, {theta-sintheta, ad*m-Fd}, {sintheta*g-ad, ad*m-Fd}, {L, d, theta-sintheta}, {L, d, sintheta*g-ad}, {L, d, ad*m-Fd}, {L, theta-sintheta, sintheta*g-ad}, {L, theta-sintheta, ad*m-Fd}, {L, sintheta*g-ad, ad*m-Fd}, {d, theta-sintheta, sintheta*g-ad}, {d, theta-sintheta, ad*m-Fd}, {d, sintheta*g-ad, ad*m-Fd}, {theta-sintheta, sintheta*g-ad, ad*m-Fd}, {L, d, theta-sintheta, sintheta*g-ad}, {L, d, theta-sintheta, ad*m-Fd}, {L, d, sintheta*g-ad, ad*m-Fd}, {L, theta-sintheta, sintheta*g-ad, ad*m-Fd}, {d, theta-sintheta, sintheta*g-ad, ad*m-Fd}, {d}, {sintheta}, {theta}, {Fd}, {ad}, {d, sintheta}, {d, theta}, {d, Fd}, {d, ad}, {sintheta, theta}, {sintheta, Fd}, {sintheta, ad}, {theta, Fd}, {theta, ad}, {Fd, ad}, {d, sintheta, theta}, {d, sintheta, Fd}, {d, sintheta, ad}, {d, theta, Fd}, {d, theta, ad}, {d, Fd, ad}, {sintheta, theta, Fd}, {sintheta, theta, ad}, {sintheta, Fd, ad}, {theta, Fd, ad}, {d, sintheta, theta, Fd}, {d, sintheta, theta, ad}, {d, sintheta, Fd, ad}, {d, theta, Fd, ad}, {sintheta, theta, Fd, ad}, {theta-sintheta}, {sintheta*L-d}, {d*g-ad*L}, {sintheta*g-ad}, {ad*m-Fd}, {4*L*j^2*Pi^2-g*Tj^2}, {4*d*j^2*Pi^2-ad*Tj^2}, {theta-sintheta, sintheta*L-d}, {theta-sintheta, d*g-ad*L}, {theta-sintheta, sintheta*g-ad}, {theta-sintheta, ad*m-Fd}, {theta-sintheta, 4*L*j^2*Pi^2-g*Tj^2}, {theta-sintheta, 4*d*j^2*Pi^2-ad*Tj^2}, {sintheta*L-d, d*g-ad*L}, {sintheta*L-d, sintheta*g-ad}, {sintheta*L-d, ad*m-Fd}, {sintheta*L-d, 4*L*j^2*Pi^2-g*Tj^2}, {sintheta*L-d, 4*d*j^2*Pi^2-ad*Tj^2}, {d*g-ad*L, sintheta*g-ad}, {d*g-ad*L, ad*m-Fd}, {d*g-ad*L, 4*L*j^2*Pi^2-g*Tj^2}, {d*g-ad*L, 4*d*j^2*Pi^2-ad*Tj^2}, {sintheta*g-ad, ad*m-Fd}, {sintheta*g-ad, 4*L*j^2*Pi^2-g*Tj^2}, {sintheta*g-ad, 4*d*j^2*Pi^2-ad*Tj^2}, {ad*m-Fd, 4*L*j^2*Pi^2-g*Tj^2}, {ad*m-Fd, 4*d*j^2*Pi^2-ad*Tj^2}, {4*L*j^2*Pi^2-g*Tj^2, 4*d*j^2*Pi^2-ad*Tj^2}, {theta-sintheta, sintheta*L-d, d*g-ad*L}, {theta-sintheta, sintheta*L-d, sintheta*g-ad}, {theta-sintheta, sintheta*L-d, ad*m-Fd}, {theta-sintheta, sintheta*L-d, 4*L*j^2*Pi^2-g*Tj^2}, {theta-sintheta, sintheta*L-d, 4*d*j^2*Pi^2-ad*Tj^2}, {theta-sintheta, d*g-ad*L, sintheta*g-ad}, {theta-sintheta, d*g-ad*L, ad*m-Fd}, {theta-sintheta, d*g-ad*L, 4*L*j^2*Pi^2-g*Tj^2}, {theta-sintheta, d*g-ad*L, 4*d*j^2*Pi^2-ad*Tj^2}, {theta-sintheta, sintheta*g-ad, ad*m-Fd}, {theta-sintheta, sintheta*g-ad, 4*L*j^2*Pi^2-g*Tj^2}, {theta-sintheta, sintheta*g-ad, 4*d*j^2*Pi^2-ad*Tj^2}, {theta-sintheta, ad*m-Fd, 4*L*j^2*Pi^2-g*Tj^2}, {theta-sintheta, ad*m-Fd, 4*d*j^2*Pi^2-ad*Tj^2}, {theta-sintheta, 4*L*j^2*Pi^2-g*Tj^2, 4*d*j^2*Pi^2-ad*Tj^2}, {sintheta*L-d, d*g-ad*L, sintheta*g-ad}, {sintheta*L-d, d*g-ad*L, ad*m-Fd}, {sintheta*L-d, d*g-ad*L, 4*L*j^2*Pi^2-g*Tj^2}, {sintheta*L-d, d*g-ad*L, 4*d*j^2*Pi^2-ad*Tj^2}, {sintheta*L-d, sintheta*g-ad, ad*m-Fd}, {sintheta*L-d, sintheta*g-ad, 4*L*j^2*Pi^2-g*Tj^2}, {sintheta*L-d, sintheta*g-ad, 4*d*j^2*Pi^2-ad*Tj^2}, {sintheta*L-d, ad*m-Fd, 4*L*j^2*Pi^2-g*Tj^2}, {sintheta*L-d, ad*m-Fd, 4*d*j^2*Pi^2-ad*Tj^2}, {sintheta*L-d, 4*L*j^2*Pi^2-g*Tj^2, 4*d*j^2*Pi^2-ad*Tj^2}, {d*g-ad*L, sintheta*g-ad, ad*m-Fd}, {d*g-ad*L, sintheta*g-ad, 4*L*j^2*Pi^2-g*Tj^2}, {d*g-ad*L, sintheta*g-ad, 4*d*j^2*Pi^2-ad*Tj^2}, {d*g-ad*L, ad*m-Fd, 4*L*j^2*Pi^2-g*Tj^2}, {d*g-ad*L, ad*m-Fd, 4*d*j^2*Pi^2-ad*Tj^2}, {d*g-ad*L, 4*L*j^2*Pi^2-g*Tj^2, 4*d*j^2*Pi^2-ad*Tj^2}, {sintheta*g-ad, ad*m-Fd, 4*L*j^2*Pi^2-g*Tj^2}, {sintheta*g-ad, ad*m-Fd, 4*d*j^2*Pi^2-ad*Tj^2}, {sintheta*g-ad, 4*L*j^2*Pi^2-g*Tj^2, 4*d*j^2*Pi^2-ad*Tj^2}, {ad*m-Fd, 4*L*j^2*Pi^2-g*Tj^2, 4*d*j^2*Pi^2-ad*Tj^2}, {theta-sintheta, sintheta*L-d, d*g-ad*L, sintheta*g-ad}, {theta-sintheta, sintheta*L-d, d*g-ad*L, ad*m-Fd}, {theta-sintheta, sintheta*L-d, d*g-ad*L, 4*L*j^2*Pi^2-g*Tj^2}, {theta-sintheta, sintheta*L-d, d*g-ad*L, 4*d*j^2*Pi^2-ad*Tj^2}, {theta-sintheta, sintheta*L-d, sintheta*g-ad, ad*m-Fd}, {theta-sintheta, sintheta*L-d, sintheta*g-ad, 4*L*j^2*Pi^2-g*Tj^2}, {theta-sintheta, sintheta*L-d, sintheta*g-ad, 4*d*j^2*Pi^2-ad*Tj^2}, {theta-sintheta, sintheta*L-d, ad*m-Fd, 4*L*j^2*Pi^2-g*Tj^2}, {theta-sintheta, sintheta*L-d, ad*m-Fd, 4*d*j^2*Pi^2-ad*Tj^2}, {theta-sintheta, sintheta*L-d, 4*L*j^2*Pi^2-g*Tj^2, 4*d*j^2*Pi^2-ad*Tj^2}, {theta-sintheta, d*g-ad*L, sintheta*g-ad, ad*m-Fd}, {theta-sintheta, d*g-ad*L, sintheta*g-ad, 4*L*j^2*Pi^2-g*Tj^2}, {theta-sintheta, d*g-ad*L, sintheta*g-ad, 4*d*j^2*Pi^2-ad*Tj^2}, {theta-sintheta, d*g-ad*L, ad*m-Fd, 4*L*j^2*Pi^2-g*Tj^2}, {theta-sintheta, d*g-ad*L, ad*m-Fd, 4*d*j^2*Pi^2-ad*Tj^2}, {theta-sintheta, d*g-ad*L, 4*L*j^2*Pi^2-g*Tj^2, 4*d*j^2*Pi^2-ad*Tj^2}, {theta-sintheta, sintheta*g-ad, ad*m-Fd, 4*L*j^2*Pi^2-g*Tj^2}, {theta-sintheta, sintheta*g-ad, ad*m-Fd, 4*d*j^2*Pi^2-ad*Tj^2}, {theta-sintheta, sintheta*g-ad, 4*L*j^2*Pi^2-g*Tj^2, 4*d*j^2*Pi^2-ad*Tj^2}, {theta-sintheta, ad*m-Fd, 4*L*j^2*Pi^2-g*Tj^2, 4*d*j^2*Pi^2-ad*Tj^2}, {sintheta*L-d, d*g-ad*L, sintheta*g-ad, ad*m-Fd}, {sintheta*L-d, d*g-ad*L, sintheta*g-ad, 4*L*j^2*Pi^2-g*Tj^2}, {sintheta*L-d, d*g-ad*L, sintheta*g-ad, 4*d*j^2*Pi^2-ad*Tj^2}, {sintheta*L-d, d*g-ad*L, ad*m-Fd, 4*L*j^2*Pi^2-g*Tj^2}, {sintheta*L-d, d*g-ad*L, ad*m-Fd, 4*d*j^2*Pi^2-ad*Tj^2}, {sintheta*L-d, d*g-ad*L, 4*L*j^2*Pi^2-g*Tj^2, 4*d*j^2*Pi^2-ad*Tj^2}, {sintheta*L-d, sintheta*g-ad, ad*m-Fd, 4*L*j^2*Pi^2-g*Tj^2}, {sintheta*L-d, sintheta*g-ad, ad*m-Fd, 4*d*j^2*Pi^2-ad*Tj^2}, {sintheta*L-d, sintheta*g-ad, 4*L*j^2*Pi^2-g*Tj^2, 4*d*j^2*Pi^2-ad*Tj^2}, {sintheta*L-d, ad*m-Fd, 4*L*j^2*Pi^2-g*Tj^2, 4*d*j^2*Pi^2-ad*Tj^2}, {d*g-ad*L, sintheta*g-ad, ad*m-Fd, 4*L*j^2*Pi^2-g*Tj^2}, {d*g-ad*L, sintheta*g-ad, ad*m-Fd, 4*d*j^2*Pi^2-ad*Tj^2}, {d*g-ad*L, sintheta*g-ad, 4*L*j^2*Pi^2-g*Tj^2, 4*d*j^2*Pi^2-ad*Tj^2}, {d*g-ad*L, ad*m-Fd, 4*L*j^2*Pi^2-g*Tj^2, 4*d*j^2*Pi^2-ad*Tj^2}, {sintheta*g-ad, ad*m-Fd, 4*L*j^2*Pi^2-g*Tj^2, 4*d*j^2*Pi^2-ad*Tj^2}};

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
f = openOut "results/pendulum/abduction/noiseless/3_axiom(s)_removed/combo_4_5_6/reasoning/reasoning_output.txt";
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

print("Reasoning complete. Output written to results/pendulum/abduction/noiseless/3_axiom(s)_removed/combo_4_5_6/reasoning/reasoning_output.txt");
