-- AI-Noether: Reasoning Template (Noiseless)
-- Tests if candidate axiom sets, when added to remaining axioms, prove targets

needsPackage("PrimaryDecomposition", Reload => true)

-- Ring definition
R = QQ[F, ad, T, Fd, omega, theta, sintheta, m, d, g, L, j, Pi, Tj, MonomialOrder => Lex];

-- Input data
remainingAxioms = toList([ad-g*sintheta, Fd - m*ad, d-L*theta, d*omega^2-ad, Tj-j*T, sintheta - theta]);
qList = toList([d*g*Tj^2-4*d*L*j^2*Pi^2]);
k = #qList;

-- Per-target variable partitions
measuredPerTarget = {{d, g, L, j, Pi, Tj}};
nonMeasuredPerTarget = {{F, ad, T, Fd, omega, theta, sintheta, m}};

-- Candidate axiom sets to test (list of lists)
candidateSets = {{}, {omega^2*L-g}, {-T*j+Tj}, {j}, {-sintheta*L+d}, {theta-sintheta}, {-sintheta*m*g+Fd}, {-sintheta*g+ad}, {omega^2*L-g, -T*j+Tj}, {omega^2*L-g, j}, {omega^2*L-g, -sintheta*L+d}, {omega^2*L-g, theta-sintheta}, {omega^2*L-g, -sintheta*m*g+Fd}, {omega^2*L-g, -sintheta*g+ad}, {-T*j+Tj, j}, {-T*j+Tj, -sintheta*L+d}, {-T*j+Tj, theta-sintheta}, {-T*j+Tj, -sintheta*m*g+Fd}, {-T*j+Tj, -sintheta*g+ad}, {j, -sintheta*L+d}, {j, theta-sintheta}, {j, -sintheta*m*g+Fd}, {j, -sintheta*g+ad}, {-sintheta*L+d, theta-sintheta}, {-sintheta*L+d, -sintheta*m*g+Fd}, {-sintheta*L+d, -sintheta*g+ad}, {theta-sintheta, -sintheta*m*g+Fd}, {theta-sintheta, -sintheta*g+ad}, {-sintheta*m*g+Fd, -sintheta*g+ad}, {L}, {g}, {-T*j+Tj}, {-sintheta*L+d}, {theta-sintheta}, {-sintheta*m*g+Fd}, {-sintheta*g+ad}, {L, g}, {L, -T*j+Tj}, {L, -sintheta*L+d}, {L, theta-sintheta}, {L, -sintheta*m*g+Fd}, {L, -sintheta*g+ad}, {g, -T*j+Tj}, {g, -sintheta*L+d}, {g, theta-sintheta}, {g, -sintheta*m*g+Fd}, {g, -sintheta*g+ad}, {-T*j+Tj, -sintheta*L+d}, {-T*j+Tj, theta-sintheta}, {-T*j+Tj, -sintheta*m*g+Fd}, {-T*j+Tj, -sintheta*g+ad}, {-sintheta*L+d, theta-sintheta}, {-sintheta*L+d, -sintheta*m*g+Fd}, {-sintheta*L+d, -sintheta*g+ad}, {theta-sintheta, -sintheta*m*g+Fd}, {theta-sintheta, -sintheta*g+ad}, {-sintheta*m*g+Fd, -sintheta*g+ad}, {omega^2*L-g}, {-2*omega*L*Pi+T*g}, {T*omega-2*Pi}, {-T*j+Tj}, {-sintheta*L+d}, {theta-sintheta}, {-sintheta*m*g+Fd}, {-sintheta*g+ad}, {omega^2*L-g, -2*omega*L*Pi+T*g}, {omega^2*L-g, T*omega-2*Pi}, {omega^2*L-g, -T*j+Tj}, {omega^2*L-g, -sintheta*L+d}, {omega^2*L-g, theta-sintheta}, {omega^2*L-g, -sintheta*m*g+Fd}, {omega^2*L-g, -sintheta*g+ad}, {-2*omega*L*Pi+T*g, T*omega-2*Pi}, {-2*omega*L*Pi+T*g, -T*j+Tj}, {-2*omega*L*Pi+T*g, -sintheta*L+d}, {-2*omega*L*Pi+T*g, theta-sintheta}, {-2*omega*L*Pi+T*g, -sintheta*m*g+Fd}, {-2*omega*L*Pi+T*g, -sintheta*g+ad}, {T*omega-2*Pi, -T*j+Tj}, {T*omega-2*Pi, -sintheta*L+d}, {T*omega-2*Pi, theta-sintheta}, {T*omega-2*Pi, -sintheta*m*g+Fd}, {T*omega-2*Pi, -sintheta*g+ad}, {-T*j+Tj, -sintheta*L+d}, {-T*j+Tj, theta-sintheta}, {-T*j+Tj, -sintheta*m*g+Fd}, {-T*j+Tj, -sintheta*g+ad}, {-sintheta*L+d, theta-sintheta}, {-sintheta*L+d, -sintheta*m*g+Fd}, {-sintheta*L+d, -sintheta*g+ad}, {theta-sintheta, -sintheta*m*g+Fd}, {theta-sintheta, -sintheta*g+ad}, {-sintheta*m*g+Fd, -sintheta*g+ad}, {omega^2*L-g}, {2*omega*L*Pi+T*g}, {T*omega+2*Pi}, {-T*j+Tj}, {-sintheta*L+d}, {theta-sintheta}, {-sintheta*m*g+Fd}, {-sintheta*g+ad}, {omega^2*L-g, 2*omega*L*Pi+T*g}, {omega^2*L-g, T*omega+2*Pi}, {omega^2*L-g, -T*j+Tj}, {omega^2*L-g, -sintheta*L+d}, {omega^2*L-g, theta-sintheta}, {omega^2*L-g, -sintheta*m*g+Fd}, {omega^2*L-g, -sintheta*g+ad}, {2*omega*L*Pi+T*g, T*omega+2*Pi}, {2*omega*L*Pi+T*g, -T*j+Tj}, {2*omega*L*Pi+T*g, -sintheta*L+d}, {2*omega*L*Pi+T*g, theta-sintheta}, {2*omega*L*Pi+T*g, -sintheta*m*g+Fd}, {2*omega*L*Pi+T*g, -sintheta*g+ad}, {T*omega+2*Pi, -T*j+Tj}, {T*omega+2*Pi, -sintheta*L+d}, {T*omega+2*Pi, theta-sintheta}, {T*omega+2*Pi, -sintheta*m*g+Fd}, {T*omega+2*Pi, -sintheta*g+ad}, {-T*j+Tj, -sintheta*L+d}, {-T*j+Tj, theta-sintheta}, {-T*j+Tj, -sintheta*m*g+Fd}, {-T*j+Tj, -sintheta*g+ad}, {-sintheta*L+d, theta-sintheta}, {-sintheta*L+d, -sintheta*m*g+Fd}, {-sintheta*L+d, -sintheta*g+ad}, {theta-sintheta, -sintheta*m*g+Fd}, {theta-sintheta, -sintheta*g+ad}, {-sintheta*m*g+Fd, -sintheta*g+ad}, {-T*j+Tj}, {-sintheta*L+d}, {sintheta}, {theta-sintheta}, {-sintheta*m*g+Fd}, {-sintheta*g+ad}, {-T*j+Tj, -sintheta*L+d}, {-T*j+Tj, sintheta}, {-T*j+Tj, theta-sintheta}, {-T*j+Tj, -sintheta*m*g+Fd}, {-T*j+Tj, -sintheta*g+ad}, {-sintheta*L+d, sintheta}, {-sintheta*L+d, theta-sintheta}, {-sintheta*L+d, -sintheta*m*g+Fd}, {-sintheta*L+d, -sintheta*g+ad}, {sintheta, theta-sintheta}, {sintheta, -sintheta*m*g+Fd}, {sintheta, -sintheta*g+ad}, {theta-sintheta, -sintheta*m*g+Fd}, {theta-sintheta, -sintheta*g+ad}, {-sintheta*m*g+Fd, -sintheta*g+ad}};

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
f = openOut "results/pendulum/abduction/noiseless/1_axiom(s)_removed/combo_4/reasoning/reasoning_output.txt";
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

print("Reasoning complete. Output written to results/pendulum/abduction/noiseless/1_axiom(s)_removed/combo_4/reasoning/reasoning_output.txt");
