-- AI-Noether: Reasoning Template (Noiseless)
-- Tests if candidate axiom sets, when added to remaining axioms, prove targets

needsPackage("PrimaryDecomposition", Reload => true)

-- Ring definition
R = QQ[F, ad, T, Fd, omega, theta, sintheta, m, d, g, L, j, Pi, Tj, MonomialOrder => Lex];

-- Input data
remainingAxioms = toList([ad-g*sintheta, Fd - m*ad, d-L*theta, T*omega-2*Pi, d*omega^2-ad]);
qList = toList([d*g*Tj^2-4*d*L*j^2*Pi^2]);
k = #qList;

-- Per-target variable partitions
measuredPerTarget = {{d, g, L, j, Pi, Tj}};
nonMeasuredPerTarget = {{F, ad, T, Fd, omega, theta, sintheta, m}};

-- Candidate axiom sets to test (list of lists)
candidateSets = {{}, {omega^2*theta*L-sintheta*g}, {T^2*sintheta*j^2-theta*Tj^2}, {T^2*omega^2*L*j^2-g*Tj^2}, {-1/2*T*omega+Pi}, {-theta*L+d}, {-sintheta*m*g+Fd}, {-sintheta*g+ad}, {omega^2*theta*L-sintheta*g, T^2*sintheta*j^2-theta*Tj^2}, {omega^2*theta*L-sintheta*g, T^2*omega^2*L*j^2-g*Tj^2}, {omega^2*theta*L-sintheta*g, -1/2*T*omega+Pi}, {omega^2*theta*L-sintheta*g, -theta*L+d}, {omega^2*theta*L-sintheta*g, -sintheta*m*g+Fd}, {omega^2*theta*L-sintheta*g, -sintheta*g+ad}, {T^2*sintheta*j^2-theta*Tj^2, T^2*omega^2*L*j^2-g*Tj^2}, {T^2*sintheta*j^2-theta*Tj^2, -1/2*T*omega+Pi}, {T^2*sintheta*j^2-theta*Tj^2, -theta*L+d}, {T^2*sintheta*j^2-theta*Tj^2, -sintheta*m*g+Fd}, {T^2*sintheta*j^2-theta*Tj^2, -sintheta*g+ad}, {T^2*omega^2*L*j^2-g*Tj^2, -1/2*T*omega+Pi}, {T^2*omega^2*L*j^2-g*Tj^2, -theta*L+d}, {T^2*omega^2*L*j^2-g*Tj^2, -sintheta*m*g+Fd}, {T^2*omega^2*L*j^2-g*Tj^2, -sintheta*g+ad}, {-1/2*T*omega+Pi, -theta*L+d}, {-1/2*T*omega+Pi, -sintheta*m*g+Fd}, {-1/2*T*omega+Pi, -sintheta*g+ad}, {-theta*L+d, -sintheta*m*g+Fd}, {-theta*L+d, -sintheta*g+ad}, {-sintheta*m*g+Fd, -sintheta*g+ad}, {omega^2*theta*L-sintheta*g, T^2*sintheta*j^2-theta*Tj^2, T^2*omega^2*L*j^2-g*Tj^2}, {omega^2*theta*L-sintheta*g, T^2*sintheta*j^2-theta*Tj^2, -1/2*T*omega+Pi}, {omega^2*theta*L-sintheta*g, T^2*sintheta*j^2-theta*Tj^2, -theta*L+d}, {omega^2*theta*L-sintheta*g, T^2*sintheta*j^2-theta*Tj^2, -sintheta*m*g+Fd}, {omega^2*theta*L-sintheta*g, T^2*sintheta*j^2-theta*Tj^2, -sintheta*g+ad}, {omega^2*theta*L-sintheta*g, T^2*omega^2*L*j^2-g*Tj^2, -1/2*T*omega+Pi}, {omega^2*theta*L-sintheta*g, T^2*omega^2*L*j^2-g*Tj^2, -theta*L+d}, {omega^2*theta*L-sintheta*g, T^2*omega^2*L*j^2-g*Tj^2, -sintheta*m*g+Fd}, {omega^2*theta*L-sintheta*g, T^2*omega^2*L*j^2-g*Tj^2, -sintheta*g+ad}, {omega^2*theta*L-sintheta*g, -1/2*T*omega+Pi, -theta*L+d}, {omega^2*theta*L-sintheta*g, -1/2*T*omega+Pi, -sintheta*m*g+Fd}, {omega^2*theta*L-sintheta*g, -1/2*T*omega+Pi, -sintheta*g+ad}, {omega^2*theta*L-sintheta*g, -theta*L+d, -sintheta*m*g+Fd}, {omega^2*theta*L-sintheta*g, -theta*L+d, -sintheta*g+ad}, {omega^2*theta*L-sintheta*g, -sintheta*m*g+Fd, -sintheta*g+ad}, {T^2*sintheta*j^2-theta*Tj^2, T^2*omega^2*L*j^2-g*Tj^2, -1/2*T*omega+Pi}, {T^2*sintheta*j^2-theta*Tj^2, T^2*omega^2*L*j^2-g*Tj^2, -theta*L+d}, {T^2*sintheta*j^2-theta*Tj^2, T^2*omega^2*L*j^2-g*Tj^2, -sintheta*m*g+Fd}, {T^2*sintheta*j^2-theta*Tj^2, T^2*omega^2*L*j^2-g*Tj^2, -sintheta*g+ad}, {T^2*sintheta*j^2-theta*Tj^2, -1/2*T*omega+Pi, -theta*L+d}, {T^2*sintheta*j^2-theta*Tj^2, -1/2*T*omega+Pi, -sintheta*m*g+Fd}, {T^2*sintheta*j^2-theta*Tj^2, -1/2*T*omega+Pi, -sintheta*g+ad}, {T^2*sintheta*j^2-theta*Tj^2, -theta*L+d, -sintheta*m*g+Fd}, {T^2*sintheta*j^2-theta*Tj^2, -theta*L+d, -sintheta*g+ad}, {T^2*sintheta*j^2-theta*Tj^2, -sintheta*m*g+Fd, -sintheta*g+ad}, {T^2*omega^2*L*j^2-g*Tj^2, -1/2*T*omega+Pi, -theta*L+d}, {T^2*omega^2*L*j^2-g*Tj^2, -1/2*T*omega+Pi, -sintheta*m*g+Fd}, {T^2*omega^2*L*j^2-g*Tj^2, -1/2*T*omega+Pi, -sintheta*g+ad}, {T^2*omega^2*L*j^2-g*Tj^2, -theta*L+d, -sintheta*m*g+Fd}, {T^2*omega^2*L*j^2-g*Tj^2, -theta*L+d, -sintheta*g+ad}, {T^2*omega^2*L*j^2-g*Tj^2, -sintheta*m*g+Fd, -sintheta*g+ad}, {-1/2*T*omega+Pi, -theta*L+d, -sintheta*m*g+Fd}, {-1/2*T*omega+Pi, -theta*L+d, -sintheta*g+ad}, {-1/2*T*omega+Pi, -sintheta*m*g+Fd, -sintheta*g+ad}, {-theta*L+d, -sintheta*m*g+Fd, -sintheta*g+ad}, {-1/2*T*omega+Pi}, {-theta*L+d}, {sintheta}, {theta}, {-sintheta*m*g+Fd}, {-sintheta*g+ad}, {-1/2*T*omega+Pi, -theta*L+d}, {-1/2*T*omega+Pi, sintheta}, {-1/2*T*omega+Pi, theta}, {-1/2*T*omega+Pi, -sintheta*m*g+Fd}, {-1/2*T*omega+Pi, -sintheta*g+ad}, {-theta*L+d, sintheta}, {-theta*L+d, theta}, {-theta*L+d, -sintheta*m*g+Fd}, {-theta*L+d, -sintheta*g+ad}, {sintheta, theta}, {sintheta, -sintheta*m*g+Fd}, {sintheta, -sintheta*g+ad}, {theta, -sintheta*m*g+Fd}, {theta, -sintheta*g+ad}, {-sintheta*m*g+Fd, -sintheta*g+ad}, {-1/2*T*omega+Pi, -theta*L+d, sintheta}, {-1/2*T*omega+Pi, -theta*L+d, theta}, {-1/2*T*omega+Pi, -theta*L+d, -sintheta*m*g+Fd}, {-1/2*T*omega+Pi, -theta*L+d, -sintheta*g+ad}, {-1/2*T*omega+Pi, sintheta, theta}, {-1/2*T*omega+Pi, sintheta, -sintheta*m*g+Fd}, {-1/2*T*omega+Pi, sintheta, -sintheta*g+ad}, {-1/2*T*omega+Pi, theta, -sintheta*m*g+Fd}, {-1/2*T*omega+Pi, theta, -sintheta*g+ad}, {-1/2*T*omega+Pi, -sintheta*m*g+Fd, -sintheta*g+ad}, {-theta*L+d, sintheta, theta}, {-theta*L+d, sintheta, -sintheta*m*g+Fd}, {-theta*L+d, sintheta, -sintheta*g+ad}, {-theta*L+d, theta, -sintheta*m*g+Fd}, {-theta*L+d, theta, -sintheta*g+ad}, {-theta*L+d, -sintheta*m*g+Fd, -sintheta*g+ad}, {sintheta, theta, -sintheta*m*g+Fd}, {sintheta, theta, -sintheta*g+ad}, {sintheta, -sintheta*m*g+Fd, -sintheta*g+ad}, {theta, -sintheta*m*g+Fd, -sintheta*g+ad}, {-1/2*T*omega+Pi}, {L}, {g}, {-theta*L+d}, {-sintheta*m*g+Fd}, {-sintheta*g+ad}, {-1/2*T*omega+Pi, L}, {-1/2*T*omega+Pi, g}, {-1/2*T*omega+Pi, -theta*L+d}, {-1/2*T*omega+Pi, -sintheta*m*g+Fd}, {-1/2*T*omega+Pi, -sintheta*g+ad}, {L, g}, {L, -theta*L+d}, {L, -sintheta*m*g+Fd}, {L, -sintheta*g+ad}, {g, -theta*L+d}, {g, -sintheta*m*g+Fd}, {g, -sintheta*g+ad}, {-theta*L+d, -sintheta*m*g+Fd}, {-theta*L+d, -sintheta*g+ad}, {-sintheta*m*g+Fd, -sintheta*g+ad}, {-1/2*T*omega+Pi, L, g}, {-1/2*T*omega+Pi, L, -theta*L+d}, {-1/2*T*omega+Pi, L, -sintheta*m*g+Fd}, {-1/2*T*omega+Pi, L, -sintheta*g+ad}, {-1/2*T*omega+Pi, g, -theta*L+d}, {-1/2*T*omega+Pi, g, -sintheta*m*g+Fd}, {-1/2*T*omega+Pi, g, -sintheta*g+ad}, {-1/2*T*omega+Pi, -theta*L+d, -sintheta*m*g+Fd}, {-1/2*T*omega+Pi, -theta*L+d, -sintheta*g+ad}, {-1/2*T*omega+Pi, -sintheta*m*g+Fd, -sintheta*g+ad}, {L, g, -theta*L+d}, {L, g, -sintheta*m*g+Fd}, {L, g, -sintheta*g+ad}, {L, -theta*L+d, -sintheta*m*g+Fd}, {L, -theta*L+d, -sintheta*g+ad}, {L, -sintheta*m*g+Fd, -sintheta*g+ad}, {g, -theta*L+d, -sintheta*m*g+Fd}, {g, -theta*L+d, -sintheta*g+ad}, {g, -sintheta*m*g+Fd, -sintheta*g+ad}, {-theta*L+d, -sintheta*m*g+Fd, -sintheta*g+ad}, {-1/2*T*omega+Pi}, {L}, {-theta*L+d}, {sintheta}, {-sintheta*m*g+Fd}, {-sintheta*g+ad}, {-1/2*T*omega+Pi, L}, {-1/2*T*omega+Pi, -theta*L+d}, {-1/2*T*omega+Pi, sintheta}, {-1/2*T*omega+Pi, -sintheta*m*g+Fd}, {-1/2*T*omega+Pi, -sintheta*g+ad}, {L, -theta*L+d}, {L, sintheta}, {L, -sintheta*m*g+Fd}, {L, -sintheta*g+ad}, {-theta*L+d, sintheta}, {-theta*L+d, -sintheta*m*g+Fd}, {-theta*L+d, -sintheta*g+ad}, {sintheta, -sintheta*m*g+Fd}, {sintheta, -sintheta*g+ad}, {-sintheta*m*g+Fd, -sintheta*g+ad}, {-1/2*T*omega+Pi, L, -theta*L+d}, {-1/2*T*omega+Pi, L, sintheta}, {-1/2*T*omega+Pi, L, -sintheta*m*g+Fd}, {-1/2*T*omega+Pi, L, -sintheta*g+ad}, {-1/2*T*omega+Pi, -theta*L+d, sintheta}, {-1/2*T*omega+Pi, -theta*L+d, -sintheta*m*g+Fd}, {-1/2*T*omega+Pi, -theta*L+d, -sintheta*g+ad}, {-1/2*T*omega+Pi, sintheta, -sintheta*m*g+Fd}, {-1/2*T*omega+Pi, sintheta, -sintheta*g+ad}, {-1/2*T*omega+Pi, -sintheta*m*g+Fd, -sintheta*g+ad}, {L, -theta*L+d, sintheta}, {L, -theta*L+d, -sintheta*m*g+Fd}, {L, -theta*L+d, -sintheta*g+ad}, {L, sintheta, -sintheta*m*g+Fd}, {L, sintheta, -sintheta*g+ad}, {L, -sintheta*m*g+Fd, -sintheta*g+ad}, {-theta*L+d, sintheta, -sintheta*m*g+Fd}, {-theta*L+d, sintheta, -sintheta*g+ad}, {-theta*L+d, -sintheta*m*g+Fd, -sintheta*g+ad}, {sintheta, -sintheta*m*g+Fd, -sintheta*g+ad}, {-1/2*T*omega+Pi}, {g}, {-theta*L+d}, {theta}, {-sintheta*m*g+Fd}, {-sintheta*g+ad}, {-1/2*T*omega+Pi, g}, {-1/2*T*omega+Pi, -theta*L+d}, {-1/2*T*omega+Pi, theta}, {-1/2*T*omega+Pi, -sintheta*m*g+Fd}, {-1/2*T*omega+Pi, -sintheta*g+ad}, {g, -theta*L+d}, {g, theta}, {g, -sintheta*m*g+Fd}, {g, -sintheta*g+ad}, {-theta*L+d, theta}, {-theta*L+d, -sintheta*m*g+Fd}, {-theta*L+d, -sintheta*g+ad}, {theta, -sintheta*m*g+Fd}, {theta, -sintheta*g+ad}, {-sintheta*m*g+Fd, -sintheta*g+ad}, {-1/2*T*omega+Pi, g, -theta*L+d}, {-1/2*T*omega+Pi, g, theta}, {-1/2*T*omega+Pi, g, -sintheta*m*g+Fd}, {-1/2*T*omega+Pi, g, -sintheta*g+ad}, {-1/2*T*omega+Pi, -theta*L+d, theta}, {-1/2*T*omega+Pi, -theta*L+d, -sintheta*m*g+Fd}, {-1/2*T*omega+Pi, -theta*L+d, -sintheta*g+ad}, {-1/2*T*omega+Pi, theta, -sintheta*m*g+Fd}, {-1/2*T*omega+Pi, theta, -sintheta*g+ad}, {-1/2*T*omega+Pi, -sintheta*m*g+Fd, -sintheta*g+ad}, {g, -theta*L+d, theta}, {g, -theta*L+d, -sintheta*m*g+Fd}, {g, -theta*L+d, -sintheta*g+ad}, {g, theta, -sintheta*m*g+Fd}, {g, theta, -sintheta*g+ad}, {g, -sintheta*m*g+Fd, -sintheta*g+ad}, {-theta*L+d, theta, -sintheta*m*g+Fd}, {-theta*L+d, theta, -sintheta*g+ad}, {-theta*L+d, -sintheta*m*g+Fd, -sintheta*g+ad}, {theta, -sintheta*m*g+Fd, -sintheta*g+ad}, {-1/2*T*omega+Pi}, {g}, {-theta*L+d}, {omega}, {-sintheta*m*g+Fd}, {-sintheta*g+ad}, {-1/2*T*omega+Pi, g}, {-1/2*T*omega+Pi, -theta*L+d}, {-1/2*T*omega+Pi, omega}, {-1/2*T*omega+Pi, -sintheta*m*g+Fd}, {-1/2*T*omega+Pi, -sintheta*g+ad}, {g, -theta*L+d}, {g, omega}, {g, -sintheta*m*g+Fd}, {g, -sintheta*g+ad}, {-theta*L+d, omega}, {-theta*L+d, -sintheta*m*g+Fd}, {-theta*L+d, -sintheta*g+ad}, {omega, -sintheta*m*g+Fd}, {omega, -sintheta*g+ad}, {-sintheta*m*g+Fd, -sintheta*g+ad}, {-1/2*T*omega+Pi, g, -theta*L+d}, {-1/2*T*omega+Pi, g, omega}, {-1/2*T*omega+Pi, g, -sintheta*m*g+Fd}, {-1/2*T*omega+Pi, g, -sintheta*g+ad}, {-1/2*T*omega+Pi, -theta*L+d, omega}, {-1/2*T*omega+Pi, -theta*L+d, -sintheta*m*g+Fd}, {-1/2*T*omega+Pi, -theta*L+d, -sintheta*g+ad}, {-1/2*T*omega+Pi, omega, -sintheta*m*g+Fd}, {-1/2*T*omega+Pi, omega, -sintheta*g+ad}, {-1/2*T*omega+Pi, -sintheta*m*g+Fd, -sintheta*g+ad}, {g, -theta*L+d, omega}, {g, -theta*L+d, -sintheta*m*g+Fd}, {g, -theta*L+d, -sintheta*g+ad}, {g, omega, -sintheta*m*g+Fd}, {g, omega, -sintheta*g+ad}, {g, -sintheta*m*g+Fd, -sintheta*g+ad}, {-theta*L+d, omega, -sintheta*m*g+Fd}, {-theta*L+d, omega, -sintheta*g+ad}, {-theta*L+d, -sintheta*m*g+Fd, -sintheta*g+ad}, {omega, -sintheta*m*g+Fd, -sintheta*g+ad}};

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
f = openOut "results/pendulum/abduction/noiseless/2_axiom(s)_removed/combo_6_7/reasoning/reasoning_output.txt";
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

print("Reasoning complete. Output written to results/pendulum/abduction/noiseless/2_axiom(s)_removed/combo_6_7/reasoning/reasoning_output.txt");
