-- AI-Noether: Reasoning Template (Noiseless)
-- Tests if candidate axiom sets, when added to remaining axioms, prove targets

needsPackage("PrimaryDecomposition", Reload => true)

-- Ring definition
R = QQ[f1, f2, E1, E2, Ee1, Ee2, p1, p2, pe2, lambda1, lambda2, h, me, c, coss, MonomialOrder => Lex];

-- Input data
remainingAxioms = toList([E1 + Ee1 - E2 - Ee2, E2 - h*f2, p1*c - h*f1, lambda1*f1 - c, lambda2*f2 - c, Ee1 - me*c^2, Ee2^2 - pe2^2*c^2 - me^2*c^4]);
qList = toList([lambda1*h*me*c^3 - lambda2*h*me*c^3 - coss*h^2*c^2 + h^2*c^2]);
k = #qList;

-- Per-target variable partitions
measuredPerTarget = {{lambda1, lambda2, h, me, c, coss}};
nonMeasuredPerTarget = {{f1, f2, E1, E2, Ee1, Ee2, p1, p2, pe2}};

-- Candidate axiom sets to test (list of lists)
candidateSets = {{}, {p1*lambda1-h}, {h*c*coss-Ee1*lambda1+Ee1*lambda2-h*c}, {f1*E2*coss-f1*E2+f1*Ee1-f2*Ee1}, {lambda1*me*c-lambda2*me*c-h*coss+h}, {E2*me*c-E2*p1*coss+E2*p1-Ee1*p1}, {f1*me*c-f2*me*c+f2*p1*coss-f2*p1}, {f1*lambda2*me-me*c+p1*coss-p1}, {f2*Ee1*lambda1-E2*c*coss+E2*c-Ee1*c}, {p1*c^2*coss+f1*Ee1*lambda2-p1*c^2-Ee1*c}, {E2*p1*c*coss-E2*p1*c+Ee1*p1*c-E2*Ee1}, {p1*lambda2*me*c-h*me*c+p1*h*coss-p1*h}, {Ee1*lambda1^2*me-2*Ee1*lambda1*lambda2*me+Ee1*lambda2^2*me-h^2*coss^2+2*h^2*coss-h^2}, {E2*p1*h*coss^2-E2*Ee1*lambda1*me+Ee1*h*me*c-2*E2*p1*h*coss+Ee1*p1*h*coss+E2*p1*h-Ee1*p1*h}, {E2*p1^2*coss^2+Ee1*p1*me*c-2*E2*p1^2*coss+Ee1*p1^2*coss+E2*p1^2-Ee1*p1^2-E2*Ee1*me}, {f2*E2*p1^2*coss-f2*E2*p1^2+f2*Ee1*p1^2-f1*E2^2*me}, {f2^2*p1^2*coss-f2^2*p1^2+f1^2*E2*me-f1*f2*E2*me}, {Ee1*p1*lambda2^2*me-p1*h^2*coss^2+Ee1*lambda1*h*me-2*Ee1*lambda2*h*me+2*p1*h^2*coss-p1*h^2}, {f2*Ee2^2*lambda1*me-E2*pe2^2*c*coss-E2*Ee1*p1*coss^2+E2*pe2^2*c-Ee2^2*me*c+2*E2*Ee1*p1*coss-Ee1^2*p1*coss-E2*Ee1*p1+Ee1^2*p1}, {Ee2^2*lambda1^2*me^2-2*Ee2^2*lambda1*lambda2*me^2+Ee2^2*lambda2^2*me^2-pe2^2*h^2*coss^2-Ee1*h^2*me*coss^2+2*pe2^2*h^2*coss+2*Ee1*h^2*me*coss-pe2^2*h^2-Ee1*h^2*me}, {Ee2^2*p1*lambda2^2*me^2-p1*pe2^2*h^2*coss^2-Ee1*p1*h^2*me*coss^2+Ee2^2*lambda1*h*me^2-2*Ee2^2*lambda2*h*me^2+2*p1*pe2^2*h^2*coss+2*Ee1*p1*h^2*me*coss-p1*pe2^2*h^2-Ee1*p1*h^2*me}, {c}, {h}, {lambda2}, {lambda1}, {Ee2}, {Ee1}, {E2}, {E1}, {f2}, {f1}, {E1-E2}, {p1}, {E1+Ee1-Ee2}};

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
f = openOut "results/compton/abduction/noiseless/3_axiom(s)_removed/combo_2_5_10/reasoning/reasoning_output.txt";
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

print("Reasoning complete. Output written to results/compton/abduction/noiseless/3_axiom(s)_removed/combo_2_5_10/reasoning/reasoning_output.txt");
