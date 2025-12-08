-- AI-Noether: Reasoning Template (Noiseless)
-- Tests if candidate axiom sets, when added to remaining axioms, prove targets

needsPackage("PrimaryDecomposition", Reload => true)

-- Ring definition
R = QQ[S, ap, sintheta, dA, dtheta, r, P, qc, x0, w, MonomialOrder => Lex];

-- Input data
remainingAxioms = toList([S * r^2 - qc^2 * ap^2 * sintheta^2, P - S * dA, 2*ap^2 - w^4 * x0^2]);
qList = toList([75*P - 314*qc^2*w^4*x0^2]);
k = #qList;

-- Per-target variable partitions
measuredPerTarget = {{P, qc, x0, w}};
nonMeasuredPerTarget = {{S, ap, sintheta, dA, dtheta, r}};

-- Candidate axiom sets to test (list of lists)
candidateSets = {{}, {75*sintheta^2*dA-628*r^2}, {-x0^2*w^4+2*ap^2}, {-ap^2*sintheta^2*qc^2+S*r^2}, {-628*ap^2*qc^2+75*S*dA}, {-S*dA+P}, {75*sintheta^2*dA-628*r^2, -x0^2*w^4+2*ap^2}, {75*sintheta^2*dA-628*r^2, -ap^2*sintheta^2*qc^2+S*r^2}, {75*sintheta^2*dA-628*r^2, -628*ap^2*qc^2+75*S*dA}, {75*sintheta^2*dA-628*r^2, -S*dA+P}, {-x0^2*w^4+2*ap^2, -ap^2*sintheta^2*qc^2+S*r^2}, {-x0^2*w^4+2*ap^2, -628*ap^2*qc^2+75*S*dA}, {-x0^2*w^4+2*ap^2, -S*dA+P}, {-ap^2*sintheta^2*qc^2+S*r^2, -628*ap^2*qc^2+75*S*dA}, {-ap^2*sintheta^2*qc^2+S*r^2, -S*dA+P}, {-628*ap^2*qc^2+75*S*dA, -S*dA+P}, {75*sintheta^2*dA-628*r^2, -x0^2*w^4+2*ap^2, -ap^2*sintheta^2*qc^2+S*r^2}, {75*sintheta^2*dA-628*r^2, -x0^2*w^4+2*ap^2, -628*ap^2*qc^2+75*S*dA}, {75*sintheta^2*dA-628*r^2, -x0^2*w^4+2*ap^2, -S*dA+P}, {75*sintheta^2*dA-628*r^2, -ap^2*sintheta^2*qc^2+S*r^2, -628*ap^2*qc^2+75*S*dA}, {75*sintheta^2*dA-628*r^2, -ap^2*sintheta^2*qc^2+S*r^2, -S*dA+P}, {75*sintheta^2*dA-628*r^2, -628*ap^2*qc^2+75*S*dA, -S*dA+P}, {-x0^2*w^4+2*ap^2, -ap^2*sintheta^2*qc^2+S*r^2, -628*ap^2*qc^2+75*S*dA}, {-x0^2*w^4+2*ap^2, -ap^2*sintheta^2*qc^2+S*r^2, -S*dA+P}, {-x0^2*w^4+2*ap^2, -628*ap^2*qc^2+75*S*dA, -S*dA+P}, {-ap^2*sintheta^2*qc^2+S*r^2, -628*ap^2*qc^2+75*S*dA, -S*dA+P}, {-x0^2*w^4+2*ap^2}, {qc}, {-S*dA+P}, {S}, {-x0^2*w^4+2*ap^2, qc}, {-x0^2*w^4+2*ap^2, -S*dA+P}, {-x0^2*w^4+2*ap^2, S}, {qc, -S*dA+P}, {qc, S}, {-S*dA+P, S}, {-x0^2*w^4+2*ap^2, qc, -S*dA+P}, {-x0^2*w^4+2*ap^2, qc, S}, {-x0^2*w^4+2*ap^2, -S*dA+P, S}, {qc, -S*dA+P, S}, {w}, {-S*dA+P}, {ap}, {S}, {w, -S*dA+P}, {w, ap}, {w, S}, {-S*dA+P, ap}, {-S*dA+P, S}, {ap, S}, {w, -S*dA+P, ap}, {w, -S*dA+P, S}, {w, ap, S}, {-S*dA+P, ap, S}, {x0}, {-S*dA+P}, {ap}, {S}, {x0, -S*dA+P}, {x0, ap}, {x0, S}, {-S*dA+P, ap}, {-S*dA+P, S}, {ap, S}, {x0, -S*dA+P, ap}, {x0, -S*dA+P, S}, {x0, ap, S}, {-S*dA+P, ap, S}};

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
f = openOut "results/light/abduction/noiseless/2_axiom(s)_removed/combo_2_4/reasoning/reasoning_output.txt";
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

print("Reasoning complete. Output written to results/light/abduction/noiseless/2_axiom(s)_removed/combo_2_4/reasoning/reasoning_output.txt");
