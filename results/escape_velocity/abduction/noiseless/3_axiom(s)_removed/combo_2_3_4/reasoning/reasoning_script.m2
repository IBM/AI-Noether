-- AI-Noether: Reasoning Template (Noiseless)
-- Tests if candidate axiom sets, when added to remaining axioms, prove targets

needsPackage("PrimaryDecomposition", Reload => true)

-- Ring definition
R = QQ[Eki, Ekf, Ugi, Ugf, G, M, m, ve, r, MonomialOrder => Lex];

-- Input data
remainingAxioms = toList([Eki - 1/2 * m * ve^2, Eki + Ugi - Ekf - Ugf]);
qList = toList([2*G*M*m - m*ve^2*r]);
k = #qList;

-- Per-target variable partitions
measuredPerTarget = {{G, M, m, ve, r}};
nonMeasuredPerTarget = {{Eki, Ekf, Ugi, Ugf}};

-- Candidate axiom sets to test (list of lists)
candidateSets = {{}, {Eki-Ekf+Ugi-Ugf}, {ve^2*r-2*G*M}, {m*ve^2-2*Ekf+2*Ugi-2*Ugf}, {G*M*m-Ekf*r+Ugi*r-Ugf*r}, {Eki-Ekf+Ugi-Ugf, ve^2*r-2*G*M}, {Eki-Ekf+Ugi-Ugf, m*ve^2-2*Ekf+2*Ugi-2*Ugf}, {Eki-Ekf+Ugi-Ugf, G*M*m-Ekf*r+Ugi*r-Ugf*r}, {ve^2*r-2*G*M, m*ve^2-2*Ekf+2*Ugi-2*Ugf}, {ve^2*r-2*G*M, G*M*m-Ekf*r+Ugi*r-Ugf*r}, {m*ve^2-2*Ekf+2*Ugi-2*Ugf, G*M*m-Ekf*r+Ugi*r-Ugf*r}, {Eki-Ekf+Ugi-Ugf, ve^2*r-2*G*M, m*ve^2-2*Ekf+2*Ugi-2*Ugf}, {Eki-Ekf+Ugi-Ugf, ve^2*r-2*G*M, G*M*m-Ekf*r+Ugi*r-Ugf*r}, {Eki-Ekf+Ugi-Ugf, m*ve^2-2*Ekf+2*Ugi-2*Ugf, G*M*m-Ekf*r+Ugi*r-Ugf*r}, {ve^2*r-2*G*M, m*ve^2-2*Ekf+2*Ugi-2*Ugf, G*M*m-Ekf*r+Ugi*r-Ugf*r}, {Eki-Ekf+Ugi-Ugf, ve^2*r-2*G*M, m*ve^2-2*Ekf+2*Ugi-2*Ugf, G*M*m-Ekf*r+Ugi*r-Ugf*r}, {m}, {Ekf-Ugi+Ugf}, {Eki}, {m, Ekf-Ugi+Ugf}, {m, Eki}, {Ekf-Ugi+Ugf, Eki}, {m, Ekf-Ugi+Ugf, Eki}};

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
f = openOut "results/escape_velocity/abduction/noiseless/3_axiom(s)_removed/combo_2_3_4/reasoning/reasoning_output.txt";
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

print("Reasoning complete. Output written to results/escape_velocity/abduction/noiseless/3_axiom(s)_removed/combo_2_3_4/reasoning/reasoning_output.txt");
