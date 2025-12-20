-- AI-Noether: Reasoning Template (Noiseless)
-- Tests if candidate axiom sets, when added to remaining axioms, prove targets

needsPackage("PrimaryDecomposition", Reload => true)

-- Ring definition
R = QQ[ph, dp, mu, muN, muH, n, dsigma2dn, e, mup, p0, dn, beta, r, sigma, H, MonomialOrder => Lex];

-- Input data
remainingAxioms = toList([beta * mup - muN, n - dn, dp - dn, H * (ph + beta * n)^2 * e - r * ph + r * beta^2 * n]);
qList = toList([r*e*mup*dn*beta^2 + r*e*mup*dn*beta - r*sigma + e*p0*sigma*H + e*dn*beta*sigma*H + e*dn*sigma*H]);
k = #qList;

-- Per-target variable partitions
measuredPerTarget = {{sigma, r, e, mup, p0, dn, beta, H}};
nonMeasuredPerTarget = {{ph, dp, mu, muN, muH, n, dsigma2dn}};

-- Candidate axiom sets to test (list of lists)
candidateSets = {{}, {muN*dn^2*beta^3*r+dn^2*beta^3*sigma*H+muN*dn^2*beta^2*r+p0*dn*beta^2*sigma*H+2*dn^2*beta^2*sigma*H-ph*muN*dn*beta*r+ph*dn*beta*sigma*H-ph*muN*dn*r+ph^2*sigma*H-ph*p0*sigma*H-ph*dn*sigma*H}, {muN^2*dn^2*beta^2*r+muN*dn^2*beta^2*sigma*H+muN^2*dn^2*beta*r+muN*p0*dn*beta*sigma*H+2*muN*dn^2*beta*sigma*H-ph*muN^2*dn*r-ph*muN*mup*dn*r+ph^2*mup*sigma*H-ph*mup*p0*sigma*H+ph*muN*dn*sigma*H-ph*mup*dn*sigma*H}, {muN^3*dn^2*beta*r+muN^2*dn^2*beta*sigma*H-ph*muN^2*mup*dn*r-ph*muN*mup^2*dn*r+muN^3*dn^2*r+ph^2*mup^2*sigma*H-ph*mup^2*p0*sigma*H+ph*muN*mup*dn*sigma*H-ph*mup^2*dn*sigma*H+muN^2*p0*dn*sigma*H+2*muN^2*dn^2*sigma*H}, {ph*muN^2*mup^2*dn*r+ph*muN*mup^3*dn*r-muN^4*dn^2*r-muN^3*mup*dn^2*r-ph^2*mup^3*sigma*H+ph*mup^3*p0*sigma*H-ph*muN*mup^2*dn*sigma*H+ph*mup^3*dn*sigma*H-muN^2*mup*p0*dn*sigma*H-muN^3*dn^2*sigma*H-2*muN^2*mup*dn^2*sigma*H}, {muN*e*dn^3*beta^3+2*ph*muN*e*dn^2*beta^2+muN*e*dn^3*beta^2+ph^2*muN*e*dn*beta+2*ph*muN*e*dn^2*beta-dn^2*beta^3*sigma+ph^2*muN*e*dn-p0*dn*beta^2*sigma-2*dn^2*beta^2*sigma-ph*dn*beta*sigma-ph^2*sigma+ph*p0*sigma+ph*dn*sigma}, {muN^2*e*dn^3*beta^2+2*ph*muN^2*e*dn^2*beta+muN^2*e*dn^3*beta+ph^2*muN^2*e*dn+ph^2*muN*e*mup*dn+2*ph*muN^2*e*dn^2-muN*dn^2*beta^2*sigma-muN*p0*dn*beta*sigma-2*muN*dn^2*beta*sigma-ph^2*mup*sigma+ph*mup*p0*sigma-ph*muN*dn*sigma+ph*mup*dn*sigma}, {muN^3*e*dn^3*beta+ph^2*muN^2*e*mup*dn+ph^2*muN*e*mup^2*dn+2*ph*muN^3*e*dn^2+2*ph*muN^2*e*mup*dn^2+muN^3*e*dn^3-muN^2*dn^2*beta*sigma-ph^2*mup^2*sigma+ph*mup^2*p0*sigma-ph*muN*mup*dn*sigma+ph*mup^2*dn*sigma-muN^2*p0*dn*sigma-2*muN^2*dn^2*sigma}, {ph^2*muN^2*e*mup^2*dn+ph^2*muN*e*mup^3*dn+2*ph*muN^3*e*mup*dn^2+2*ph*muN^2*e*mup^2*dn^2+muN^4*e*dn^3+muN^3*e*mup*dn^3-ph^2*mup^3*sigma+ph*mup^3*p0*sigma-ph*muN*mup^2*dn*sigma+ph*mup^3*dn*sigma-muN^2*mup*p0*dn*sigma-muN^3*dn^2*sigma-2*muN^2*mup*dn^2*sigma}, {H}, {r}, {e}};

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
f = openOut "results/photoHall/abduction/noiseless/3_axiom(s)_removed/combo_2_3_6/reasoning/reasoning_output.txt";
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

print("Reasoning complete. Output written to results/photoHall/abduction/noiseless/3_axiom(s)_removed/combo_2_3_6/reasoning/reasoning_output.txt");
