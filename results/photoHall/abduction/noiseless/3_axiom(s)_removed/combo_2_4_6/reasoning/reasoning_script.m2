-- AI-Noether: Reasoning Template (Noiseless)
-- Tests if candidate axiom sets, when added to remaining axioms, prove targets

needsPackage("PrimaryDecomposition", Reload => true)

-- Ring definition
R = QQ[ph, dp, mu, muN, muH, n, dsigma2dn, e, mup, p0, dn, beta, r, sigma, H, MonomialOrder => Lex];

-- Input data
remainingAxioms = toList([beta * mup - muN, ph - p0 - dp, dp - dn, H * (ph + beta * n)^2 * e - r * ph + r * beta^2 * n]);
qList = toList([r*e*mup*dn*beta^2 + r*e*mup*dn*beta - r*sigma + e*p0*sigma*H + e*dn*beta*sigma*H + e*dn*sigma*H]);
k = #qList;

-- Per-target variable partitions
measuredPerTarget = {{sigma, r, e, mup, p0, dn, beta, H}};
nonMeasuredPerTarget = {{ph, dp, mu, muN, muH, n, dsigma2dn}};

-- Candidate axiom sets to test (list of lists)
candidateSets = {{}, {n^2*e*beta*sigma*H-muN*e*p0*dn*r-e*mup*p0*dn*r-muN*e*dn^2*r-e*mup*dn^2*r+2*n*e*p0*sigma*H+2*n*e*dn*sigma*H-e*p0*dn*sigma*H-e*dn^2*sigma*H+n*beta*r*sigma}, {muN*n*dn*beta^2*r+n*dn*beta^2*sigma*H+muN*n*dn*beta*r+n^2*beta*sigma*H+n*p0*beta*sigma*H+n*dn*beta*sigma*H-muN*p0*dn*r-mup*p0*dn*r-muN*dn^2*r-mup*dn^2*r+2*n*p0*sigma*H+2*n*dn*sigma*H-p0*dn*sigma*H-dn^2*sigma*H}, {muN^2*n*dn*beta*r+muN*n*dn*beta*sigma*H+muN^2*n*dn*r-muN*mup*p0*dn*r-mup^2*p0*dn*r-muN*mup*dn^2*r-mup^2*dn^2*r+muN*n^2*sigma*H+muN*n*p0*sigma*H+2*n*mup*p0*sigma*H+muN*n*dn*sigma*H+2*n*mup*dn*sigma*H-mup*p0*dn*sigma*H-mup*dn^2*sigma*H}, {muN*e*mup*p0*dn*r+e*mup^2*p0*dn*r+muN*e*mup*dn^2*r+e*mup^2*dn^2*r-muN*n^2*e*sigma*H-2*n*e*mup*p0*sigma*H-2*n*e*mup*dn*sigma*H+e*mup*p0*dn*sigma*H+e*mup*dn^2*sigma*H-muN*n*r*sigma}, {muN^3*n*dn*r+muN^2*n*mup*dn*r-muN*mup^2*p0*dn*r-mup^3*p0*dn*r-muN*mup^2*dn^2*r-mup^3*dn^2*r+muN*n^2*mup*sigma*H+muN*n*mup*p0*sigma*H+2*n*mup^2*p0*sigma*H+muN^2*n*dn*sigma*H+muN*n*mup*dn*sigma*H+2*n*mup^2*dn*sigma*H-mup^2*p0*dn*sigma*H-mup^2*dn^2*sigma*H}, {muN*n^2*e*dn*r*H-2*muN*n*e*p0*dn*r*H-e*mup*p0^2*dn*r*H-2*muN*n*e*dn^2*r*H+muN*e*p0*dn^2*r*H-e*mup*p0*dn^2*r*H+muN*e*dn^3*r*H+n^2*e*p0*sigma*H^2+n^2*e*dn*sigma*H^2-2*n*e*p0*dn*sigma*H^2-2*n*e*dn^2*sigma*H^2+e*p0*dn^2*sigma*H^2+e*dn^3*sigma*H^2-muN*n*dn*beta*r^2-n*dn*beta*r*sigma*H+mup*p0*dn*r^2+mup*dn^2*r^2-n^2*r*sigma*H}, {muN*n^2*e*dn*beta^2+muN*n^2*e*dn*beta+2*muN*n*e*p0*dn*beta+2*muN*n*e*dn^2*beta+2*muN*n*e*p0*dn+muN*e*p0^2*dn+e*mup*p0^2*dn+2*muN*n*e*dn^2+2*muN*e*p0*dn^2+2*e*mup*p0*dn^2+muN*e*dn^3+e*mup*dn^3-n*dn*beta^2*sigma-n^2*beta*sigma-n*p0*beta*sigma-n*dn*beta*sigma-2*n*p0*sigma-2*n*dn*sigma+p0*dn*sigma+dn^2*sigma}, {muN^2*n^2*e*dn*beta+muN^2*n^2*e*dn+2*muN^2*n*e*p0*dn+2*muN*n*e*mup*p0*dn+muN*e*mup*p0^2*dn+e*mup^2*p0^2*dn+2*muN^2*n*e*dn^2+2*muN*n*e*mup*dn^2+2*muN*e*mup*p0*dn^2+2*e*mup^2*p0*dn^2+muN*e*mup*dn^3+e*mup^2*dn^3-muN*n*dn*beta*sigma-muN*n^2*sigma-muN*n*p0*sigma-2*n*mup*p0*sigma-muN*n*dn*sigma-2*n*mup*dn*sigma+mup*p0*dn*sigma+mup*dn^2*sigma}, {muN^3*n^2*e*dn+muN^2*n^2*e*mup*dn+2*muN^2*n*e*mup*p0*dn+2*muN*n*e*mup^2*p0*dn+muN*e*mup^2*p0^2*dn+e*mup^3*p0^2*dn+2*muN^2*n*e*mup*dn^2+2*muN*n*e*mup^2*dn^2+2*muN*e*mup^2*p0*dn^2+2*e*mup^3*p0*dn^2+muN*e*mup^2*dn^3+e*mup^3*dn^3-muN*n^2*mup*sigma-muN*n*mup*p0*sigma-2*n*mup^2*p0*sigma-muN^2*n*dn*sigma-muN*n*mup*dn*sigma-2*n*mup^2*dn*sigma+mup^2*p0*dn*sigma+mup^2*dn^2*sigma}, {n^2*e*mup^2*p0*dn*r*H-2*n*e*mup^2*p0^2*dn*r*H+e*mup^2*p0^3*dn*r*H+n^2*e*mup^2*dn^2*r*H-4*n*e*mup^2*p0*dn^2*r*H+3*e*mup^2*p0^2*dn^2*r*H-2*n*e*mup^2*dn^3*r*H+3*e*mup^2*p0*dn^3*r*H+e*mup^2*dn^4*r*H-muN*n^4*e*sigma*H^2+2*muN*n^3*e*p0*sigma*H^2-2*n^3*e*mup*p0*sigma*H^2+3*n^2*e*mup*p0^2*sigma*H^2+2*muN*n^3*e*dn*sigma*H^2-2*n^3*e*mup*dn*sigma*H^2-muN*n^2*e*p0*dn*sigma*H^2+7*n^2*e*mup*p0*dn*sigma*H^2-2*n*e*mup*p0^2*dn*sigma*H^2-muN*n^2*e*dn^2*sigma*H^2+4*n^2*e*mup*dn^2*sigma*H^2-4*n*e*mup*p0*dn^2*sigma*H^2-2*n*e*mup*dn^3*sigma*H^2+muN^2*n*p0*dn*r^2-mup^2*p0^2*dn*r^2+muN^2*n*dn^2*r^2-2*mup^2*p0*dn^2*r^2-mup^2*dn^3*r^2-muN*n^3*r*sigma*H+2*muN*n^2*p0*r*sigma*H+n^2*mup*p0*r*sigma*H+2*muN*n^2*dn*r*sigma*H+n^2*mup*dn*r*sigma*H}, {H}, {r}, {e}, {beta}, {muN}, {e*p0*H+e*dn*H-r}};

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
f = openOut "results/photoHall/abduction/noiseless/3_axiom(s)_removed/combo_2_4_6/reasoning/reasoning_output.txt";
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

print("Reasoning complete. Output written to results/photoHall/abduction/noiseless/3_axiom(s)_removed/combo_2_4_6/reasoning/reasoning_output.txt");
