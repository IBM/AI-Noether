-- AI-Noether: Reasoning Template (Noiseless)
-- Tests if candidate axiom sets, when added to remaining axioms, prove targets

needsPackage("PrimaryDecomposition", Reload => true)

-- Ring definition
R = QQ[ph, dp, mu, muN, muH, n, dsigma2dn, e, mup, p0, dn, beta, r, sigma, H, MonomialOrder => Lex];

-- Input data
remainingAxioms = toList([beta * mup - muN, muH - r * mu, ph - p0 - dp, sigma - e * ph * mup - e * n * muN, H * (ph + beta * n)^2 * e - r * ph + r * beta^2 * n]);
qList = toList([r*e*mup*dn*beta^2 + r*e*mup*dn*beta - r*sigma + e*p0*sigma*H + e*dn*beta*sigma*H + e*dn*sigma*H]);
k = #qList;

-- Per-target variable partitions
measuredPerTarget = {{sigma, r, e, mup, p0, dn, beta, H}};
nonMeasuredPerTarget = {{ph, dp, mu, muN, muH, n, dsigma2dn}};

-- Candidate axiom sets to test (list of lists)
candidateSets = {{}, {n*e*p0*H-dp*e*dn*H+n*e*dn*H-e*p0*dn*H-n*r+dn*r}, {muN*dn*beta*r+dn*beta*sigma*H-muN*n*r-dp*mup*r-mup*p0*r+muN*dn*r+p0*sigma*H+dn*sigma*H}, {muN*n*mup*r+dp*mup^2*r+mup^2*p0*r-muN^2*dn*r-muN*mup*dn*r-mup*p0*sigma*H-muN*dn*sigma*H-mup*dn*sigma*H}, {muN*n^2*r+dp*n*mup*r+n*mup*p0*r-muN*n*dn*r-dp*mup*dn*r-mup*p0*dn*r-n*p0*sigma*H+dp*dn*sigma*H-n*dn*sigma*H+p0*dn*sigma*H}, {n^2*beta^2+n*p0*beta^2-dp*dn*beta^2-p0*dn*beta^2+2*dp*n*beta+2*n*p0*beta-2*dp*dn*beta-2*p0*dn*beta+dp^2+dp*p0-dp*dn-p0*dn}, {muN*n^2*beta+muN*n*p0*beta-dp*muN*dn*beta-muN*p0*dn*beta+2*dp*muN*n+dp^2*mup+2*muN*n*p0+dp*mup*p0-2*dp*muN*dn-dp*mup*dn-2*muN*p0*dn-mup*p0*dn}, {muN^2*n^2+2*dp*muN*n*mup+dp^2*mup^2+muN^2*n*p0+2*muN*n*mup*p0+dp*mup^2*p0-dp*muN^2*dn-2*dp*muN*mup*dn-dp*mup^2*dn-muN^2*p0*dn-2*muN*mup*p0*dn-mup^2*p0*dn}, {mu*dn*beta*sigma*H+muN*muH*dn*beta+mu*p0*sigma*H+mu*dn*sigma*H-muN*muH*n-dp*muH*mup-muH*mup*p0+muN*muH*dn}, {n^2*beta*sigma*H+n*p0*beta*sigma*H-dp*dn*beta*sigma*H-p0*dn*beta*sigma*H-dp*muN*n*r-dp*n*mup*r-muN*n*p0*r-n*mup*p0*r+dp*muN*dn*r+dp*mup*dn*r+muN*p0*dn*r+mup*p0*dn*r+dp*n*sigma*H+n*p0*sigma*H-dp*dn*sigma*H-p0*dn*sigma*H}, {mu*mup*p0*sigma*H+mu*muN*dn*sigma*H+mu*mup*dn*sigma*H-muN*muH*n*mup-dp*muH*mup^2-muH*mup^2*p0+muN^2*muH*dn+muN*muH*mup*dn}, {mu*n*p0*sigma*H-dp*mu*dn*sigma*H+mu*n*dn*sigma*H-mu*p0*dn*sigma*H-muN*muH*n^2-dp*muH*n*mup-muH*n*mup*p0+muN*muH*n*dn+dp*muH*mup*dn+muH*mup*p0*dn}, {dp*e*mup*p0*H+e*mup*p0^2*H+dp*muN*e*dn*H+dp*e*mup*dn*H+muN*e*p0*dn*H+e*mup*p0*dn*H+muN*n*r-muN*dn*r-p0*sigma*H-dn*sigma*H}, {dp*muN*mup^2*r+dp*mup^3*r+muN*mup^2*p0*r+mup^3*p0*r-muN^3*dn*r-muN^2*mup*dn*r-muN*n*mup*sigma*H-dp*mup^2*sigma*H-muN*mup*p0*sigma*H-mup^2*p0*sigma*H-muN^2*dn*sigma*H-muN*mup*dn*sigma*H}, {dp^2*mup^2*r-dp*n*mup^2*r+2*dp*mup^2*p0*r-n*mup^2*p0*r+mup^2*p0^2*r-dp*muN^2*dn*r+dp*mup^2*dn*r-muN^2*p0*dn*r+mup^2*p0*dn*r+muN*n^2*sigma*H+dp*n*mup*sigma*H+muN*n*p0*sigma*H-dp*mup*p0*sigma*H+n*mup*p0*sigma*H-mup*p0^2*sigma*H-2*dp*muN*dn*sigma*H-2*dp*mup*dn*sigma*H-2*muN*p0*dn*sigma*H-2*mup*p0*dn*sigma*H}, {dp*muN*e*dn*beta+muN*e*p0*dn*beta+dp*muN*e*p0+dp*e*mup*p0+muN*e*p0^2+e*mup*p0^2+2*dp*muN*e*dn+dp*e*mup*dn+2*muN*e*p0*dn+e*mup*p0*dn-n*beta*sigma-p0*beta*sigma-dp*sigma-p0*sigma}, {dp*muN*e*mup*p0+dp*e*mup^2*p0+muN*e*mup*p0^2+e*mup^2*p0^2+dp*muN^2*e*dn+2*dp*muN*e*mup*dn+dp*e*mup^2*dn+muN^2*e*p0*dn+2*muN*e*mup*p0*dn+e*mup^2*p0*dn-muN*n*sigma-dp*mup*sigma-muN*p0*sigma-mup*p0*sigma}, {dp^2*e*mup*p0-dp*n*e*mup*p0+2*dp*e*mup*p0^2-n*e*mup*p0^2+e*mup*p0^3+dp^2*muN*e*dn+2*dp^2*e*mup*dn-dp*n*e*mup*dn+2*dp*muN*e*p0*dn+4*dp*e*mup*p0*dn-n*e*mup*p0*dn+muN*e*p0^2*dn+2*e*mup*p0^2*dn+n^2*beta*sigma+n*p0*beta*sigma-dp*dn*beta*sigma-p0*dn*beta*sigma+dp*n*sigma-dp*p0*sigma+n*p0*sigma-p0^2*sigma-2*dp*dn*sigma-2*p0*dn*sigma}, {n*e*dn*beta^2*H+2*dp*e*dn*beta*H+2*e*p0*dn*beta*H+dn*beta^2*r+dp*e*p0*H+e*p0^2*H+dp*e*dn*H+e*p0*dn*H-dp*r-p0*r}, {dp*e*dn^2*beta^2*H+e*p0*dn^2*beta^2*H+2*dp*e*p0*dn*beta*H+2*e*p0^2*dn*beta*H+2*dp*e*dn^2*beta*H+2*e*p0*dn^2*beta*H+n*dn*beta^2*r+p0*dn*beta^2*r+dp*e*p0^2*H+e*p0^3*H+2*dp*e*p0*dn*H+2*e*p0^2*dn*H+dp*e*dn^2*H+e*p0*dn^2*H-dp*p0*r-p0^2*r-dp*dn*r-p0*dn*r}, {sigma}, {r}, {e}, {muH}, {H}, {n*beta+dp+p0}, {muN*n+dp*mup+mup*p0}, {n*beta^2-dp-p0}, {muN*n*beta-dp*mup-mup*p0}, {muN^2*n-dp*mup^2-mup^2*p0}, {mup}, {muN}, {beta}, {dp+p0}, {ph}, {beta+1}, {muN+mup}, {dp-n+p0}, {ph-n}};

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
f = openOut "results/photoHall/abduction/noiseless/2_axiom(s)_removed/combo_4_5/reasoning/reasoning_output.txt";
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

print("Reasoning complete. Output written to results/photoHall/abduction/noiseless/2_axiom(s)_removed/combo_4_5/reasoning/reasoning_output.txt");
