-- AI-Noether: Reasoning Template (Noiseless)
-- Tests if candidate axiom sets, when added to remaining axioms, prove targets

needsPackage("PrimaryDecomposition", Reload => true)

-- Ring definition
R = QQ[ph, dp, mu, muN, muH, n, dsigma2dn, e, mup, p0, dn, beta, r, sigma, H, MonomialOrder => Lex];

-- Input data
remainingAxioms = toList([beta * mup - muN, muH - r * mu, ph - p0 - dp, H * (ph + beta * n)^2 * e - r * ph + r * beta^2 * n]);
qList = toList([r*e*mup*dn*beta^2 + r*e*mup*dn*beta - r*sigma + e*p0*sigma*H + e*dn*beta*sigma*H + e*dn*sigma*H]);
k = #qList;

-- Per-target variable partitions
measuredPerTarget = {{sigma, r, e, mup, p0, dn, beta, H}};
nonMeasuredPerTarget = {{ph, dp, mu, muN, muH, n, dsigma2dn}};

-- Candidate axiom sets to test (list of lists)
candidateSets = {{}, {muN*n*dn*beta^3*r+n*dn*beta^3*sigma*H+muN*n*dn*beta^2*r+n^2*beta^2*sigma*H+n*p0*beta^2*sigma*H+n*dn*beta^2*sigma*H-dp*muN*dn*beta*r-muN*p0*dn*beta*r+2*dp*n*beta*sigma*H+2*n*p0*beta*sigma*H-dp*dn*beta*sigma*H-p0*dn*beta*sigma*H-dp*muN*dn*r-muN*p0*dn*r+dp^2*sigma*H+dp*p0*sigma*H-dp*dn*sigma*H-p0*dn*sigma*H}, {muN^2*n*dn*beta^2*r+muN*n*dn*beta^2*sigma*H+muN^2*n*dn*beta*r+muN*n^2*beta*sigma*H+muN*n*p0*beta*sigma*H+muN*n*dn*beta*sigma*H-dp*muN^2*dn*r-dp*muN*mup*dn*r-muN^2*p0*dn*r-muN*mup*p0*dn*r+2*dp*muN*n*sigma*H+dp^2*mup*sigma*H+2*muN*n*p0*sigma*H+dp*mup*p0*sigma*H-dp*muN*dn*sigma*H-dp*mup*dn*sigma*H-muN*p0*dn*sigma*H-mup*p0*dn*sigma*H}, {muN^3*n*dn*beta*r+muN^2*n*dn*beta*sigma*H+muN^3*n*dn*r-dp*muN^2*mup*dn*r-dp*muN*mup^2*dn*r-muN^2*mup*p0*dn*r-muN*mup^2*p0*dn*r+muN^2*n^2*sigma*H+2*dp*muN*n*mup*sigma*H+dp^2*mup^2*sigma*H+muN^2*n*p0*sigma*H+2*muN*n*mup*p0*sigma*H+dp*mup^2*p0*sigma*H+muN^2*n*dn*sigma*H-dp*muN*mup*dn*sigma*H-dp*mup^2*dn*sigma*H-muN*mup*p0*dn*sigma*H-mup^2*p0*dn*sigma*H}, {muN^4*n*dn*r+muN^3*n*mup*dn*r-dp*muN^2*mup^2*dn*r-dp*muN*mup^3*dn*r-muN^2*mup^2*p0*dn*r-muN*mup^3*p0*dn*r+muN^2*n^2*mup*sigma*H+2*dp*muN*n*mup^2*sigma*H+dp^2*mup^3*sigma*H+muN^2*n*mup*p0*sigma*H+2*muN*n*mup^2*p0*sigma*H+dp*mup^3*p0*sigma*H+muN^3*n*dn*sigma*H+muN^2*n*mup*dn*sigma*H-dp*muN*mup^2*dn*sigma*H-dp*mup^3*dn*sigma*H-muN*mup^2*p0*dn*sigma*H-mup^3*p0*dn*sigma*H}, {mu*n*dn*beta^3*sigma*H+muN*muH*n*dn*beta^3+mu*n^2*beta^2*sigma*H+mu*n*p0*beta^2*sigma*H+mu*n*dn*beta^2*sigma*H+muN*muH*n*dn*beta^2+2*dp*mu*n*beta*sigma*H+2*mu*n*p0*beta*sigma*H-dp*mu*dn*beta*sigma*H-mu*p0*dn*beta*sigma*H-dp*muN*muH*dn*beta-muN*muH*p0*dn*beta+dp^2*mu*sigma*H+dp*mu*p0*sigma*H-dp*mu*dn*sigma*H-mu*p0*dn*sigma*H-dp*muN*muH*dn-muN*muH*p0*dn}, {mu*muN*n*dn*beta^2*sigma*H+muN^2*muH*n*dn*beta^2+mu*muN*n^2*beta*sigma*H+mu*muN*n*p0*beta*sigma*H+mu*muN*n*dn*beta*sigma*H+muN^2*muH*n*dn*beta+2*dp*mu*muN*n*sigma*H+dp^2*mu*mup*sigma*H+2*mu*muN*n*p0*sigma*H+dp*mu*mup*p0*sigma*H-dp*mu*muN*dn*sigma*H-dp*mu*mup*dn*sigma*H-mu*muN*p0*dn*sigma*H-mu*mup*p0*dn*sigma*H-dp*muN^2*muH*dn-dp*muN*muH*mup*dn-muN^2*muH*p0*dn-muN*muH*mup*p0*dn}, {mu*muN^2*n*dn*beta*sigma*H+muN^3*muH*n*dn*beta+mu*muN^2*n^2*sigma*H+2*dp*mu*muN*n*mup*sigma*H+dp^2*mu*mup^2*sigma*H+mu*muN^2*n*p0*sigma*H+2*mu*muN*n*mup*p0*sigma*H+dp*mu*mup^2*p0*sigma*H+mu*muN^2*n*dn*sigma*H-dp*mu*muN*mup*dn*sigma*H-dp*mu*mup^2*dn*sigma*H-mu*muN*mup*p0*dn*sigma*H-mu*mup^2*p0*dn*sigma*H+muN^3*muH*n*dn-dp*muN^2*muH*mup*dn-dp*muN*muH*mup^2*dn-muN^2*muH*mup*p0*dn-muN*muH*mup^2*p0*dn}, {mu*muN^2*n^2*mup*sigma*H+2*dp*mu*muN*n*mup^2*sigma*H+dp^2*mu*mup^3*sigma*H+mu*muN^2*n*mup*p0*sigma*H+2*mu*muN*n*mup^2*p0*sigma*H+dp*mu*mup^3*p0*sigma*H+mu*muN^3*n*dn*sigma*H+mu*muN^2*n*mup*dn*sigma*H-dp*mu*muN*mup^2*dn*sigma*H-dp*mu*mup^3*dn*sigma*H-mu*muN*mup^2*p0*dn*sigma*H-mu*mup^3*p0*dn*sigma*H+muN^4*muH*n*dn+muN^3*muH*n*mup*dn-dp*muN^2*muH*mup^2*dn-dp*muN*muH*mup^3*dn-muN^2*muH*mup^2*p0*dn-muN*muH*mup^3*p0*dn}, {muN*n^2*e*dn*beta^3+2*dp*muN*n*e*dn*beta^2+muN*n^2*e*dn*beta^2+2*muN*n*e*p0*dn*beta^2+dp^2*muN*e*dn*beta+2*dp*muN*n*e*dn*beta+2*dp*muN*e*p0*dn*beta+2*muN*n*e*p0*dn*beta+muN*e*p0^2*dn*beta-n*dn*beta^3*sigma+dp^2*muN*e*dn+2*dp*muN*e*p0*dn+muN*e*p0^2*dn-n^2*beta^2*sigma-n*p0*beta^2*sigma-n*dn*beta^2*sigma-2*dp*n*beta*sigma-2*n*p0*beta*sigma+dp*dn*beta*sigma+p0*dn*beta*sigma-dp^2*sigma-dp*p0*sigma+dp*dn*sigma+p0*dn*sigma}, {muN^2*n^2*e*dn*beta^2+2*dp*muN^2*n*e*dn*beta+muN^2*n^2*e*dn*beta+2*muN^2*n*e*p0*dn*beta+dp^2*muN^2*e*dn+2*dp*muN^2*n*e*dn+dp^2*muN*e*mup*dn+2*dp*muN^2*e*p0*dn+2*muN^2*n*e*p0*dn+2*dp*muN*e*mup*p0*dn+muN^2*e*p0^2*dn+muN*e*mup*p0^2*dn-muN*n*dn*beta^2*sigma-muN*n^2*beta*sigma-muN*n*p0*beta*sigma-muN*n*dn*beta*sigma-2*dp*muN*n*sigma-dp^2*mup*sigma-2*muN*n*p0*sigma-dp*mup*p0*sigma+dp*muN*dn*sigma+dp*mup*dn*sigma+muN*p0*dn*sigma+mup*p0*dn*sigma}, {muN^3*n^2*e*dn*beta+2*dp*muN^3*n*e*dn+muN^3*n^2*e*dn+dp^2*muN^2*e*mup*dn+2*dp*muN^2*n*e*mup*dn+dp^2*muN*e*mup^2*dn+2*muN^3*n*e*p0*dn+2*dp*muN^2*e*mup*p0*dn+2*muN^2*n*e*mup*p0*dn+2*dp*muN*e*mup^2*p0*dn+muN^2*e*mup*p0^2*dn+muN*e*mup^2*p0^2*dn-muN^2*n*dn*beta*sigma-muN^2*n^2*sigma-2*dp*muN*n*mup*sigma-dp^2*mup^2*sigma-muN^2*n*p0*sigma-2*muN*n*mup*p0*sigma-dp*mup^2*p0*sigma-muN^2*n*dn*sigma+dp*muN*mup*dn*sigma+dp*mup^2*dn*sigma+muN*mup*p0*dn*sigma+mup^2*p0*dn*sigma}, {muN^4*n^2*e*dn+2*dp*muN^3*n*e*mup*dn+muN^3*n^2*e*mup*dn+dp^2*muN^2*e*mup^2*dn+2*dp*muN^2*n*e*mup^2*dn+dp^2*muN*e*mup^3*dn+2*muN^3*n*e*mup*p0*dn+2*dp*muN^2*e*mup^2*p0*dn+2*muN^2*n*e*mup^2*p0*dn+2*dp*muN*e*mup^3*p0*dn+muN^2*e*mup^2*p0^2*dn+muN*e*mup^3*p0^2*dn-muN^2*n^2*mup*sigma-2*dp*muN*n*mup^2*sigma-dp^2*mup^3*sigma-muN^2*n*mup*p0*sigma-2*muN*n*mup^2*p0*sigma-dp*mup^3*p0*sigma-muN^3*n*dn*sigma-muN^2*n*mup*dn*sigma+dp*muN*mup^2*dn*sigma+dp*mup^3*dn*sigma+muN*mup^2*p0*dn*sigma+mup^3*p0*dn*sigma}, {r}, {e}, {muH}, {H}};

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
f = openOut "results/photoHall/abduction/noiseless/3_axiom(s)_removed/combo_4_5_6/reasoning/reasoning_output.txt";
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

print("Reasoning complete. Output written to results/photoHall/abduction/noiseless/3_axiom(s)_removed/combo_4_5_6/reasoning/reasoning_output.txt");
