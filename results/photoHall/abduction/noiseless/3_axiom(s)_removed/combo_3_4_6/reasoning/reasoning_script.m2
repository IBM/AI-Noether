-- AI-Noether: Reasoning Template (Noiseless)
-- Tests if candidate axiom sets, when added to remaining axioms, prove targets

needsPackage("PrimaryDecomposition", Reload => true)

-- Ring definition
R = QQ[ph, dp, mu, muN, muH, n, dsigma2dn, e, mup, p0, dn, beta, r, sigma, H, MonomialOrder => Lex];

-- Input data
remainingAxioms = toList([beta * mup - muN, muH - r * mu, dp - dn, H * (ph + beta * n)^2 * e - r * ph + r * beta^2 * n]);
qList = toList([r*e*mup*dn*beta^2 + r*e*mup*dn*beta - r*sigma + e*p0*sigma*H + e*dn*beta*sigma*H + e*dn*sigma*H]);
k = #qList;

-- Per-target variable partitions
measuredPerTarget = {{sigma, r, e, mup, p0, dn, beta, H}};
nonMeasuredPerTarget = {{ph, dp, mu, muN, muH, n, dsigma2dn}};

-- Candidate axiom sets to test (list of lists)
candidateSets = {{}, {muN*n*dn*beta^3*r+n*dn*beta^3*sigma*H+muN*n*dn*beta^2*r+n^2*beta^2*sigma*H+n*p0*beta^2*sigma*H+n*dn*beta^2*sigma*H-ph*muN*dn*beta*r+2*ph*n*beta*sigma*H-ph*dn*beta*sigma*H-ph*muN*dn*r+ph^2*sigma*H-ph*p0*sigma*H-ph*dn*sigma*H}, {muN^2*n*dn*beta^2*r+muN*n*dn*beta^2*sigma*H+muN^2*n*dn*beta*r+muN*n^2*beta*sigma*H+muN*n*p0*beta*sigma*H+muN*n*dn*beta*sigma*H-ph*muN^2*dn*r-ph*muN*mup*dn*r+2*ph*muN*n*sigma*H+ph^2*mup*sigma*H-ph*mup*p0*sigma*H-ph*muN*dn*sigma*H-ph*mup*dn*sigma*H}, {muN^3*n*dn*beta*r+muN^2*n*dn*beta*sigma*H+muN^3*n*dn*r-ph*muN^2*mup*dn*r-ph*muN*mup^2*dn*r+muN^2*n^2*sigma*H+2*ph*muN*n*mup*sigma*H+ph^2*mup^2*sigma*H+muN^2*n*p0*sigma*H-ph*mup^2*p0*sigma*H+muN^2*n*dn*sigma*H-ph*muN*mup*dn*sigma*H-ph*mup^2*dn*sigma*H}, {muN^4*n*dn*r+muN^3*n*mup*dn*r-ph*muN^2*mup^2*dn*r-ph*muN*mup^3*dn*r+muN^2*n^2*mup*sigma*H+2*ph*muN*n*mup^2*sigma*H+ph^2*mup^3*sigma*H+muN^2*n*mup*p0*sigma*H-ph*mup^3*p0*sigma*H+muN^3*n*dn*sigma*H+muN^2*n*mup*dn*sigma*H-ph*muN*mup^2*dn*sigma*H-ph*mup^3*dn*sigma*H}, {mu*n*dn*beta^3*sigma*H+muN*muH*n*dn*beta^3+mu*n^2*beta^2*sigma*H+mu*n*p0*beta^2*sigma*H+mu*n*dn*beta^2*sigma*H+muN*muH*n*dn*beta^2+2*ph*mu*n*beta*sigma*H-ph*mu*dn*beta*sigma*H-ph*muN*muH*dn*beta+ph^2*mu*sigma*H-ph*mu*p0*sigma*H-ph*mu*dn*sigma*H-ph*muN*muH*dn}, {mu*muN*n*dn*beta^2*sigma*H+muN^2*muH*n*dn*beta^2+mu*muN*n^2*beta*sigma*H+mu*muN*n*p0*beta*sigma*H+mu*muN*n*dn*beta*sigma*H+muN^2*muH*n*dn*beta+2*ph*mu*muN*n*sigma*H+ph^2*mu*mup*sigma*H-ph*mu*mup*p0*sigma*H-ph*mu*muN*dn*sigma*H-ph*mu*mup*dn*sigma*H-ph*muN^2*muH*dn-ph*muN*muH*mup*dn}, {mu*muN^2*n*dn*beta*sigma*H+muN^3*muH*n*dn*beta+mu*muN^2*n^2*sigma*H+2*ph*mu*muN*n*mup*sigma*H+ph^2*mu*mup^2*sigma*H+mu*muN^2*n*p0*sigma*H-ph*mu*mup^2*p0*sigma*H+mu*muN^2*n*dn*sigma*H-ph*mu*muN*mup*dn*sigma*H-ph*mu*mup^2*dn*sigma*H+muN^3*muH*n*dn-ph*muN^2*muH*mup*dn-ph*muN*muH*mup^2*dn}, {mu*muN^2*n^2*mup*sigma*H+2*ph*mu*muN*n*mup^2*sigma*H+ph^2*mu*mup^3*sigma*H+mu*muN^2*n*mup*p0*sigma*H-ph*mu*mup^3*p0*sigma*H+mu*muN^3*n*dn*sigma*H+mu*muN^2*n*mup*dn*sigma*H-ph*mu*muN*mup^2*dn*sigma*H-ph*mu*mup^3*dn*sigma*H+muN^4*muH*n*dn+muN^3*muH*n*mup*dn-ph*muN^2*muH*mup^2*dn-ph*muN*muH*mup^3*dn}, {muN*n^2*e*dn*beta^3+2*ph*muN*n*e*dn*beta^2+muN*n^2*e*dn*beta^2+ph^2*muN*e*dn*beta+2*ph*muN*n*e*dn*beta-n*dn*beta^3*sigma+ph^2*muN*e*dn-n^2*beta^2*sigma-n*p0*beta^2*sigma-n*dn*beta^2*sigma-2*ph*n*beta*sigma+ph*dn*beta*sigma-ph^2*sigma+ph*p0*sigma+ph*dn*sigma}, {muN^2*n^2*e*dn*beta^2+2*ph*muN^2*n*e*dn*beta+muN^2*n^2*e*dn*beta+ph^2*muN^2*e*dn+2*ph*muN^2*n*e*dn+ph^2*muN*e*mup*dn-muN*n*dn*beta^2*sigma-muN*n^2*beta*sigma-muN*n*p0*beta*sigma-muN*n*dn*beta*sigma-2*ph*muN*n*sigma-ph^2*mup*sigma+ph*mup*p0*sigma+ph*muN*dn*sigma+ph*mup*dn*sigma}, {muN^3*n^2*e*dn*beta+2*ph*muN^3*n*e*dn+muN^3*n^2*e*dn+ph^2*muN^2*e*mup*dn+2*ph*muN^2*n*e*mup*dn+ph^2*muN*e*mup^2*dn-muN^2*n*dn*beta*sigma-muN^2*n^2*sigma-2*ph*muN*n*mup*sigma-ph^2*mup^2*sigma-muN^2*n*p0*sigma+ph*mup^2*p0*sigma-muN^2*n*dn*sigma+ph*muN*mup*dn*sigma+ph*mup^2*dn*sigma}, {muN^4*n^2*e*dn+2*ph*muN^3*n*e*mup*dn+muN^3*n^2*e*mup*dn+ph^2*muN^2*e*mup^2*dn+2*ph*muN^2*n*e*mup^2*dn+ph^2*muN*e*mup^3*dn-muN^2*n^2*mup*sigma-2*ph*muN*n*mup^2*sigma-ph^2*mup^3*sigma-muN^2*n*mup*p0*sigma+ph*mup^3*p0*sigma-muN^3*n*dn*sigma-muN^2*n*mup*dn*sigma+ph*muN*mup^2*dn*sigma+ph*mup^3*dn*sigma}, {r}, {e}, {muH}, {H}};

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
f = openOut "results/photoHall/abduction/noiseless/3_axiom(s)_removed/combo_3_4_6/reasoning/reasoning_output.txt";
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

print("Reasoning complete. Output written to results/photoHall/abduction/noiseless/3_axiom(s)_removed/combo_3_4_6/reasoning/reasoning_output.txt");
