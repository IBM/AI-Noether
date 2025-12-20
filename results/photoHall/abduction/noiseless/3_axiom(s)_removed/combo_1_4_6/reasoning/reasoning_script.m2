-- AI-Noether: Reasoning Template (Noiseless)
-- Tests if candidate axiom sets, when added to remaining axioms, prove targets

needsPackage("PrimaryDecomposition", Reload => true)

-- Ring definition
R = QQ[ph, dp, mu, muN, muH, n, dsigma2dn, e, mup, p0, dn, beta, r, sigma, H, MonomialOrder => Lex];

-- Input data
remainingAxioms = toList([muH - r * mu, ph - p0 - dp, dp - dn, H * (ph + beta * n)^2 * e - r * ph + r * beta^2 * n]);
qList = toList([r*e*mup*dn*beta^2 + r*e*mup*dn*beta - r*sigma + e*p0*sigma*H + e*dn*beta*sigma*H + e*dn*sigma*H]);
k = #qList;

-- Per-target variable partitions
measuredPerTarget = {{sigma, r, e, mup, p0, dn, beta, H}};
nonMeasuredPerTarget = {{ph, dp, mu, muN, muH, n, dsigma2dn}};

-- Candidate axiom sets to test (list of lists)
candidateSets = {{}, {e*mup*p0*dn*beta*r+e*mup*dn^2*beta*r-n^2*e*beta*sigma*H+e*mup*p0*dn*r+e*mup*dn^2*r-2*n*e*p0*sigma*H-2*n*e*dn*sigma*H+e*p0*dn*sigma*H+e*dn^2*sigma*H-n*beta*r*sigma}, {mu*n^2*e*beta*sigma*H-muH*e*mup*p0*dn*beta-muH*e*mup*dn^2*beta+2*mu*n*e*p0*sigma*H+2*mu*n*e*dn*sigma*H-mu*e*p0*dn*sigma*H-mu*e*dn^2*sigma*H-muH*e*mup*p0*dn-muH*e*mup*dn^2+muH*n*beta*sigma}, {n*mup*dn*beta^3*r+n*mup*dn*beta^2*r+n*dn*beta^2*sigma*H-mup*p0*dn*beta*r-mup*dn^2*beta*r+n^2*beta*sigma*H+n*p0*beta*sigma*H+n*dn*beta*sigma*H-mup*p0*dn*r-mup*dn^2*r+2*n*p0*sigma*H+2*n*dn*sigma*H-p0*dn*sigma*H-dn^2*sigma*H}, {muH*n*mup*dn*beta^3+mu*n*dn*beta^2*sigma*H+muH*n*mup*dn*beta^2+mu*n^2*beta*sigma*H+mu*n*p0*beta*sigma*H+mu*n*dn*beta*sigma*H-muH*mup*p0*dn*beta-muH*mup*dn^2*beta+2*mu*n*p0*sigma*H+2*mu*n*dn*sigma*H-mu*p0*dn*sigma*H-mu*dn^2*sigma*H-muH*mup*p0*dn-muH*mup*dn^2}, {n^2*e*mup*dn*beta*r*H-2*n^3*e*beta*sigma*H^2+n^2*e*dn*beta*sigma*H^2-n*mup*dn*beta^2*r^2+2*n*e*mup*p0*dn*r*H-e*mup*p0^2*dn*r*H+2*n*e*mup*dn^2*r*H-2*e*mup*p0*dn^2*r*H-e*mup*dn^3*r*H-3*n^2*e*p0*sigma*H^2-3*n^2*e*dn*sigma*H^2+2*n*e*p0*dn*sigma*H^2+2*n*e*dn^2*sigma*H^2-2*n^2*beta*r*sigma*H+mup*p0*dn*r^2+mup*dn^2*r^2-n^2*r*sigma*H}, {muH*n^2*e*mup*dn*beta*H-2*muH*n*e*mup*p0*dn*beta*H-2*muH*n*e*mup*dn^2*beta*H+muH*e*mup*p0*dn^2*beta*H+muH*e*mup*dn^3*beta*H+mu*n^2*e*p0*sigma*H^2+mu*n^2*e*dn*sigma*H^2-2*mu*n*e*p0*dn*sigma*H^2-2*mu*n*e*dn^2*sigma*H^2+mu*e*p0*dn^2*sigma*H^2+mu*e*dn^3*sigma*H^2-muH*n*mup*dn*beta^2*r-muH*e*mup*p0^2*dn*H-muH*e*mup*p0*dn^2*H-muH*n*dn*beta*sigma*H+muH*mup*p0*dn*r+muH*mup*dn^2*r-muH*n^2*sigma*H}, {n^2*e*mup*dn*beta^3+n^2*e*mup*dn*beta^2+2*n*e*mup*p0*dn*beta^2+2*n*e*mup*dn^2*beta^2+2*n*e*mup*p0*dn*beta+e*mup*p0^2*dn*beta+2*n*e*mup*dn^2*beta+2*e*mup*p0*dn^2*beta+e*mup*dn^3*beta+e*mup*p0^2*dn+2*e*mup*p0*dn^2+e*mup*dn^3-n*dn*beta^2*sigma-n^2*beta*sigma-n*p0*beta*sigma-n*dn*beta*sigma-2*n*p0*sigma-2*n*dn*sigma+p0*dn*sigma+dn^2*sigma}, {n^4*e*beta*sigma*H^2-2*n^3*e*p0*beta*sigma*H^2-2*n^3*e*dn*beta*sigma*H^2+n^2*e*p0*dn*beta*sigma*H^2+n^2*e*dn^2*beta*sigma*H^2-n*mup*p0*dn*beta^2*r^2-n*mup*dn^2*beta^2*r^2-n^2*e*mup*p0*dn*r*H+2*n*e*mup*p0^2*dn*r*H-e*mup*p0^3*dn*r*H-n^2*e*mup*dn^2*r*H+4*n*e*mup*p0*dn^2*r*H-3*e*mup*p0^2*dn^2*r*H+2*n*e*mup*dn^3*r*H-3*e*mup*p0*dn^3*r*H-e*mup*dn^4*r*H+2*n^3*e*p0*sigma*H^2-3*n^2*e*p0^2*sigma*H^2+2*n^3*e*dn*sigma*H^2-7*n^2*e*p0*dn*sigma*H^2+2*n*e*p0^2*dn*sigma*H^2-4*n^2*e*dn^2*sigma*H^2+4*n*e*p0*dn^2*sigma*H^2+2*n*e*dn^3*sigma*H^2+n^3*beta*r*sigma*H-2*n^2*p0*beta*r*sigma*H-2*n^2*dn*beta*r*sigma*H+mup*p0^2*dn*r^2+2*mup*p0*dn^2*r^2+mup*dn^3*r^2-n^2*p0*r*sigma*H-n^2*dn*r*sigma*H}, {2*mu*muH*n*e*mup*p0*dn*beta*sigma*H+2*mu*muH*n*e*mup*dn^2*beta*sigma*H-mu*muH*e*mup*p0*dn^2*beta*sigma*H-mu*muH*e*mup*dn^3*beta*sigma*H-mu^2*n^2*e*p0*sigma^2*H^2-mu^2*n^2*e*dn*sigma^2*H^2+2*mu^2*n*e*p0*dn*sigma^2*H^2+2*mu^2*n*e*dn^2*sigma^2*H^2-mu^2*e*p0*dn^2*sigma^2*H^2-mu^2*e*dn^3*sigma^2*H^2-muH^2*e*mup^2*p0*dn^2*beta-muH^2*e*mup^2*dn^3*beta+2*mu*muH*n*e*mup*p0*dn*sigma*H+mu*muH*e*mup*p0^2*dn*sigma*H+2*mu*muH*n*e*mup*dn^2*sigma*H-mu*muH*e*mup*dn^3*sigma*H-muH^2*e*mup^2*p0*dn^2-muH^2*e*mup^2*dn^3+muH^2*n*mup*dn*beta^2*sigma+mu*muH*n*dn*beta*sigma^2*H+muH^2*n*mup*dn*beta*sigma+mu*muH*n^2*sigma^2*H-muH^2*mup*p0*dn*sigma-muH^2*mup*dn^2*sigma}, {mu*muH*e*mup*p0*dn^3*beta*sigma*H+mu*muH*e*mup*dn^4*beta*sigma*H+2*mu^2*n^3*e*p0*sigma^2*H^2+2*mu^2*n^3*e*dn*sigma^2*H^2-3*mu^2*n^2*e*p0*dn*sigma^2*H^2-3*mu^2*n^2*e*dn^2*sigma^2*H^2+mu^2*e*p0*dn^3*sigma^2*H^2+mu^2*e*dn^4*sigma^2*H^2+2*muH^2*n*e*mup^2*p0*dn^2*beta-4*muH^2*e*mup^2*p0^2*dn^2*beta+2*muH^2*n*e*mup^2*dn^3*beta-7*muH^2*e*mup^2*p0*dn^3*beta-3*muH^2*e*mup^2*dn^4*beta-4*mu*muH*n^2*e*mup*p0*dn*sigma*H+6*mu*muH*n*e*mup*p0^2*dn*sigma*H-4*mu*muH*n^2*e*mup*dn^2*sigma*H+14*mu*muH*n*e*mup*p0*dn^2*sigma*H-5*mu*muH*e*mup*p0^2*dn^2*sigma*H+8*mu*muH*n*e*mup*dn^3*sigma*H-8*mu*muH*e*mup*p0*dn^3*sigma*H-3*mu*muH*e*mup*dn^4*sigma*H+2*muH^2*n*e*mup^2*p0*dn^2-4*muH^2*e*mup^2*p0^2*dn^2+2*muH^2*n*e*mup^2*dn^3-7*muH^2*e*mup^2*p0*dn^3-3*muH^2*e*mup^2*dn^4-2*muH^2*n^2*mup*dn*beta^2*sigma-muH^2*n*mup*dn^2*beta^2*sigma-2*mu*muH*n^2*dn*beta*sigma^2*H-mu*muH*n*dn^2*beta*sigma^2*H-2*muH^2*n^2*mup*dn*beta*sigma+4*muH^2*n*mup*p0*dn*beta*sigma+3*muH^2*n*mup*dn^2*beta*sigma-2*mu*muH*n^3*sigma^2*H-mu*muH*n^2*dn*sigma^2*H+2*muH^2*n*mup*p0*dn*sigma+2*muH^2*n*mup*dn^2*sigma+muH^2*mup*p0*dn^2*sigma+muH^2*mup*dn^3*sigma}, {n*mup^2*p0*dn^2*beta^2*r^3+n*mup^2*dn^3*beta^2*r^3+n^2*e*mup^2*p0*dn^2*r^2*H-2*n*e*mup^2*p0^2*dn^2*r^2*H+e*mup^2*p0^3*dn^2*r^2*H+n^2*e*mup^2*dn^3*r^2*H-4*n*e*mup^2*p0*dn^3*r^2*H+3*e*mup^2*p0^2*dn^3*r^2*H-2*n*e*mup^2*dn^4*r^2*H+3*e*mup^2*p0*dn^4*r^2*H+e*mup^2*dn^5*r^2*H-n^3*mup*dn*beta^2*r^2*sigma*H-2*n^3*e*mup*p0*dn*r*sigma*H^2+2*n^2*e*mup*p0^2*dn*r*sigma*H^2-2*n^3*e*mup*dn^2*r*sigma*H^2+6*n^2*e*mup*p0*dn^2*r*sigma*H^2-2*n*e*mup*p0^2*dn^2*r*sigma*H^2+4*n^2*e*mup*dn^3*r*sigma*H^2-4*n*e*mup*p0*dn^3*r*sigma*H^2-2*n*e*mup*dn^4*r*sigma*H^2+n^4*e*p0*sigma^2*H^3+n^4*e*dn*sigma^2*H^3-2*n^3*e*p0*dn*sigma^2*H^3-2*n^3*e*dn^2*sigma^2*H^3+n^2*e*p0*dn^2*sigma^2*H^3+n^2*e*dn^3*sigma^2*H^3-n^3*mup*dn*beta*r^2*sigma*H+2*n^2*mup*p0*dn*beta*r^2*sigma*H+2*n^2*mup*dn^2*beta*r^2*sigma*H-n^3*dn*beta*r*sigma^2*H^2-mup^2*p0^2*dn^2*r^3-2*mup^2*p0*dn^3*r^3-mup^2*dn^4*r^3+2*n^2*mup*p0*dn*r^2*sigma*H+2*n^2*mup*dn^2*r^2*sigma*H-n^4*r*sigma^2*H^2}, {mu*n^4*e*p0*sigma^2*H^3+mu*n^4*e*dn*sigma^2*H^3-2*mu*n^3*e*p0*dn*sigma^2*H^3-2*mu*n^3*e*dn^2*sigma^2*H^3+mu*n^2*e*p0*dn^2*sigma^2*H^3+mu*n^2*e*dn^3*sigma^2*H^3+muH*n*mup^2*p0*dn^2*beta^2*r^2+muH*n*mup^2*dn^3*beta^2*r^2+muH*n^2*e*mup^2*p0*dn^2*r*H-2*muH*n*e*mup^2*p0^2*dn^2*r*H+muH*e*mup^2*p0^3*dn^2*r*H+muH*n^2*e*mup^2*dn^3*r*H-4*muH*n*e*mup^2*p0*dn^3*r*H+3*muH*e*mup^2*p0^2*dn^3*r*H-2*muH*n*e*mup^2*dn^4*r*H+3*muH*e*mup^2*p0*dn^4*r*H+muH*e*mup^2*dn^5*r*H-muH*n^3*mup*dn*beta^2*r*sigma*H-2*muH*n^3*e*mup*p0*dn*sigma*H^2+2*muH*n^2*e*mup*p0^2*dn*sigma*H^2-2*muH*n^3*e*mup*dn^2*sigma*H^2+6*muH*n^2*e*mup*p0*dn^2*sigma*H^2-2*muH*n*e*mup*p0^2*dn^2*sigma*H^2+4*muH*n^2*e*mup*dn^3*sigma*H^2-4*muH*n*e*mup*p0*dn^3*sigma*H^2-2*muH*n*e*mup*dn^4*sigma*H^2-muH*n^3*mup*dn*beta*r*sigma*H+2*muH*n^2*mup*p0*dn*beta*r*sigma*H+2*muH*n^2*mup*dn^2*beta*r*sigma*H-muH*n^3*dn*beta*sigma^2*H^2-muH*mup^2*p0^2*dn^2*r^2-2*muH*mup^2*p0*dn^3*r^2-muH*mup^2*dn^4*r^2+2*muH*n^2*mup*p0*dn*r*sigma*H+2*muH*n^2*mup*dn^2*r*sigma*H-muH*n^4*sigma^2*H^2}, {mu^2*n^4*e*p0*sigma^2*H^2+mu^2*n^4*e*dn*sigma^2*H^2-2*mu^2*n^3*e*p0*dn*sigma^2*H^2-2*mu^2*n^3*e*dn^2*sigma^2*H^2+mu^2*n^2*e*p0*dn^2*sigma^2*H^2+mu^2*n^2*e*dn^3*sigma^2*H^2+muH^2*n^2*e*mup^2*p0*dn^2*beta-2*muH^2*n*e*mup^2*p0^2*dn^2*beta+muH^2*n^2*e*mup^2*dn^3*beta-4*muH^2*n*e*mup^2*p0*dn^3*beta+muH^2*e*mup^2*p0^2*dn^3*beta-2*muH^2*n*e*mup^2*dn^4*beta+2*muH^2*e*mup^2*p0*dn^4*beta+muH^2*e*mup^2*dn^5*beta-2*mu*muH*n^3*e*mup*p0*dn*sigma*H+3*mu*muH*n^2*e*mup*p0^2*dn*sigma*H-2*mu*muH*n^3*e*mup*dn^2*sigma*H+8*mu*muH*n^2*e*mup*p0*dn^2*sigma*H-4*mu*muH*n*e*mup*p0^2*dn^2*sigma*H+5*mu*muH*n^2*e*mup*dn^3*sigma*H-8*mu*muH*n*e*mup*p0*dn^3*sigma*H+mu*muH*e*mup*p0^2*dn^3*sigma*H-4*mu*muH*n*e*mup*dn^4*sigma*H+2*mu*muH*e*mup*p0*dn^4*sigma*H+mu*muH*e*mup*dn^5*sigma*H+muH^2*n^2*e*mup^2*p0*dn^2-2*muH^2*n*e*mup^2*p0^2*dn^2+muH^2*n^2*e*mup^2*dn^3-4*muH^2*n*e*mup^2*p0*dn^3+muH^2*e*mup^2*p0^2*dn^3-2*muH^2*n*e*mup^2*dn^4+2*muH^2*e*mup^2*p0*dn^4+muH^2*e*mup^2*dn^5-muH^2*n^3*mup*dn*beta^2*sigma-mu*muH*n^3*dn*beta*sigma^2*H-muH^2*n^3*mup*dn*beta*sigma+2*muH^2*n^2*mup*p0*dn*beta*sigma+2*muH^2*n^2*mup*dn^2*beta*sigma-muH^2*n*mup*p0*dn^2*beta*sigma-muH^2*n*mup*dn^3*beta*sigma-mu*muH*n^4*sigma^2*H+muH^2*n^2*mup*p0*dn*sigma+muH^2*n^2*mup*dn^2*sigma}, {n^2*e^2*mup^2*p0*dn^2*r^2*H-2*n*e^2*mup^2*p0^2*dn^2*r^2*H+e^2*mup^2*p0^3*dn^2*r^2*H+n^2*e^2*mup^2*dn^3*r^2*H-4*n*e^2*mup^2*p0*dn^3*r^2*H+3*e^2*mup^2*p0^2*dn^3*r^2*H-2*n*e^2*mup^2*dn^4*r^2*H+3*e^2*mup^2*p0*dn^4*r^2*H+e^2*mup^2*dn^5*r^2*H-2*n^3*e^2*mup*p0*dn*r*sigma*H^2+2*n^2*e^2*mup*p0^2*dn*r*sigma*H^2-2*n^3*e^2*mup*dn^2*r*sigma*H^2+6*n^2*e^2*mup*p0*dn^2*r*sigma*H^2-2*n*e^2*mup*p0^2*dn^2*r*sigma*H^2+4*n^2*e^2*mup*dn^3*r*sigma*H^2-4*n*e^2*mup*p0*dn^3*r*sigma*H^2-2*n*e^2*mup*dn^4*r*sigma*H^2+n^4*e^2*p0*sigma^2*H^3+n^4*e^2*dn*sigma^2*H^3-2*n^3*e^2*p0*dn*sigma^2*H^3-2*n^3*e^2*dn^2*sigma^2*H^3+n^2*e^2*p0*dn^2*sigma^2*H^3+n^2*e^2*dn^3*sigma^2*H^3+n*e*mup^2*p0*dn^2*r^3-e*mup^2*p0^2*dn^2*r^3+n*e*mup^2*dn^3*r^3-2*e*mup^2*p0*dn^3*r^3-e*mup^2*dn^4*r^3-n^2*mup*dn*beta^2*r^3*sigma-2*n*e*mup*p0^2*dn*r^2*sigma*H-2*n*e*mup*p0*dn^2*r^2*sigma*H-n^4*e*r*sigma^2*H^2+2*n^3*e*p0*r*sigma^2*H^2+2*n^3*e*dn*r*sigma^2*H^2-2*n^2*e*p0*dn*r*sigma^2*H^2-2*n^2*e*dn^2*r*sigma^2*H^2+n*e*p0*dn^2*r*sigma^2*H^2+n*e*dn^3*r*sigma^2*H^2-n^2*mup*dn*beta*r^3*sigma-n^2*dn*beta*r^2*sigma^2*H+2*n*mup*p0*dn*r^3*sigma+2*n*mup*dn^2*r^3*sigma-2*n^3*r^2*sigma^2*H}, {H}, {r}, {muH}, {e}, {beta}, {e*p0*H+e*dn*H-r}};

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
f = openOut "results/photoHall/abduction/noiseless/3_axiom(s)_removed/combo_1_4_6/reasoning/reasoning_output.txt";
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

print("Reasoning complete. Output written to results/photoHall/abduction/noiseless/3_axiom(s)_removed/combo_1_4_6/reasoning/reasoning_output.txt");
