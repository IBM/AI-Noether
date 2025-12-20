-- AI-Noether: Reasoning Template (Noiseless)
-- Tests if candidate axiom sets, when added to remaining axioms, prove targets

needsPackage("PrimaryDecomposition", Reload => true)

-- Ring definition
R = QQ[ph, dp, mu, muN, muH, n, dsigma2dn, e, mup, p0, dn, beta, r, sigma, H, MonomialOrder => Lex];

-- Input data
remainingAxioms = toList([beta * mup - muN, muH - r * mu, n - dn, dp - dn, sigma - e * ph * mup - e * n * muN, H * (ph + beta * n)^2 * e - r * ph + r * beta^2 * n]);
qList = toList([r*e*mup*dn*beta^2 + r*e*mup*dn*beta - r*sigma + e*p0*sigma*H + e*dn*beta*sigma*H + e*dn*sigma*H]);
k = #qList;

-- Per-target variable partitions
measuredPerTarget = {{sigma, r, e, mup, p0, dn, beta, H}};
nonMeasuredPerTarget = {{ph, dp, mu, muN, muH, n, dsigma2dn}};

-- Candidate axiom sets to test (list of lists)
candidateSets = {{}, {n-dn}, {dp-dn}, {ph-p0-dn}, {mu*r-muH}, {mup*beta-muN}, {e*mup*p0+muN*e*dn+e*mup*dn-sigma}, {muN*dn*beta*r+dn*beta*sigma*H-mup*p0*r-mup*dn*r+p0*sigma*H+dn*sigma*H}, {mup^2*p0*r-muN^2*dn*r+mup^2*dn*r-mup*p0*sigma*H-muN*dn*sigma*H-mup*dn*sigma*H}, {muN*e*dn*beta+muN*e*p0+muN*e*dn-beta*sigma}, {e*dn*beta*sigma*H-muN*e*p0*r+e*p0*sigma*H+e*dn*sigma*H+beta*r*sigma-r*sigma}, {mu*dn*beta*sigma*H+muN*muH*dn*beta+mu*p0*sigma*H+mu*dn*sigma*H-muH*mup*p0-muH*mup*dn}, {mu*mup*p0*sigma*H+mu*muN*dn*sigma*H+mu*mup*dn*sigma*H-muH*mup^2*p0+muN^2*muH*dn-muH*mup^2*dn}, {muN^2*e*dn*r+muN*e*mup*dn*r-mup*r*sigma+sigma^2*H}, {muN^2*e*p0*r-muN*beta*r*sigma-beta*sigma^2*H+muN*r*sigma}, {muN^2*muH*e*dn+muN*muH*e*mup*dn+mu*sigma^2*H-muH*mup*sigma}, {muN^2*muH*e*p0-mu*beta*sigma^2*H-muN*muH*beta*sigma+muN*muH*sigma}, {e*dn^2*beta^2*H+2*e*p0*dn*beta*H+2*e*dn^2*beta*H+dn*beta^2*r+e*p0^2*H+2*e*p0*dn*H+e*dn^2*H-p0*r-dn*r}, {n-dn, dp-dn}, {n-dn, ph-p0-dn}, {n-dn, mu*r-muH}, {n-dn, mup*beta-muN}, {n-dn, e*mup*p0+muN*e*dn+e*mup*dn-sigma}, {n-dn, muN*dn*beta*r+dn*beta*sigma*H-mup*p0*r-mup*dn*r+p0*sigma*H+dn*sigma*H}, {n-dn, mup^2*p0*r-muN^2*dn*r+mup^2*dn*r-mup*p0*sigma*H-muN*dn*sigma*H-mup*dn*sigma*H}, {n-dn, muN*e*dn*beta+muN*e*p0+muN*e*dn-beta*sigma}, {n-dn, e*dn*beta*sigma*H-muN*e*p0*r+e*p0*sigma*H+e*dn*sigma*H+beta*r*sigma-r*sigma}, {n-dn, mu*dn*beta*sigma*H+muN*muH*dn*beta+mu*p0*sigma*H+mu*dn*sigma*H-muH*mup*p0-muH*mup*dn}, {n-dn, mu*mup*p0*sigma*H+mu*muN*dn*sigma*H+mu*mup*dn*sigma*H-muH*mup^2*p0+muN^2*muH*dn-muH*mup^2*dn}, {n-dn, muN^2*e*dn*r+muN*e*mup*dn*r-mup*r*sigma+sigma^2*H}, {n-dn, muN^2*e*p0*r-muN*beta*r*sigma-beta*sigma^2*H+muN*r*sigma}, {n-dn, muN^2*muH*e*dn+muN*muH*e*mup*dn+mu*sigma^2*H-muH*mup*sigma}, {n-dn, muN^2*muH*e*p0-mu*beta*sigma^2*H-muN*muH*beta*sigma+muN*muH*sigma}, {n-dn, e*dn^2*beta^2*H+2*e*p0*dn*beta*H+2*e*dn^2*beta*H+dn*beta^2*r+e*p0^2*H+2*e*p0*dn*H+e*dn^2*H-p0*r-dn*r}, {dp-dn, ph-p0-dn}, {dp-dn, mu*r-muH}, {dp-dn, mup*beta-muN}, {dp-dn, e*mup*p0+muN*e*dn+e*mup*dn-sigma}, {dp-dn, muN*dn*beta*r+dn*beta*sigma*H-mup*p0*r-mup*dn*r+p0*sigma*H+dn*sigma*H}, {dp-dn, mup^2*p0*r-muN^2*dn*r+mup^2*dn*r-mup*p0*sigma*H-muN*dn*sigma*H-mup*dn*sigma*H}, {dp-dn, muN*e*dn*beta+muN*e*p0+muN*e*dn-beta*sigma}, {dp-dn, e*dn*beta*sigma*H-muN*e*p0*r+e*p0*sigma*H+e*dn*sigma*H+beta*r*sigma-r*sigma}, {dp-dn, mu*dn*beta*sigma*H+muN*muH*dn*beta+mu*p0*sigma*H+mu*dn*sigma*H-muH*mup*p0-muH*mup*dn}, {dp-dn, mu*mup*p0*sigma*H+mu*muN*dn*sigma*H+mu*mup*dn*sigma*H-muH*mup^2*p0+muN^2*muH*dn-muH*mup^2*dn}, {dp-dn, muN^2*e*dn*r+muN*e*mup*dn*r-mup*r*sigma+sigma^2*H}, {dp-dn, muN^2*e*p0*r-muN*beta*r*sigma-beta*sigma^2*H+muN*r*sigma}, {dp-dn, muN^2*muH*e*dn+muN*muH*e*mup*dn+mu*sigma^2*H-muH*mup*sigma}, {dp-dn, muN^2*muH*e*p0-mu*beta*sigma^2*H-muN*muH*beta*sigma+muN*muH*sigma}, {dp-dn, e*dn^2*beta^2*H+2*e*p0*dn*beta*H+2*e*dn^2*beta*H+dn*beta^2*r+e*p0^2*H+2*e*p0*dn*H+e*dn^2*H-p0*r-dn*r}, {ph-p0-dn, mu*r-muH}, {ph-p0-dn, mup*beta-muN}, {ph-p0-dn, e*mup*p0+muN*e*dn+e*mup*dn-sigma}, {ph-p0-dn, muN*dn*beta*r+dn*beta*sigma*H-mup*p0*r-mup*dn*r+p0*sigma*H+dn*sigma*H}, {ph-p0-dn, mup^2*p0*r-muN^2*dn*r+mup^2*dn*r-mup*p0*sigma*H-muN*dn*sigma*H-mup*dn*sigma*H}, {ph-p0-dn, muN*e*dn*beta+muN*e*p0+muN*e*dn-beta*sigma}, {ph-p0-dn, e*dn*beta*sigma*H-muN*e*p0*r+e*p0*sigma*H+e*dn*sigma*H+beta*r*sigma-r*sigma}, {ph-p0-dn, mu*dn*beta*sigma*H+muN*muH*dn*beta+mu*p0*sigma*H+mu*dn*sigma*H-muH*mup*p0-muH*mup*dn}, {ph-p0-dn, mu*mup*p0*sigma*H+mu*muN*dn*sigma*H+mu*mup*dn*sigma*H-muH*mup^2*p0+muN^2*muH*dn-muH*mup^2*dn}, {ph-p0-dn, muN^2*e*dn*r+muN*e*mup*dn*r-mup*r*sigma+sigma^2*H}, {ph-p0-dn, muN^2*e*p0*r-muN*beta*r*sigma-beta*sigma^2*H+muN*r*sigma}, {ph-p0-dn, muN^2*muH*e*dn+muN*muH*e*mup*dn+mu*sigma^2*H-muH*mup*sigma}, {ph-p0-dn, muN^2*muH*e*p0-mu*beta*sigma^2*H-muN*muH*beta*sigma+muN*muH*sigma}, {ph-p0-dn, e*dn^2*beta^2*H+2*e*p0*dn*beta*H+2*e*dn^2*beta*H+dn*beta^2*r+e*p0^2*H+2*e*p0*dn*H+e*dn^2*H-p0*r-dn*r}, {mu*r-muH, mup*beta-muN}, {mu*r-muH, e*mup*p0+muN*e*dn+e*mup*dn-sigma}, {mu*r-muH, muN*dn*beta*r+dn*beta*sigma*H-mup*p0*r-mup*dn*r+p0*sigma*H+dn*sigma*H}, {mu*r-muH, mup^2*p0*r-muN^2*dn*r+mup^2*dn*r-mup*p0*sigma*H-muN*dn*sigma*H-mup*dn*sigma*H}, {mu*r-muH, muN*e*dn*beta+muN*e*p0+muN*e*dn-beta*sigma}, {mu*r-muH, e*dn*beta*sigma*H-muN*e*p0*r+e*p0*sigma*H+e*dn*sigma*H+beta*r*sigma-r*sigma}, {mu*r-muH, mu*dn*beta*sigma*H+muN*muH*dn*beta+mu*p0*sigma*H+mu*dn*sigma*H-muH*mup*p0-muH*mup*dn}, {mu*r-muH, mu*mup*p0*sigma*H+mu*muN*dn*sigma*H+mu*mup*dn*sigma*H-muH*mup^2*p0+muN^2*muH*dn-muH*mup^2*dn}, {mu*r-muH, muN^2*e*dn*r+muN*e*mup*dn*r-mup*r*sigma+sigma^2*H}, {mu*r-muH, muN^2*e*p0*r-muN*beta*r*sigma-beta*sigma^2*H+muN*r*sigma}, {mu*r-muH, muN^2*muH*e*dn+muN*muH*e*mup*dn+mu*sigma^2*H-muH*mup*sigma}, {mu*r-muH, muN^2*muH*e*p0-mu*beta*sigma^2*H-muN*muH*beta*sigma+muN*muH*sigma}, {mu*r-muH, e*dn^2*beta^2*H+2*e*p0*dn*beta*H+2*e*dn^2*beta*H+dn*beta^2*r+e*p0^2*H+2*e*p0*dn*H+e*dn^2*H-p0*r-dn*r}, {mup*beta-muN, e*mup*p0+muN*e*dn+e*mup*dn-sigma}, {mup*beta-muN, muN*dn*beta*r+dn*beta*sigma*H-mup*p0*r-mup*dn*r+p0*sigma*H+dn*sigma*H}, {mup*beta-muN, mup^2*p0*r-muN^2*dn*r+mup^2*dn*r-mup*p0*sigma*H-muN*dn*sigma*H-mup*dn*sigma*H}, {mup*beta-muN, muN*e*dn*beta+muN*e*p0+muN*e*dn-beta*sigma}, {mup*beta-muN, e*dn*beta*sigma*H-muN*e*p0*r+e*p0*sigma*H+e*dn*sigma*H+beta*r*sigma-r*sigma}, {mup*beta-muN, mu*dn*beta*sigma*H+muN*muH*dn*beta+mu*p0*sigma*H+mu*dn*sigma*H-muH*mup*p0-muH*mup*dn}, {mup*beta-muN, mu*mup*p0*sigma*H+mu*muN*dn*sigma*H+mu*mup*dn*sigma*H-muH*mup^2*p0+muN^2*muH*dn-muH*mup^2*dn}, {mup*beta-muN, muN^2*e*dn*r+muN*e*mup*dn*r-mup*r*sigma+sigma^2*H}, {mup*beta-muN, muN^2*e*p0*r-muN*beta*r*sigma-beta*sigma^2*H+muN*r*sigma}, {mup*beta-muN, muN^2*muH*e*dn+muN*muH*e*mup*dn+mu*sigma^2*H-muH*mup*sigma}, {mup*beta-muN, muN^2*muH*e*p0-mu*beta*sigma^2*H-muN*muH*beta*sigma+muN*muH*sigma}, {mup*beta-muN, e*dn^2*beta^2*H+2*e*p0*dn*beta*H+2*e*dn^2*beta*H+dn*beta^2*r+e*p0^2*H+2*e*p0*dn*H+e*dn^2*H-p0*r-dn*r}, {e*mup*p0+muN*e*dn+e*mup*dn-sigma, muN*dn*beta*r+dn*beta*sigma*H-mup*p0*r-mup*dn*r+p0*sigma*H+dn*sigma*H}, {e*mup*p0+muN*e*dn+e*mup*dn-sigma, mup^2*p0*r-muN^2*dn*r+mup^2*dn*r-mup*p0*sigma*H-muN*dn*sigma*H-mup*dn*sigma*H}, {e*mup*p0+muN*e*dn+e*mup*dn-sigma, muN*e*dn*beta+muN*e*p0+muN*e*dn-beta*sigma}, {e*mup*p0+muN*e*dn+e*mup*dn-sigma, e*dn*beta*sigma*H-muN*e*p0*r+e*p0*sigma*H+e*dn*sigma*H+beta*r*sigma-r*sigma}, {e*mup*p0+muN*e*dn+e*mup*dn-sigma, mu*dn*beta*sigma*H+muN*muH*dn*beta+mu*p0*sigma*H+mu*dn*sigma*H-muH*mup*p0-muH*mup*dn}, {e*mup*p0+muN*e*dn+e*mup*dn-sigma, mu*mup*p0*sigma*H+mu*muN*dn*sigma*H+mu*mup*dn*sigma*H-muH*mup^2*p0+muN^2*muH*dn-muH*mup^2*dn}, {e*mup*p0+muN*e*dn+e*mup*dn-sigma, muN^2*e*dn*r+muN*e*mup*dn*r-mup*r*sigma+sigma^2*H}, {e*mup*p0+muN*e*dn+e*mup*dn-sigma, muN^2*e*p0*r-muN*beta*r*sigma-beta*sigma^2*H+muN*r*sigma}, {e*mup*p0+muN*e*dn+e*mup*dn-sigma, muN^2*muH*e*dn+muN*muH*e*mup*dn+mu*sigma^2*H-muH*mup*sigma}, {e*mup*p0+muN*e*dn+e*mup*dn-sigma, muN^2*muH*e*p0-mu*beta*sigma^2*H-muN*muH*beta*sigma+muN*muH*sigma}, {e*mup*p0+muN*e*dn+e*mup*dn-sigma, e*dn^2*beta^2*H+2*e*p0*dn*beta*H+2*e*dn^2*beta*H+dn*beta^2*r+e*p0^2*H+2*e*p0*dn*H+e*dn^2*H-p0*r-dn*r}, {muN*dn*beta*r+dn*beta*sigma*H-mup*p0*r-mup*dn*r+p0*sigma*H+dn*sigma*H, mup^2*p0*r-muN^2*dn*r+mup^2*dn*r-mup*p0*sigma*H-muN*dn*sigma*H-mup*dn*sigma*H}, {muN*dn*beta*r+dn*beta*sigma*H-mup*p0*r-mup*dn*r+p0*sigma*H+dn*sigma*H, muN*e*dn*beta+muN*e*p0+muN*e*dn-beta*sigma}, {muN*dn*beta*r+dn*beta*sigma*H-mup*p0*r-mup*dn*r+p0*sigma*H+dn*sigma*H, e*dn*beta*sigma*H-muN*e*p0*r+e*p0*sigma*H+e*dn*sigma*H+beta*r*sigma-r*sigma}, {muN*dn*beta*r+dn*beta*sigma*H-mup*p0*r-mup*dn*r+p0*sigma*H+dn*sigma*H, mu*dn*beta*sigma*H+muN*muH*dn*beta+mu*p0*sigma*H+mu*dn*sigma*H-muH*mup*p0-muH*mup*dn}, {muN*dn*beta*r+dn*beta*sigma*H-mup*p0*r-mup*dn*r+p0*sigma*H+dn*sigma*H, mu*mup*p0*sigma*H+mu*muN*dn*sigma*H+mu*mup*dn*sigma*H-muH*mup^2*p0+muN^2*muH*dn-muH*mup^2*dn}, {muN*dn*beta*r+dn*beta*sigma*H-mup*p0*r-mup*dn*r+p0*sigma*H+dn*sigma*H, muN^2*e*dn*r+muN*e*mup*dn*r-mup*r*sigma+sigma^2*H}, {muN*dn*beta*r+dn*beta*sigma*H-mup*p0*r-mup*dn*r+p0*sigma*H+dn*sigma*H, muN^2*e*p0*r-muN*beta*r*sigma-beta*sigma^2*H+muN*r*sigma}, {muN*dn*beta*r+dn*beta*sigma*H-mup*p0*r-mup*dn*r+p0*sigma*H+dn*sigma*H, muN^2*muH*e*dn+muN*muH*e*mup*dn+mu*sigma^2*H-muH*mup*sigma}, {muN*dn*beta*r+dn*beta*sigma*H-mup*p0*r-mup*dn*r+p0*sigma*H+dn*sigma*H, muN^2*muH*e*p0-mu*beta*sigma^2*H-muN*muH*beta*sigma+muN*muH*sigma}, {muN*dn*beta*r+dn*beta*sigma*H-mup*p0*r-mup*dn*r+p0*sigma*H+dn*sigma*H, e*dn^2*beta^2*H+2*e*p0*dn*beta*H+2*e*dn^2*beta*H+dn*beta^2*r+e*p0^2*H+2*e*p0*dn*H+e*dn^2*H-p0*r-dn*r}, {mup^2*p0*r-muN^2*dn*r+mup^2*dn*r-mup*p0*sigma*H-muN*dn*sigma*H-mup*dn*sigma*H, muN*e*dn*beta+muN*e*p0+muN*e*dn-beta*sigma}, {mup^2*p0*r-muN^2*dn*r+mup^2*dn*r-mup*p0*sigma*H-muN*dn*sigma*H-mup*dn*sigma*H, e*dn*beta*sigma*H-muN*e*p0*r+e*p0*sigma*H+e*dn*sigma*H+beta*r*sigma-r*sigma}, {mup^2*p0*r-muN^2*dn*r+mup^2*dn*r-mup*p0*sigma*H-muN*dn*sigma*H-mup*dn*sigma*H, mu*dn*beta*sigma*H+muN*muH*dn*beta+mu*p0*sigma*H+mu*dn*sigma*H-muH*mup*p0-muH*mup*dn}, {mup^2*p0*r-muN^2*dn*r+mup^2*dn*r-mup*p0*sigma*H-muN*dn*sigma*H-mup*dn*sigma*H, mu*mup*p0*sigma*H+mu*muN*dn*sigma*H+mu*mup*dn*sigma*H-muH*mup^2*p0+muN^2*muH*dn-muH*mup^2*dn}, {mup^2*p0*r-muN^2*dn*r+mup^2*dn*r-mup*p0*sigma*H-muN*dn*sigma*H-mup*dn*sigma*H, muN^2*e*dn*r+muN*e*mup*dn*r-mup*r*sigma+sigma^2*H}, {mup^2*p0*r-muN^2*dn*r+mup^2*dn*r-mup*p0*sigma*H-muN*dn*sigma*H-mup*dn*sigma*H, muN^2*e*p0*r-muN*beta*r*sigma-beta*sigma^2*H+muN*r*sigma}, {mup^2*p0*r-muN^2*dn*r+mup^2*dn*r-mup*p0*sigma*H-muN*dn*sigma*H-mup*dn*sigma*H, muN^2*muH*e*dn+muN*muH*e*mup*dn+mu*sigma^2*H-muH*mup*sigma}, {mup^2*p0*r-muN^2*dn*r+mup^2*dn*r-mup*p0*sigma*H-muN*dn*sigma*H-mup*dn*sigma*H, muN^2*muH*e*p0-mu*beta*sigma^2*H-muN*muH*beta*sigma+muN*muH*sigma}, {mup^2*p0*r-muN^2*dn*r+mup^2*dn*r-mup*p0*sigma*H-muN*dn*sigma*H-mup*dn*sigma*H, e*dn^2*beta^2*H+2*e*p0*dn*beta*H+2*e*dn^2*beta*H+dn*beta^2*r+e*p0^2*H+2*e*p0*dn*H+e*dn^2*H-p0*r-dn*r}, {muN*e*dn*beta+muN*e*p0+muN*e*dn-beta*sigma, e*dn*beta*sigma*H-muN*e*p0*r+e*p0*sigma*H+e*dn*sigma*H+beta*r*sigma-r*sigma}, {muN*e*dn*beta+muN*e*p0+muN*e*dn-beta*sigma, mu*dn*beta*sigma*H+muN*muH*dn*beta+mu*p0*sigma*H+mu*dn*sigma*H-muH*mup*p0-muH*mup*dn}, {muN*e*dn*beta+muN*e*p0+muN*e*dn-beta*sigma, mu*mup*p0*sigma*H+mu*muN*dn*sigma*H+mu*mup*dn*sigma*H-muH*mup^2*p0+muN^2*muH*dn-muH*mup^2*dn}, {muN*e*dn*beta+muN*e*p0+muN*e*dn-beta*sigma, muN^2*e*dn*r+muN*e*mup*dn*r-mup*r*sigma+sigma^2*H}, {muN*e*dn*beta+muN*e*p0+muN*e*dn-beta*sigma, muN^2*e*p0*r-muN*beta*r*sigma-beta*sigma^2*H+muN*r*sigma}, {muN*e*dn*beta+muN*e*p0+muN*e*dn-beta*sigma, muN^2*muH*e*dn+muN*muH*e*mup*dn+mu*sigma^2*H-muH*mup*sigma}, {muN*e*dn*beta+muN*e*p0+muN*e*dn-beta*sigma, muN^2*muH*e*p0-mu*beta*sigma^2*H-muN*muH*beta*sigma+muN*muH*sigma}, {muN*e*dn*beta+muN*e*p0+muN*e*dn-beta*sigma, e*dn^2*beta^2*H+2*e*p0*dn*beta*H+2*e*dn^2*beta*H+dn*beta^2*r+e*p0^2*H+2*e*p0*dn*H+e*dn^2*H-p0*r-dn*r}, {e*dn*beta*sigma*H-muN*e*p0*r+e*p0*sigma*H+e*dn*sigma*H+beta*r*sigma-r*sigma, mu*dn*beta*sigma*H+muN*muH*dn*beta+mu*p0*sigma*H+mu*dn*sigma*H-muH*mup*p0-muH*mup*dn}, {e*dn*beta*sigma*H-muN*e*p0*r+e*p0*sigma*H+e*dn*sigma*H+beta*r*sigma-r*sigma, mu*mup*p0*sigma*H+mu*muN*dn*sigma*H+mu*mup*dn*sigma*H-muH*mup^2*p0+muN^2*muH*dn-muH*mup^2*dn}, {e*dn*beta*sigma*H-muN*e*p0*r+e*p0*sigma*H+e*dn*sigma*H+beta*r*sigma-r*sigma, muN^2*e*dn*r+muN*e*mup*dn*r-mup*r*sigma+sigma^2*H}, {e*dn*beta*sigma*H-muN*e*p0*r+e*p0*sigma*H+e*dn*sigma*H+beta*r*sigma-r*sigma, muN^2*e*p0*r-muN*beta*r*sigma-beta*sigma^2*H+muN*r*sigma}, {e*dn*beta*sigma*H-muN*e*p0*r+e*p0*sigma*H+e*dn*sigma*H+beta*r*sigma-r*sigma, muN^2*muH*e*dn+muN*muH*e*mup*dn+mu*sigma^2*H-muH*mup*sigma}, {e*dn*beta*sigma*H-muN*e*p0*r+e*p0*sigma*H+e*dn*sigma*H+beta*r*sigma-r*sigma, muN^2*muH*e*p0-mu*beta*sigma^2*H-muN*muH*beta*sigma+muN*muH*sigma}, {e*dn*beta*sigma*H-muN*e*p0*r+e*p0*sigma*H+e*dn*sigma*H+beta*r*sigma-r*sigma, e*dn^2*beta^2*H+2*e*p0*dn*beta*H+2*e*dn^2*beta*H+dn*beta^2*r+e*p0^2*H+2*e*p0*dn*H+e*dn^2*H-p0*r-dn*r}, {mu*dn*beta*sigma*H+muN*muH*dn*beta+mu*p0*sigma*H+mu*dn*sigma*H-muH*mup*p0-muH*mup*dn, mu*mup*p0*sigma*H+mu*muN*dn*sigma*H+mu*mup*dn*sigma*H-muH*mup^2*p0+muN^2*muH*dn-muH*mup^2*dn}, {mu*dn*beta*sigma*H+muN*muH*dn*beta+mu*p0*sigma*H+mu*dn*sigma*H-muH*mup*p0-muH*mup*dn, muN^2*e*dn*r+muN*e*mup*dn*r-mup*r*sigma+sigma^2*H}, {mu*dn*beta*sigma*H+muN*muH*dn*beta+mu*p0*sigma*H+mu*dn*sigma*H-muH*mup*p0-muH*mup*dn, muN^2*e*p0*r-muN*beta*r*sigma-beta*sigma^2*H+muN*r*sigma}, {mu*dn*beta*sigma*H+muN*muH*dn*beta+mu*p0*sigma*H+mu*dn*sigma*H-muH*mup*p0-muH*mup*dn, muN^2*muH*e*dn+muN*muH*e*mup*dn+mu*sigma^2*H-muH*mup*sigma}, {mu*dn*beta*sigma*H+muN*muH*dn*beta+mu*p0*sigma*H+mu*dn*sigma*H-muH*mup*p0-muH*mup*dn, muN^2*muH*e*p0-mu*beta*sigma^2*H-muN*muH*beta*sigma+muN*muH*sigma}, {mu*dn*beta*sigma*H+muN*muH*dn*beta+mu*p0*sigma*H+mu*dn*sigma*H-muH*mup*p0-muH*mup*dn, e*dn^2*beta^2*H+2*e*p0*dn*beta*H+2*e*dn^2*beta*H+dn*beta^2*r+e*p0^2*H+2*e*p0*dn*H+e*dn^2*H-p0*r-dn*r}, {mu*mup*p0*sigma*H+mu*muN*dn*sigma*H+mu*mup*dn*sigma*H-muH*mup^2*p0+muN^2*muH*dn-muH*mup^2*dn, muN^2*e*dn*r+muN*e*mup*dn*r-mup*r*sigma+sigma^2*H}, {mu*mup*p0*sigma*H+mu*muN*dn*sigma*H+mu*mup*dn*sigma*H-muH*mup^2*p0+muN^2*muH*dn-muH*mup^2*dn, muN^2*e*p0*r-muN*beta*r*sigma-beta*sigma^2*H+muN*r*sigma}, {mu*mup*p0*sigma*H+mu*muN*dn*sigma*H+mu*mup*dn*sigma*H-muH*mup^2*p0+muN^2*muH*dn-muH*mup^2*dn, muN^2*muH*e*dn+muN*muH*e*mup*dn+mu*sigma^2*H-muH*mup*sigma}, {mu*mup*p0*sigma*H+mu*muN*dn*sigma*H+mu*mup*dn*sigma*H-muH*mup^2*p0+muN^2*muH*dn-muH*mup^2*dn, muN^2*muH*e*p0-mu*beta*sigma^2*H-muN*muH*beta*sigma+muN*muH*sigma}, {mu*mup*p0*sigma*H+mu*muN*dn*sigma*H+mu*mup*dn*sigma*H-muH*mup^2*p0+muN^2*muH*dn-muH*mup^2*dn, e*dn^2*beta^2*H+2*e*p0*dn*beta*H+2*e*dn^2*beta*H+dn*beta^2*r+e*p0^2*H+2*e*p0*dn*H+e*dn^2*H-p0*r-dn*r}, {muN^2*e*dn*r+muN*e*mup*dn*r-mup*r*sigma+sigma^2*H, muN^2*e*p0*r-muN*beta*r*sigma-beta*sigma^2*H+muN*r*sigma}, {muN^2*e*dn*r+muN*e*mup*dn*r-mup*r*sigma+sigma^2*H, muN^2*muH*e*dn+muN*muH*e*mup*dn+mu*sigma^2*H-muH*mup*sigma}, {muN^2*e*dn*r+muN*e*mup*dn*r-mup*r*sigma+sigma^2*H, muN^2*muH*e*p0-mu*beta*sigma^2*H-muN*muH*beta*sigma+muN*muH*sigma}, {muN^2*e*dn*r+muN*e*mup*dn*r-mup*r*sigma+sigma^2*H, e*dn^2*beta^2*H+2*e*p0*dn*beta*H+2*e*dn^2*beta*H+dn*beta^2*r+e*p0^2*H+2*e*p0*dn*H+e*dn^2*H-p0*r-dn*r}, {muN^2*e*p0*r-muN*beta*r*sigma-beta*sigma^2*H+muN*r*sigma, muN^2*muH*e*dn+muN*muH*e*mup*dn+mu*sigma^2*H-muH*mup*sigma}, {muN^2*e*p0*r-muN*beta*r*sigma-beta*sigma^2*H+muN*r*sigma, muN^2*muH*e*p0-mu*beta*sigma^2*H-muN*muH*beta*sigma+muN*muH*sigma}, {muN^2*e*p0*r-muN*beta*r*sigma-beta*sigma^2*H+muN*r*sigma, e*dn^2*beta^2*H+2*e*p0*dn*beta*H+2*e*dn^2*beta*H+dn*beta^2*r+e*p0^2*H+2*e*p0*dn*H+e*dn^2*H-p0*r-dn*r}, {muN^2*muH*e*dn+muN*muH*e*mup*dn+mu*sigma^2*H-muH*mup*sigma, muN^2*muH*e*p0-mu*beta*sigma^2*H-muN*muH*beta*sigma+muN*muH*sigma}, {muN^2*muH*e*dn+muN*muH*e*mup*dn+mu*sigma^2*H-muH*mup*sigma, e*dn^2*beta^2*H+2*e*p0*dn*beta*H+2*e*dn^2*beta*H+dn*beta^2*r+e*p0^2*H+2*e*p0*dn*H+e*dn^2*H-p0*r-dn*r}, {muN^2*muH*e*p0-mu*beta*sigma^2*H-muN*muH*beta*sigma+muN*muH*sigma, e*dn^2*beta^2*H+2*e*p0*dn*beta*H+2*e*dn^2*beta*H+dn*beta^2*r+e*p0^2*H+2*e*p0*dn*H+e*dn^2*H-p0*r-dn*r}, {sigma}, {r}, {e}, {n-dn}, {muH}, {dp-dn}, {mup*beta-muN}, {sigma, r}, {sigma, e}, {sigma, n-dn}, {sigma, muH}, {sigma, dp-dn}, {sigma, mup*beta-muN}, {r, e}, {r, n-dn}, {r, muH}, {r, dp-dn}, {r, mup*beta-muN}, {e, n-dn}, {e, muH}, {e, dp-dn}, {e, mup*beta-muN}, {n-dn, muH}, {n-dn, dp-dn}, {n-dn, mup*beta-muN}, {muH, dp-dn}, {muH, mup*beta-muN}, {dp-dn, mup*beta-muN}, {H}, {r}, {n-dn}, {muH}, {dp-dn}, {mup*beta-muN}, {ph*e*mup+muN*e*dn-sigma}, {muN*e*dn*beta+ph*muN*e-beta*sigma}, {H, r}, {H, n-dn}, {H, muH}, {H, dp-dn}, {H, mup*beta-muN}, {H, ph*e*mup+muN*e*dn-sigma}, {H, muN*e*dn*beta+ph*muN*e-beta*sigma}, {r, n-dn}, {r, muH}, {r, dp-dn}, {r, mup*beta-muN}, {r, ph*e*mup+muN*e*dn-sigma}, {r, muN*e*dn*beta+ph*muN*e-beta*sigma}, {n-dn, muH}, {n-dn, dp-dn}, {n-dn, mup*beta-muN}, {n-dn, ph*e*mup+muN*e*dn-sigma}, {n-dn, muN*e*dn*beta+ph*muN*e-beta*sigma}, {muH, dp-dn}, {muH, mup*beta-muN}, {muH, ph*e*mup+muN*e*dn-sigma}, {muH, muN*e*dn*beta+ph*muN*e-beta*sigma}, {dp-dn, mup*beta-muN}, {dp-dn, ph*e*mup+muN*e*dn-sigma}, {dp-dn, muN*e*dn*beta+ph*muN*e-beta*sigma}, {mup*beta-muN, ph*e*mup+muN*e*dn-sigma}, {mup*beta-muN, muN*e*dn*beta+ph*muN*e-beta*sigma}, {ph*e*mup+muN*e*dn-sigma, muN*e*dn*beta+ph*muN*e-beta*sigma}, {sigma}, {r}, {n-dn}, {muH}, {dp-dn}, {dn*beta+ph}, {mup*beta-muN}, {ph*mup+muN*dn}, {sigma, r}, {sigma, n-dn}, {sigma, muH}, {sigma, dp-dn}, {sigma, dn*beta+ph}, {sigma, mup*beta-muN}, {sigma, ph*mup+muN*dn}, {r, n-dn}, {r, muH}, {r, dp-dn}, {r, dn*beta+ph}, {r, mup*beta-muN}, {r, ph*mup+muN*dn}, {n-dn, muH}, {n-dn, dp-dn}, {n-dn, dn*beta+ph}, {n-dn, mup*beta-muN}, {n-dn, ph*mup+muN*dn}, {muH, dp-dn}, {muH, dn*beta+ph}, {muH, mup*beta-muN}, {muH, ph*mup+muN*dn}, {dp-dn, dn*beta+ph}, {dp-dn, mup*beta-muN}, {dp-dn, ph*mup+muN*dn}, {dn*beta+ph, mup*beta-muN}, {dn*beta+ph, ph*mup+muN*dn}, {mup*beta-muN, ph*mup+muN*dn}, {sigma}, {e}, {n-dn}, {dp-dn}, {mu*r-muH}, {mup*beta-muN}, {dn*beta^2-ph}, {muN*dn*beta-ph*mup}, {ph*mup^2-muN^2*dn}, {sigma, e}, {sigma, n-dn}, {sigma, dp-dn}, {sigma, mu*r-muH}, {sigma, mup*beta-muN}, {sigma, dn*beta^2-ph}, {sigma, muN*dn*beta-ph*mup}, {sigma, ph*mup^2-muN^2*dn}, {e, n-dn}, {e, dp-dn}, {e, mu*r-muH}, {e, mup*beta-muN}, {e, dn*beta^2-ph}, {e, muN*dn*beta-ph*mup}, {e, ph*mup^2-muN^2*dn}, {n-dn, dp-dn}, {n-dn, mu*r-muH}, {n-dn, mup*beta-muN}, {n-dn, dn*beta^2-ph}, {n-dn, muN*dn*beta-ph*mup}, {n-dn, ph*mup^2-muN^2*dn}, {dp-dn, mu*r-muH}, {dp-dn, mup*beta-muN}, {dp-dn, dn*beta^2-ph}, {dp-dn, muN*dn*beta-ph*mup}, {dp-dn, ph*mup^2-muN^2*dn}, {mu*r-muH, mup*beta-muN}, {mu*r-muH, dn*beta^2-ph}, {mu*r-muH, muN*dn*beta-ph*mup}, {mu*r-muH, ph*mup^2-muN^2*dn}, {mup*beta-muN, dn*beta^2-ph}, {mup*beta-muN, muN*dn*beta-ph*mup}, {mup*beta-muN, ph*mup^2-muN^2*dn}, {dn*beta^2-ph, muN*dn*beta-ph*mup}, {dn*beta^2-ph, ph*mup^2-muN^2*dn}, {muN*dn*beta-ph*mup, ph*mup^2-muN^2*dn}, {sigma}, {mup}, {n-dn}, {muN}, {dp-dn}, {mu*r-muH}, {e*dn^2*beta^2*H+2*ph*e*dn*beta*H+dn*beta^2*r+ph^2*e*H-ph*r}, {sigma, mup}, {sigma, n-dn}, {sigma, muN}, {sigma, dp-dn}, {sigma, mu*r-muH}, {sigma, e*dn^2*beta^2*H+2*ph*e*dn*beta*H+dn*beta^2*r+ph^2*e*H-ph*r}, {mup, n-dn}, {mup, muN}, {mup, dp-dn}, {mup, mu*r-muH}, {mup, e*dn^2*beta^2*H+2*ph*e*dn*beta*H+dn*beta^2*r+ph^2*e*H-ph*r}, {n-dn, muN}, {n-dn, dp-dn}, {n-dn, mu*r-muH}, {n-dn, e*dn^2*beta^2*H+2*ph*e*dn*beta*H+dn*beta^2*r+ph^2*e*H-ph*r}, {muN, dp-dn}, {muN, mu*r-muH}, {muN, e*dn^2*beta^2*H+2*ph*e*dn*beta*H+dn*beta^2*r+ph^2*e*H-ph*r}, {dp-dn, mu*r-muH}, {dp-dn, e*dn^2*beta^2*H+2*ph*e*dn*beta*H+dn*beta^2*r+ph^2*e*H-ph*r}, {mu*r-muH, e*dn^2*beta^2*H+2*ph*e*dn*beta*H+dn*beta^2*r+ph^2*e*H-ph*r}, {sigma}, {beta+1}, {n-dn}, {muN+mup}, {dp-dn}, {ph-dn}, {mu*r-muH}, {sigma, beta+1}, {sigma, n-dn}, {sigma, muN+mup}, {sigma, dp-dn}, {sigma, ph-dn}, {sigma, mu*r-muH}, {beta+1, n-dn}, {beta+1, muN+mup}, {beta+1, dp-dn}, {beta+1, ph-dn}, {beta+1, mu*r-muH}, {n-dn, muN+mup}, {n-dn, dp-dn}, {n-dn, ph-dn}, {n-dn, mu*r-muH}, {muN+mup, dp-dn}, {muN+mup, ph-dn}, {muN+mup, mu*r-muH}, {dp-dn, ph-dn}, {dp-dn, mu*r-muH}, {ph-dn, mu*r-muH}, {sigma}, {beta}, {n-dn}, {muN}, {dp-dn}, {ph}, {mu*r-muH}, {sigma, beta}, {sigma, n-dn}, {sigma, muN}, {sigma, dp-dn}, {sigma, ph}, {sigma, mu*r-muH}, {beta, n-dn}, {beta, muN}, {beta, dp-dn}, {beta, ph}, {beta, mu*r-muH}, {n-dn, muN}, {n-dn, dp-dn}, {n-dn, ph}, {n-dn, mu*r-muH}, {muN, dp-dn}, {muN, ph}, {muN, mu*r-muH}, {dp-dn, ph}, {dp-dn, mu*r-muH}, {ph, mu*r-muH}, {sigma}, {dn}, {n}, {dp}, {ph}, {mu*r-muH}, {mup*beta-muN}, {sigma, dn}, {sigma, n}, {sigma, dp}, {sigma, ph}, {sigma, mu*r-muH}, {sigma, mup*beta-muN}, {dn, n}, {dn, dp}, {dn, ph}, {dn, mu*r-muH}, {dn, mup*beta-muN}, {n, dp}, {n, ph}, {n, mu*r-muH}, {n, mup*beta-muN}, {dp, ph}, {dp, mu*r-muH}, {dp, mup*beta-muN}, {ph, mu*r-muH}, {ph, mup*beta-muN}, {mu*r-muH, mup*beta-muN}, {H}, {n-dn}, {dp-dn}, {mu*r-muH}, {mup*beta-muN}, {dn*beta^2-ph}, {muN*dn*beta-ph*mup}, {ph*mup^2-muN^2*dn}, {ph*e*mup+muN*e*dn-sigma}, {ph*muN*e-muN*e*dn-beta*sigma+sigma}, {muN^2*e*dn+muN*e*mup*dn-mup*sigma}, {H, n-dn}, {H, dp-dn}, {H, mu*r-muH}, {H, mup*beta-muN}, {H, dn*beta^2-ph}, {H, muN*dn*beta-ph*mup}, {H, ph*mup^2-muN^2*dn}, {H, ph*e*mup+muN*e*dn-sigma}, {H, ph*muN*e-muN*e*dn-beta*sigma+sigma}, {H, muN^2*e*dn+muN*e*mup*dn-mup*sigma}, {n-dn, dp-dn}, {n-dn, mu*r-muH}, {n-dn, mup*beta-muN}, {n-dn, dn*beta^2-ph}, {n-dn, muN*dn*beta-ph*mup}, {n-dn, ph*mup^2-muN^2*dn}, {n-dn, ph*e*mup+muN*e*dn-sigma}, {n-dn, ph*muN*e-muN*e*dn-beta*sigma+sigma}, {n-dn, muN^2*e*dn+muN*e*mup*dn-mup*sigma}, {dp-dn, mu*r-muH}, {dp-dn, mup*beta-muN}, {dp-dn, dn*beta^2-ph}, {dp-dn, muN*dn*beta-ph*mup}, {dp-dn, ph*mup^2-muN^2*dn}, {dp-dn, ph*e*mup+muN*e*dn-sigma}, {dp-dn, ph*muN*e-muN*e*dn-beta*sigma+sigma}, {dp-dn, muN^2*e*dn+muN*e*mup*dn-mup*sigma}, {mu*r-muH, mup*beta-muN}, {mu*r-muH, dn*beta^2-ph}, {mu*r-muH, muN*dn*beta-ph*mup}, {mu*r-muH, ph*mup^2-muN^2*dn}, {mu*r-muH, ph*e*mup+muN*e*dn-sigma}, {mu*r-muH, ph*muN*e-muN*e*dn-beta*sigma+sigma}, {mu*r-muH, muN^2*e*dn+muN*e*mup*dn-mup*sigma}, {mup*beta-muN, dn*beta^2-ph}, {mup*beta-muN, muN*dn*beta-ph*mup}, {mup*beta-muN, ph*mup^2-muN^2*dn}, {mup*beta-muN, ph*e*mup+muN*e*dn-sigma}, {mup*beta-muN, ph*muN*e-muN*e*dn-beta*sigma+sigma}, {mup*beta-muN, muN^2*e*dn+muN*e*mup*dn-mup*sigma}, {dn*beta^2-ph, muN*dn*beta-ph*mup}, {dn*beta^2-ph, ph*mup^2-muN^2*dn}, {dn*beta^2-ph, ph*e*mup+muN*e*dn-sigma}, {dn*beta^2-ph, ph*muN*e-muN*e*dn-beta*sigma+sigma}, {dn*beta^2-ph, muN^2*e*dn+muN*e*mup*dn-mup*sigma}, {muN*dn*beta-ph*mup, ph*mup^2-muN^2*dn}, {muN*dn*beta-ph*mup, ph*e*mup+muN*e*dn-sigma}, {muN*dn*beta-ph*mup, ph*muN*e-muN*e*dn-beta*sigma+sigma}, {muN*dn*beta-ph*mup, muN^2*e*dn+muN*e*mup*dn-mup*sigma}, {ph*mup^2-muN^2*dn, ph*e*mup+muN*e*dn-sigma}, {ph*mup^2-muN^2*dn, ph*muN*e-muN*e*dn-beta*sigma+sigma}, {ph*mup^2-muN^2*dn, muN^2*e*dn+muN*e*mup*dn-mup*sigma}, {ph*e*mup+muN*e*dn-sigma, ph*muN*e-muN*e*dn-beta*sigma+sigma}, {ph*e*mup+muN*e*dn-sigma, muN^2*e*dn+muN*e*mup*dn-mup*sigma}, {ph*muN*e-muN*e*dn-beta*sigma+sigma, muN^2*e*dn+muN*e*mup*dn-mup*sigma}};

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
f = openOut "results/photoHall/abduction/noiseless/1_axiom(s)_removed/combo_3/reasoning/reasoning_output.txt";
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

print("Reasoning complete. Output written to results/photoHall/abduction/noiseless/1_axiom(s)_removed/combo_3/reasoning/reasoning_output.txt");
