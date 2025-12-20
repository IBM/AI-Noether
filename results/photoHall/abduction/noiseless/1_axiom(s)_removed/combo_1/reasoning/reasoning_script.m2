-- AI-Noether: Reasoning Template (Noiseless)
-- Tests if candidate axiom sets, when added to remaining axioms, prove targets

needsPackage("PrimaryDecomposition", Reload => true)

-- Ring definition
R = QQ[ph, dp, mu, muN, muH, n, dsigma2dn, e, mup, p0, dn, beta, r, sigma, H, MonomialOrder => Lex];

-- Input data
remainingAxioms = toList([muH - r * mu, ph - p0 - dp, n - dn, dp - dn, sigma - e * ph * mup - e * n * muN, H * (ph + beta * n)^2 * e - r * ph + r * beta^2 * n]);
qList = toList([r*e*mup*dn*beta^2 + r*e*mup*dn*beta - r*sigma + e*p0*sigma*H + e*dn*beta*sigma*H + e*dn*sigma*H]);
k = #qList;

-- Per-target variable partitions
measuredPerTarget = {{sigma, r, e, mup, p0, dn, beta, H}};
nonMeasuredPerTarget = {{ph, dp, mu, muN, muH, n, dsigma2dn}};

-- Candidate axiom sets to test (list of lists)
candidateSets = {{}, {n-dn}, {dp-dn}, {ph-p0-dn}, {mu*r-muH}, {mup*beta-muN}, {e*mup*p0+muN*e*dn+e*mup*dn-sigma}, {muN*dn*beta*r+dn*beta*sigma*H-mup*p0*r-mup*dn*r+p0*sigma*H+dn*sigma*H}, {mup^2*p0*r-muN^2*dn*r+mup^2*dn*r-mup*p0*sigma*H-muN*dn*sigma*H-mup*dn*sigma*H}, {muN*e*dn*beta+muN*e*p0+muN*e*dn-beta*sigma}, {e*dn*beta*sigma*H-muN*e*p0*r+e*p0*sigma*H+e*dn*sigma*H+beta*r*sigma-r*sigma}, {mu*dn*beta*sigma*H+muN*muH*dn*beta+mu*p0*sigma*H+mu*dn*sigma*H-muH*mup*p0-muH*mup*dn}, {mu*mup*p0*sigma*H+mu*muN*dn*sigma*H+mu*mup*dn*sigma*H-muH*mup^2*p0+muN^2*muH*dn-muH*mup^2*dn}, {muN^2*e*dn*r+muN*e*mup*dn*r-mup*r*sigma+sigma^2*H}, {muN^2*e*p0*r-muN*beta*r*sigma-beta*sigma^2*H+muN*r*sigma}, {muN^2*muH*e*dn+muN*muH*e*mup*dn+mu*sigma^2*H-muH*mup*sigma}, {muN^2*muH*e*p0-mu*beta*sigma^2*H-muN*muH*beta*sigma+muN*muH*sigma}, {e*dn^2*beta^2*H+2*e*p0*dn*beta*H+2*e*dn^2*beta*H+dn*beta^2*r+e*p0^2*H+2*e*p0*dn*H+e*dn^2*H-p0*r-dn*r}, {n-dn, dp-dn}, {n-dn, ph-p0-dn}, {n-dn, mu*r-muH}, {n-dn, mup*beta-muN}, {n-dn, e*mup*p0+muN*e*dn+e*mup*dn-sigma}, {n-dn, muN*dn*beta*r+dn*beta*sigma*H-mup*p0*r-mup*dn*r+p0*sigma*H+dn*sigma*H}, {n-dn, mup^2*p0*r-muN^2*dn*r+mup^2*dn*r-mup*p0*sigma*H-muN*dn*sigma*H-mup*dn*sigma*H}, {n-dn, muN*e*dn*beta+muN*e*p0+muN*e*dn-beta*sigma}, {n-dn, e*dn*beta*sigma*H-muN*e*p0*r+e*p0*sigma*H+e*dn*sigma*H+beta*r*sigma-r*sigma}, {n-dn, mu*dn*beta*sigma*H+muN*muH*dn*beta+mu*p0*sigma*H+mu*dn*sigma*H-muH*mup*p0-muH*mup*dn}, {n-dn, mu*mup*p0*sigma*H+mu*muN*dn*sigma*H+mu*mup*dn*sigma*H-muH*mup^2*p0+muN^2*muH*dn-muH*mup^2*dn}, {n-dn, muN^2*e*dn*r+muN*e*mup*dn*r-mup*r*sigma+sigma^2*H}, {n-dn, muN^2*e*p0*r-muN*beta*r*sigma-beta*sigma^2*H+muN*r*sigma}, {n-dn, muN^2*muH*e*dn+muN*muH*e*mup*dn+mu*sigma^2*H-muH*mup*sigma}, {n-dn, muN^2*muH*e*p0-mu*beta*sigma^2*H-muN*muH*beta*sigma+muN*muH*sigma}, {n-dn, e*dn^2*beta^2*H+2*e*p0*dn*beta*H+2*e*dn^2*beta*H+dn*beta^2*r+e*p0^2*H+2*e*p0*dn*H+e*dn^2*H-p0*r-dn*r}, {dp-dn, ph-p0-dn}, {dp-dn, mu*r-muH}, {dp-dn, mup*beta-muN}, {dp-dn, e*mup*p0+muN*e*dn+e*mup*dn-sigma}, {dp-dn, muN*dn*beta*r+dn*beta*sigma*H-mup*p0*r-mup*dn*r+p0*sigma*H+dn*sigma*H}, {dp-dn, mup^2*p0*r-muN^2*dn*r+mup^2*dn*r-mup*p0*sigma*H-muN*dn*sigma*H-mup*dn*sigma*H}, {dp-dn, muN*e*dn*beta+muN*e*p0+muN*e*dn-beta*sigma}, {dp-dn, e*dn*beta*sigma*H-muN*e*p0*r+e*p0*sigma*H+e*dn*sigma*H+beta*r*sigma-r*sigma}, {dp-dn, mu*dn*beta*sigma*H+muN*muH*dn*beta+mu*p0*sigma*H+mu*dn*sigma*H-muH*mup*p0-muH*mup*dn}, {dp-dn, mu*mup*p0*sigma*H+mu*muN*dn*sigma*H+mu*mup*dn*sigma*H-muH*mup^2*p0+muN^2*muH*dn-muH*mup^2*dn}, {dp-dn, muN^2*e*dn*r+muN*e*mup*dn*r-mup*r*sigma+sigma^2*H}, {dp-dn, muN^2*e*p0*r-muN*beta*r*sigma-beta*sigma^2*H+muN*r*sigma}, {dp-dn, muN^2*muH*e*dn+muN*muH*e*mup*dn+mu*sigma^2*H-muH*mup*sigma}, {dp-dn, muN^2*muH*e*p0-mu*beta*sigma^2*H-muN*muH*beta*sigma+muN*muH*sigma}, {dp-dn, e*dn^2*beta^2*H+2*e*p0*dn*beta*H+2*e*dn^2*beta*H+dn*beta^2*r+e*p0^2*H+2*e*p0*dn*H+e*dn^2*H-p0*r-dn*r}, {ph-p0-dn, mu*r-muH}, {ph-p0-dn, mup*beta-muN}, {ph-p0-dn, e*mup*p0+muN*e*dn+e*mup*dn-sigma}, {ph-p0-dn, muN*dn*beta*r+dn*beta*sigma*H-mup*p0*r-mup*dn*r+p0*sigma*H+dn*sigma*H}, {ph-p0-dn, mup^2*p0*r-muN^2*dn*r+mup^2*dn*r-mup*p0*sigma*H-muN*dn*sigma*H-mup*dn*sigma*H}, {ph-p0-dn, muN*e*dn*beta+muN*e*p0+muN*e*dn-beta*sigma}, {ph-p0-dn, e*dn*beta*sigma*H-muN*e*p0*r+e*p0*sigma*H+e*dn*sigma*H+beta*r*sigma-r*sigma}, {ph-p0-dn, mu*dn*beta*sigma*H+muN*muH*dn*beta+mu*p0*sigma*H+mu*dn*sigma*H-muH*mup*p0-muH*mup*dn}, {ph-p0-dn, mu*mup*p0*sigma*H+mu*muN*dn*sigma*H+mu*mup*dn*sigma*H-muH*mup^2*p0+muN^2*muH*dn-muH*mup^2*dn}, {ph-p0-dn, muN^2*e*dn*r+muN*e*mup*dn*r-mup*r*sigma+sigma^2*H}, {ph-p0-dn, muN^2*e*p0*r-muN*beta*r*sigma-beta*sigma^2*H+muN*r*sigma}, {ph-p0-dn, muN^2*muH*e*dn+muN*muH*e*mup*dn+mu*sigma^2*H-muH*mup*sigma}, {ph-p0-dn, muN^2*muH*e*p0-mu*beta*sigma^2*H-muN*muH*beta*sigma+muN*muH*sigma}, {ph-p0-dn, e*dn^2*beta^2*H+2*e*p0*dn*beta*H+2*e*dn^2*beta*H+dn*beta^2*r+e*p0^2*H+2*e*p0*dn*H+e*dn^2*H-p0*r-dn*r}, {mu*r-muH, mup*beta-muN}, {mu*r-muH, e*mup*p0+muN*e*dn+e*mup*dn-sigma}, {mu*r-muH, muN*dn*beta*r+dn*beta*sigma*H-mup*p0*r-mup*dn*r+p0*sigma*H+dn*sigma*H}, {mu*r-muH, mup^2*p0*r-muN^2*dn*r+mup^2*dn*r-mup*p0*sigma*H-muN*dn*sigma*H-mup*dn*sigma*H}, {mu*r-muH, muN*e*dn*beta+muN*e*p0+muN*e*dn-beta*sigma}, {mu*r-muH, e*dn*beta*sigma*H-muN*e*p0*r+e*p0*sigma*H+e*dn*sigma*H+beta*r*sigma-r*sigma}, {mu*r-muH, mu*dn*beta*sigma*H+muN*muH*dn*beta+mu*p0*sigma*H+mu*dn*sigma*H-muH*mup*p0-muH*mup*dn}, {mu*r-muH, mu*mup*p0*sigma*H+mu*muN*dn*sigma*H+mu*mup*dn*sigma*H-muH*mup^2*p0+muN^2*muH*dn-muH*mup^2*dn}, {mu*r-muH, muN^2*e*dn*r+muN*e*mup*dn*r-mup*r*sigma+sigma^2*H}, {mu*r-muH, muN^2*e*p0*r-muN*beta*r*sigma-beta*sigma^2*H+muN*r*sigma}, {mu*r-muH, muN^2*muH*e*dn+muN*muH*e*mup*dn+mu*sigma^2*H-muH*mup*sigma}, {mu*r-muH, muN^2*muH*e*p0-mu*beta*sigma^2*H-muN*muH*beta*sigma+muN*muH*sigma}, {mu*r-muH, e*dn^2*beta^2*H+2*e*p0*dn*beta*H+2*e*dn^2*beta*H+dn*beta^2*r+e*p0^2*H+2*e*p0*dn*H+e*dn^2*H-p0*r-dn*r}, {mup*beta-muN, e*mup*p0+muN*e*dn+e*mup*dn-sigma}, {mup*beta-muN, muN*dn*beta*r+dn*beta*sigma*H-mup*p0*r-mup*dn*r+p0*sigma*H+dn*sigma*H}, {mup*beta-muN, mup^2*p0*r-muN^2*dn*r+mup^2*dn*r-mup*p0*sigma*H-muN*dn*sigma*H-mup*dn*sigma*H}, {mup*beta-muN, muN*e*dn*beta+muN*e*p0+muN*e*dn-beta*sigma}, {mup*beta-muN, e*dn*beta*sigma*H-muN*e*p0*r+e*p0*sigma*H+e*dn*sigma*H+beta*r*sigma-r*sigma}, {mup*beta-muN, mu*dn*beta*sigma*H+muN*muH*dn*beta+mu*p0*sigma*H+mu*dn*sigma*H-muH*mup*p0-muH*mup*dn}, {mup*beta-muN, mu*mup*p0*sigma*H+mu*muN*dn*sigma*H+mu*mup*dn*sigma*H-muH*mup^2*p0+muN^2*muH*dn-muH*mup^2*dn}, {mup*beta-muN, muN^2*e*dn*r+muN*e*mup*dn*r-mup*r*sigma+sigma^2*H}, {mup*beta-muN, muN^2*e*p0*r-muN*beta*r*sigma-beta*sigma^2*H+muN*r*sigma}, {mup*beta-muN, muN^2*muH*e*dn+muN*muH*e*mup*dn+mu*sigma^2*H-muH*mup*sigma}, {mup*beta-muN, muN^2*muH*e*p0-mu*beta*sigma^2*H-muN*muH*beta*sigma+muN*muH*sigma}, {mup*beta-muN, e*dn^2*beta^2*H+2*e*p0*dn*beta*H+2*e*dn^2*beta*H+dn*beta^2*r+e*p0^2*H+2*e*p0*dn*H+e*dn^2*H-p0*r-dn*r}, {e*mup*p0+muN*e*dn+e*mup*dn-sigma, muN*dn*beta*r+dn*beta*sigma*H-mup*p0*r-mup*dn*r+p0*sigma*H+dn*sigma*H}, {e*mup*p0+muN*e*dn+e*mup*dn-sigma, mup^2*p0*r-muN^2*dn*r+mup^2*dn*r-mup*p0*sigma*H-muN*dn*sigma*H-mup*dn*sigma*H}, {e*mup*p0+muN*e*dn+e*mup*dn-sigma, muN*e*dn*beta+muN*e*p0+muN*e*dn-beta*sigma}, {e*mup*p0+muN*e*dn+e*mup*dn-sigma, e*dn*beta*sigma*H-muN*e*p0*r+e*p0*sigma*H+e*dn*sigma*H+beta*r*sigma-r*sigma}, {e*mup*p0+muN*e*dn+e*mup*dn-sigma, mu*dn*beta*sigma*H+muN*muH*dn*beta+mu*p0*sigma*H+mu*dn*sigma*H-muH*mup*p0-muH*mup*dn}, {e*mup*p0+muN*e*dn+e*mup*dn-sigma, mu*mup*p0*sigma*H+mu*muN*dn*sigma*H+mu*mup*dn*sigma*H-muH*mup^2*p0+muN^2*muH*dn-muH*mup^2*dn}, {e*mup*p0+muN*e*dn+e*mup*dn-sigma, muN^2*e*dn*r+muN*e*mup*dn*r-mup*r*sigma+sigma^2*H}, {e*mup*p0+muN*e*dn+e*mup*dn-sigma, muN^2*e*p0*r-muN*beta*r*sigma-beta*sigma^2*H+muN*r*sigma}, {e*mup*p0+muN*e*dn+e*mup*dn-sigma, muN^2*muH*e*dn+muN*muH*e*mup*dn+mu*sigma^2*H-muH*mup*sigma}, {e*mup*p0+muN*e*dn+e*mup*dn-sigma, muN^2*muH*e*p0-mu*beta*sigma^2*H-muN*muH*beta*sigma+muN*muH*sigma}, {e*mup*p0+muN*e*dn+e*mup*dn-sigma, e*dn^2*beta^2*H+2*e*p0*dn*beta*H+2*e*dn^2*beta*H+dn*beta^2*r+e*p0^2*H+2*e*p0*dn*H+e*dn^2*H-p0*r-dn*r}, {muN*dn*beta*r+dn*beta*sigma*H-mup*p0*r-mup*dn*r+p0*sigma*H+dn*sigma*H, mup^2*p0*r-muN^2*dn*r+mup^2*dn*r-mup*p0*sigma*H-muN*dn*sigma*H-mup*dn*sigma*H}, {muN*dn*beta*r+dn*beta*sigma*H-mup*p0*r-mup*dn*r+p0*sigma*H+dn*sigma*H, muN*e*dn*beta+muN*e*p0+muN*e*dn-beta*sigma}, {muN*dn*beta*r+dn*beta*sigma*H-mup*p0*r-mup*dn*r+p0*sigma*H+dn*sigma*H, e*dn*beta*sigma*H-muN*e*p0*r+e*p0*sigma*H+e*dn*sigma*H+beta*r*sigma-r*sigma}, {muN*dn*beta*r+dn*beta*sigma*H-mup*p0*r-mup*dn*r+p0*sigma*H+dn*sigma*H, mu*dn*beta*sigma*H+muN*muH*dn*beta+mu*p0*sigma*H+mu*dn*sigma*H-muH*mup*p0-muH*mup*dn}, {muN*dn*beta*r+dn*beta*sigma*H-mup*p0*r-mup*dn*r+p0*sigma*H+dn*sigma*H, mu*mup*p0*sigma*H+mu*muN*dn*sigma*H+mu*mup*dn*sigma*H-muH*mup^2*p0+muN^2*muH*dn-muH*mup^2*dn}, {muN*dn*beta*r+dn*beta*sigma*H-mup*p0*r-mup*dn*r+p0*sigma*H+dn*sigma*H, muN^2*e*dn*r+muN*e*mup*dn*r-mup*r*sigma+sigma^2*H}, {muN*dn*beta*r+dn*beta*sigma*H-mup*p0*r-mup*dn*r+p0*sigma*H+dn*sigma*H, muN^2*e*p0*r-muN*beta*r*sigma-beta*sigma^2*H+muN*r*sigma}, {muN*dn*beta*r+dn*beta*sigma*H-mup*p0*r-mup*dn*r+p0*sigma*H+dn*sigma*H, muN^2*muH*e*dn+muN*muH*e*mup*dn+mu*sigma^2*H-muH*mup*sigma}, {muN*dn*beta*r+dn*beta*sigma*H-mup*p0*r-mup*dn*r+p0*sigma*H+dn*sigma*H, muN^2*muH*e*p0-mu*beta*sigma^2*H-muN*muH*beta*sigma+muN*muH*sigma}, {muN*dn*beta*r+dn*beta*sigma*H-mup*p0*r-mup*dn*r+p0*sigma*H+dn*sigma*H, e*dn^2*beta^2*H+2*e*p0*dn*beta*H+2*e*dn^2*beta*H+dn*beta^2*r+e*p0^2*H+2*e*p0*dn*H+e*dn^2*H-p0*r-dn*r}, {mup^2*p0*r-muN^2*dn*r+mup^2*dn*r-mup*p0*sigma*H-muN*dn*sigma*H-mup*dn*sigma*H, muN*e*dn*beta+muN*e*p0+muN*e*dn-beta*sigma}, {mup^2*p0*r-muN^2*dn*r+mup^2*dn*r-mup*p0*sigma*H-muN*dn*sigma*H-mup*dn*sigma*H, e*dn*beta*sigma*H-muN*e*p0*r+e*p0*sigma*H+e*dn*sigma*H+beta*r*sigma-r*sigma}, {mup^2*p0*r-muN^2*dn*r+mup^2*dn*r-mup*p0*sigma*H-muN*dn*sigma*H-mup*dn*sigma*H, mu*dn*beta*sigma*H+muN*muH*dn*beta+mu*p0*sigma*H+mu*dn*sigma*H-muH*mup*p0-muH*mup*dn}, {mup^2*p0*r-muN^2*dn*r+mup^2*dn*r-mup*p0*sigma*H-muN*dn*sigma*H-mup*dn*sigma*H, mu*mup*p0*sigma*H+mu*muN*dn*sigma*H+mu*mup*dn*sigma*H-muH*mup^2*p0+muN^2*muH*dn-muH*mup^2*dn}, {mup^2*p0*r-muN^2*dn*r+mup^2*dn*r-mup*p0*sigma*H-muN*dn*sigma*H-mup*dn*sigma*H, muN^2*e*dn*r+muN*e*mup*dn*r-mup*r*sigma+sigma^2*H}, {mup^2*p0*r-muN^2*dn*r+mup^2*dn*r-mup*p0*sigma*H-muN*dn*sigma*H-mup*dn*sigma*H, muN^2*e*p0*r-muN*beta*r*sigma-beta*sigma^2*H+muN*r*sigma}, {mup^2*p0*r-muN^2*dn*r+mup^2*dn*r-mup*p0*sigma*H-muN*dn*sigma*H-mup*dn*sigma*H, muN^2*muH*e*dn+muN*muH*e*mup*dn+mu*sigma^2*H-muH*mup*sigma}, {mup^2*p0*r-muN^2*dn*r+mup^2*dn*r-mup*p0*sigma*H-muN*dn*sigma*H-mup*dn*sigma*H, muN^2*muH*e*p0-mu*beta*sigma^2*H-muN*muH*beta*sigma+muN*muH*sigma}, {mup^2*p0*r-muN^2*dn*r+mup^2*dn*r-mup*p0*sigma*H-muN*dn*sigma*H-mup*dn*sigma*H, e*dn^2*beta^2*H+2*e*p0*dn*beta*H+2*e*dn^2*beta*H+dn*beta^2*r+e*p0^2*H+2*e*p0*dn*H+e*dn^2*H-p0*r-dn*r}, {muN*e*dn*beta+muN*e*p0+muN*e*dn-beta*sigma, e*dn*beta*sigma*H-muN*e*p0*r+e*p0*sigma*H+e*dn*sigma*H+beta*r*sigma-r*sigma}, {muN*e*dn*beta+muN*e*p0+muN*e*dn-beta*sigma, mu*dn*beta*sigma*H+muN*muH*dn*beta+mu*p0*sigma*H+mu*dn*sigma*H-muH*mup*p0-muH*mup*dn}, {muN*e*dn*beta+muN*e*p0+muN*e*dn-beta*sigma, mu*mup*p0*sigma*H+mu*muN*dn*sigma*H+mu*mup*dn*sigma*H-muH*mup^2*p0+muN^2*muH*dn-muH*mup^2*dn}, {muN*e*dn*beta+muN*e*p0+muN*e*dn-beta*sigma, muN^2*e*dn*r+muN*e*mup*dn*r-mup*r*sigma+sigma^2*H}, {muN*e*dn*beta+muN*e*p0+muN*e*dn-beta*sigma, muN^2*e*p0*r-muN*beta*r*sigma-beta*sigma^2*H+muN*r*sigma}, {muN*e*dn*beta+muN*e*p0+muN*e*dn-beta*sigma, muN^2*muH*e*dn+muN*muH*e*mup*dn+mu*sigma^2*H-muH*mup*sigma}, {muN*e*dn*beta+muN*e*p0+muN*e*dn-beta*sigma, muN^2*muH*e*p0-mu*beta*sigma^2*H-muN*muH*beta*sigma+muN*muH*sigma}, {muN*e*dn*beta+muN*e*p0+muN*e*dn-beta*sigma, e*dn^2*beta^2*H+2*e*p0*dn*beta*H+2*e*dn^2*beta*H+dn*beta^2*r+e*p0^2*H+2*e*p0*dn*H+e*dn^2*H-p0*r-dn*r}, {e*dn*beta*sigma*H-muN*e*p0*r+e*p0*sigma*H+e*dn*sigma*H+beta*r*sigma-r*sigma, mu*dn*beta*sigma*H+muN*muH*dn*beta+mu*p0*sigma*H+mu*dn*sigma*H-muH*mup*p0-muH*mup*dn}, {e*dn*beta*sigma*H-muN*e*p0*r+e*p0*sigma*H+e*dn*sigma*H+beta*r*sigma-r*sigma, mu*mup*p0*sigma*H+mu*muN*dn*sigma*H+mu*mup*dn*sigma*H-muH*mup^2*p0+muN^2*muH*dn-muH*mup^2*dn}, {e*dn*beta*sigma*H-muN*e*p0*r+e*p0*sigma*H+e*dn*sigma*H+beta*r*sigma-r*sigma, muN^2*e*dn*r+muN*e*mup*dn*r-mup*r*sigma+sigma^2*H}, {e*dn*beta*sigma*H-muN*e*p0*r+e*p0*sigma*H+e*dn*sigma*H+beta*r*sigma-r*sigma, muN^2*e*p0*r-muN*beta*r*sigma-beta*sigma^2*H+muN*r*sigma}, {e*dn*beta*sigma*H-muN*e*p0*r+e*p0*sigma*H+e*dn*sigma*H+beta*r*sigma-r*sigma, muN^2*muH*e*dn+muN*muH*e*mup*dn+mu*sigma^2*H-muH*mup*sigma}, {e*dn*beta*sigma*H-muN*e*p0*r+e*p0*sigma*H+e*dn*sigma*H+beta*r*sigma-r*sigma, muN^2*muH*e*p0-mu*beta*sigma^2*H-muN*muH*beta*sigma+muN*muH*sigma}, {e*dn*beta*sigma*H-muN*e*p0*r+e*p0*sigma*H+e*dn*sigma*H+beta*r*sigma-r*sigma, e*dn^2*beta^2*H+2*e*p0*dn*beta*H+2*e*dn^2*beta*H+dn*beta^2*r+e*p0^2*H+2*e*p0*dn*H+e*dn^2*H-p0*r-dn*r}, {mu*dn*beta*sigma*H+muN*muH*dn*beta+mu*p0*sigma*H+mu*dn*sigma*H-muH*mup*p0-muH*mup*dn, mu*mup*p0*sigma*H+mu*muN*dn*sigma*H+mu*mup*dn*sigma*H-muH*mup^2*p0+muN^2*muH*dn-muH*mup^2*dn}, {mu*dn*beta*sigma*H+muN*muH*dn*beta+mu*p0*sigma*H+mu*dn*sigma*H-muH*mup*p0-muH*mup*dn, muN^2*e*dn*r+muN*e*mup*dn*r-mup*r*sigma+sigma^2*H}, {mu*dn*beta*sigma*H+muN*muH*dn*beta+mu*p0*sigma*H+mu*dn*sigma*H-muH*mup*p0-muH*mup*dn, muN^2*e*p0*r-muN*beta*r*sigma-beta*sigma^2*H+muN*r*sigma}, {mu*dn*beta*sigma*H+muN*muH*dn*beta+mu*p0*sigma*H+mu*dn*sigma*H-muH*mup*p0-muH*mup*dn, muN^2*muH*e*dn+muN*muH*e*mup*dn+mu*sigma^2*H-muH*mup*sigma}, {mu*dn*beta*sigma*H+muN*muH*dn*beta+mu*p0*sigma*H+mu*dn*sigma*H-muH*mup*p0-muH*mup*dn, muN^2*muH*e*p0-mu*beta*sigma^2*H-muN*muH*beta*sigma+muN*muH*sigma}, {mu*dn*beta*sigma*H+muN*muH*dn*beta+mu*p0*sigma*H+mu*dn*sigma*H-muH*mup*p0-muH*mup*dn, e*dn^2*beta^2*H+2*e*p0*dn*beta*H+2*e*dn^2*beta*H+dn*beta^2*r+e*p0^2*H+2*e*p0*dn*H+e*dn^2*H-p0*r-dn*r}, {mu*mup*p0*sigma*H+mu*muN*dn*sigma*H+mu*mup*dn*sigma*H-muH*mup^2*p0+muN^2*muH*dn-muH*mup^2*dn, muN^2*e*dn*r+muN*e*mup*dn*r-mup*r*sigma+sigma^2*H}, {mu*mup*p0*sigma*H+mu*muN*dn*sigma*H+mu*mup*dn*sigma*H-muH*mup^2*p0+muN^2*muH*dn-muH*mup^2*dn, muN^2*e*p0*r-muN*beta*r*sigma-beta*sigma^2*H+muN*r*sigma}, {mu*mup*p0*sigma*H+mu*muN*dn*sigma*H+mu*mup*dn*sigma*H-muH*mup^2*p0+muN^2*muH*dn-muH*mup^2*dn, muN^2*muH*e*dn+muN*muH*e*mup*dn+mu*sigma^2*H-muH*mup*sigma}, {mu*mup*p0*sigma*H+mu*muN*dn*sigma*H+mu*mup*dn*sigma*H-muH*mup^2*p0+muN^2*muH*dn-muH*mup^2*dn, muN^2*muH*e*p0-mu*beta*sigma^2*H-muN*muH*beta*sigma+muN*muH*sigma}, {mu*mup*p0*sigma*H+mu*muN*dn*sigma*H+mu*mup*dn*sigma*H-muH*mup^2*p0+muN^2*muH*dn-muH*mup^2*dn, e*dn^2*beta^2*H+2*e*p0*dn*beta*H+2*e*dn^2*beta*H+dn*beta^2*r+e*p0^2*H+2*e*p0*dn*H+e*dn^2*H-p0*r-dn*r}, {muN^2*e*dn*r+muN*e*mup*dn*r-mup*r*sigma+sigma^2*H, muN^2*e*p0*r-muN*beta*r*sigma-beta*sigma^2*H+muN*r*sigma}, {muN^2*e*dn*r+muN*e*mup*dn*r-mup*r*sigma+sigma^2*H, muN^2*muH*e*dn+muN*muH*e*mup*dn+mu*sigma^2*H-muH*mup*sigma}, {muN^2*e*dn*r+muN*e*mup*dn*r-mup*r*sigma+sigma^2*H, muN^2*muH*e*p0-mu*beta*sigma^2*H-muN*muH*beta*sigma+muN*muH*sigma}, {muN^2*e*dn*r+muN*e*mup*dn*r-mup*r*sigma+sigma^2*H, e*dn^2*beta^2*H+2*e*p0*dn*beta*H+2*e*dn^2*beta*H+dn*beta^2*r+e*p0^2*H+2*e*p0*dn*H+e*dn^2*H-p0*r-dn*r}, {muN^2*e*p0*r-muN*beta*r*sigma-beta*sigma^2*H+muN*r*sigma, muN^2*muH*e*dn+muN*muH*e*mup*dn+mu*sigma^2*H-muH*mup*sigma}, {muN^2*e*p0*r-muN*beta*r*sigma-beta*sigma^2*H+muN*r*sigma, muN^2*muH*e*p0-mu*beta*sigma^2*H-muN*muH*beta*sigma+muN*muH*sigma}, {muN^2*e*p0*r-muN*beta*r*sigma-beta*sigma^2*H+muN*r*sigma, e*dn^2*beta^2*H+2*e*p0*dn*beta*H+2*e*dn^2*beta*H+dn*beta^2*r+e*p0^2*H+2*e*p0*dn*H+e*dn^2*H-p0*r-dn*r}, {muN^2*muH*e*dn+muN*muH*e*mup*dn+mu*sigma^2*H-muH*mup*sigma, muN^2*muH*e*p0-mu*beta*sigma^2*H-muN*muH*beta*sigma+muN*muH*sigma}, {muN^2*muH*e*dn+muN*muH*e*mup*dn+mu*sigma^2*H-muH*mup*sigma, e*dn^2*beta^2*H+2*e*p0*dn*beta*H+2*e*dn^2*beta*H+dn*beta^2*r+e*p0^2*H+2*e*p0*dn*H+e*dn^2*H-p0*r-dn*r}, {muN^2*muH*e*p0-mu*beta*sigma^2*H-muN*muH*beta*sigma+muN*muH*sigma, e*dn^2*beta^2*H+2*e*p0*dn*beta*H+2*e*dn^2*beta*H+dn*beta^2*r+e*p0^2*H+2*e*p0*dn*H+e*dn^2*H-p0*r-dn*r}, {r}, {n-dn}, {muH}, {dp-dn}, {ph-p0-dn}, {dn*beta+p0+dn}, {e*mup*p0+muN*e*dn+e*mup*dn-sigma}, {r, n-dn}, {r, muH}, {r, dp-dn}, {r, ph-p0-dn}, {r, dn*beta+p0+dn}, {r, e*mup*p0+muN*e*dn+e*mup*dn-sigma}, {n-dn, muH}, {n-dn, dp-dn}, {n-dn, ph-p0-dn}, {n-dn, dn*beta+p0+dn}, {n-dn, e*mup*p0+muN*e*dn+e*mup*dn-sigma}, {muH, dp-dn}, {muH, ph-p0-dn}, {muH, dn*beta+p0+dn}, {muH, e*mup*p0+muN*e*dn+e*mup*dn-sigma}, {dp-dn, ph-p0-dn}, {dp-dn, dn*beta+p0+dn}, {dp-dn, e*mup*p0+muN*e*dn+e*mup*dn-sigma}, {ph-p0-dn, dn*beta+p0+dn}, {ph-p0-dn, e*mup*p0+muN*e*dn+e*mup*dn-sigma}, {dn*beta+p0+dn, e*mup*p0+muN*e*dn+e*mup*dn-sigma}, {sigma}, {r}, {e}, {n-dn}, {muH}, {dp-dn}, {ph-p0-dn}, {sigma, r}, {sigma, e}, {sigma, n-dn}, {sigma, muH}, {sigma, dp-dn}, {sigma, ph-p0-dn}, {r, e}, {r, n-dn}, {r, muH}, {r, dp-dn}, {r, ph-p0-dn}, {e, n-dn}, {e, muH}, {e, dp-dn}, {e, ph-p0-dn}, {n-dn, muH}, {n-dn, dp-dn}, {n-dn, ph-p0-dn}, {muH, dp-dn}, {muH, ph-p0-dn}, {dp-dn, ph-p0-dn}, {H}, {r}, {n-dn}, {muH}, {dp-dn}, {ph-p0-dn}, {e*mup*p0+muN*e*dn+e*mup*dn-sigma}, {H, r}, {H, n-dn}, {H, muH}, {H, dp-dn}, {H, ph-p0-dn}, {H, e*mup*p0+muN*e*dn+e*mup*dn-sigma}, {r, n-dn}, {r, muH}, {r, dp-dn}, {r, ph-p0-dn}, {r, e*mup*p0+muN*e*dn+e*mup*dn-sigma}, {n-dn, muH}, {n-dn, dp-dn}, {n-dn, ph-p0-dn}, {n-dn, e*mup*p0+muN*e*dn+e*mup*dn-sigma}, {muH, dp-dn}, {muH, ph-p0-dn}, {muH, e*mup*p0+muN*e*dn+e*mup*dn-sigma}, {dp-dn, ph-p0-dn}, {dp-dn, e*mup*p0+muN*e*dn+e*mup*dn-sigma}, {ph-p0-dn, e*mup*p0+muN*e*dn+e*mup*dn-sigma}, {dn}, {n}, {dp}, {ph-p0}, {mup*r-sigma*H}, {mu*r-muH}, {mu*sigma*H-muH*mup}, {e*p0*H-r}, {e*mup*p0-sigma}, {dn, n}, {dn, dp}, {dn, ph-p0}, {dn, mup*r-sigma*H}, {dn, mu*r-muH}, {dn, mu*sigma*H-muH*mup}, {dn, e*p0*H-r}, {dn, e*mup*p0-sigma}, {n, dp}, {n, ph-p0}, {n, mup*r-sigma*H}, {n, mu*r-muH}, {n, mu*sigma*H-muH*mup}, {n, e*p0*H-r}, {n, e*mup*p0-sigma}, {dp, ph-p0}, {dp, mup*r-sigma*H}, {dp, mu*r-muH}, {dp, mu*sigma*H-muH*mup}, {dp, e*p0*H-r}, {dp, e*mup*p0-sigma}, {ph-p0, mup*r-sigma*H}, {ph-p0, mu*r-muH}, {ph-p0, mu*sigma*H-muH*mup}, {ph-p0, e*p0*H-r}, {ph-p0, e*mup*p0-sigma}, {mup*r-sigma*H, mu*r-muH}, {mup*r-sigma*H, mu*sigma*H-muH*mup}, {mup*r-sigma*H, e*p0*H-r}, {mup*r-sigma*H, e*mup*p0-sigma}, {mu*r-muH, mu*sigma*H-muH*mup}, {mu*r-muH, e*p0*H-r}, {mu*r-muH, e*mup*p0-sigma}, {mu*sigma*H-muH*mup, e*p0*H-r}, {mu*sigma*H-muH*mup, e*mup*p0-sigma}, {e*p0*H-r, e*mup*p0-sigma}, {sigma}, {dn}, {p0}, {n}, {dp}, {ph}, {mu*r-muH}, {sigma, dn}, {sigma, p0}, {sigma, n}, {sigma, dp}, {sigma, ph}, {sigma, mu*r-muH}, {dn, p0}, {dn, n}, {dn, dp}, {dn, ph}, {dn, mu*r-muH}, {p0, n}, {p0, dp}, {p0, ph}, {p0, mu*r-muH}, {n, dp}, {n, ph}, {n, mu*r-muH}, {dp, ph}, {dp, mu*r-muH}, {ph, mu*r-muH}, {beta}, {n-dn}, {dp-dn}, {ph-p0-dn}, {mu*r-muH}, {e*p0*H+e*dn*H-r}, {mup*p0*r+muN*dn*r+mup*dn*r-p0*sigma*H-dn*sigma*H}, {e*mup*p0+muN*e*dn+e*mup*dn-sigma}, {mu*p0*sigma*H+mu*dn*sigma*H-muH*mup*p0-muN*muH*dn-muH*mup*dn}, {muN*e*dn*H+mup*r-sigma*H}, {beta, n-dn}, {beta, dp-dn}, {beta, ph-p0-dn}, {beta, mu*r-muH}, {beta, e*p0*H+e*dn*H-r}, {beta, mup*p0*r+muN*dn*r+mup*dn*r-p0*sigma*H-dn*sigma*H}, {beta, e*mup*p0+muN*e*dn+e*mup*dn-sigma}, {beta, mu*p0*sigma*H+mu*dn*sigma*H-muH*mup*p0-muN*muH*dn-muH*mup*dn}, {beta, muN*e*dn*H+mup*r-sigma*H}, {n-dn, dp-dn}, {n-dn, ph-p0-dn}, {n-dn, mu*r-muH}, {n-dn, e*p0*H+e*dn*H-r}, {n-dn, mup*p0*r+muN*dn*r+mup*dn*r-p0*sigma*H-dn*sigma*H}, {n-dn, e*mup*p0+muN*e*dn+e*mup*dn-sigma}, {n-dn, mu*p0*sigma*H+mu*dn*sigma*H-muH*mup*p0-muN*muH*dn-muH*mup*dn}, {n-dn, muN*e*dn*H+mup*r-sigma*H}, {dp-dn, ph-p0-dn}, {dp-dn, mu*r-muH}, {dp-dn, e*p0*H+e*dn*H-r}, {dp-dn, mup*p0*r+muN*dn*r+mup*dn*r-p0*sigma*H-dn*sigma*H}, {dp-dn, e*mup*p0+muN*e*dn+e*mup*dn-sigma}, {dp-dn, mu*p0*sigma*H+mu*dn*sigma*H-muH*mup*p0-muN*muH*dn-muH*mup*dn}, {dp-dn, muN*e*dn*H+mup*r-sigma*H}, {ph-p0-dn, mu*r-muH}, {ph-p0-dn, e*p0*H+e*dn*H-r}, {ph-p0-dn, mup*p0*r+muN*dn*r+mup*dn*r-p0*sigma*H-dn*sigma*H}, {ph-p0-dn, e*mup*p0+muN*e*dn+e*mup*dn-sigma}, {ph-p0-dn, mu*p0*sigma*H+mu*dn*sigma*H-muH*mup*p0-muN*muH*dn-muH*mup*dn}, {ph-p0-dn, muN*e*dn*H+mup*r-sigma*H}, {mu*r-muH, e*p0*H+e*dn*H-r}, {mu*r-muH, mup*p0*r+muN*dn*r+mup*dn*r-p0*sigma*H-dn*sigma*H}, {mu*r-muH, e*mup*p0+muN*e*dn+e*mup*dn-sigma}, {mu*r-muH, mu*p0*sigma*H+mu*dn*sigma*H-muH*mup*p0-muN*muH*dn-muH*mup*dn}, {mu*r-muH, muN*e*dn*H+mup*r-sigma*H}, {e*p0*H+e*dn*H-r, mup*p0*r+muN*dn*r+mup*dn*r-p0*sigma*H-dn*sigma*H}, {e*p0*H+e*dn*H-r, e*mup*p0+muN*e*dn+e*mup*dn-sigma}, {e*p0*H+e*dn*H-r, mu*p0*sigma*H+mu*dn*sigma*H-muH*mup*p0-muN*muH*dn-muH*mup*dn}, {e*p0*H+e*dn*H-r, muN*e*dn*H+mup*r-sigma*H}, {mup*p0*r+muN*dn*r+mup*dn*r-p0*sigma*H-dn*sigma*H, e*mup*p0+muN*e*dn+e*mup*dn-sigma}, {mup*p0*r+muN*dn*r+mup*dn*r-p0*sigma*H-dn*sigma*H, mu*p0*sigma*H+mu*dn*sigma*H-muH*mup*p0-muN*muH*dn-muH*mup*dn}, {mup*p0*r+muN*dn*r+mup*dn*r-p0*sigma*H-dn*sigma*H, muN*e*dn*H+mup*r-sigma*H}, {e*mup*p0+muN*e*dn+e*mup*dn-sigma, mu*p0*sigma*H+mu*dn*sigma*H-muH*mup*p0-muN*muH*dn-muH*mup*dn}, {e*mup*p0+muN*e*dn+e*mup*dn-sigma, muN*e*dn*H+mup*r-sigma*H}, {mu*p0*sigma*H+mu*dn*sigma*H-muH*mup*p0-muN*muH*dn-muH*mup*dn, muN*e*dn*H+mup*r-sigma*H}, {sigma}, {e}, {n-dn}, {dp-dn}, {ph-p0-dn}, {mu*r-muH}, {dn*beta^2-p0-dn}, {sigma, e}, {sigma, n-dn}, {sigma, dp-dn}, {sigma, ph-p0-dn}, {sigma, mu*r-muH}, {sigma, dn*beta^2-p0-dn}, {e, n-dn}, {e, dp-dn}, {e, ph-p0-dn}, {e, mu*r-muH}, {e, dn*beta^2-p0-dn}, {n-dn, dp-dn}, {n-dn, ph-p0-dn}, {n-dn, mu*r-muH}, {n-dn, dn*beta^2-p0-dn}, {dp-dn, ph-p0-dn}, {dp-dn, mu*r-muH}, {dp-dn, dn*beta^2-p0-dn}, {ph-p0-dn, mu*r-muH}, {ph-p0-dn, dn*beta^2-p0-dn}, {mu*r-muH, dn*beta^2-p0-dn}, {beta+1}, {n-dn}, {dp-dn}, {ph-p0-dn}, {mu*r-muH}, {e*p0*H-r}, {mup*p0*r+muN*dn*r+mup*dn*r-p0*sigma*H}, {e*mup*p0+muN*e*dn+e*mup*dn-sigma}, {mu*p0*sigma*H-muH*mup*p0-muN*muH*dn-muH*mup*dn}, {muN*e*dn*H+e*mup*dn*H+mup*r-sigma*H}, {beta+1, n-dn}, {beta+1, dp-dn}, {beta+1, ph-p0-dn}, {beta+1, mu*r-muH}, {beta+1, e*p0*H-r}, {beta+1, mup*p0*r+muN*dn*r+mup*dn*r-p0*sigma*H}, {beta+1, e*mup*p0+muN*e*dn+e*mup*dn-sigma}, {beta+1, mu*p0*sigma*H-muH*mup*p0-muN*muH*dn-muH*mup*dn}, {beta+1, muN*e*dn*H+e*mup*dn*H+mup*r-sigma*H}, {n-dn, dp-dn}, {n-dn, ph-p0-dn}, {n-dn, mu*r-muH}, {n-dn, e*p0*H-r}, {n-dn, mup*p0*r+muN*dn*r+mup*dn*r-p0*sigma*H}, {n-dn, e*mup*p0+muN*e*dn+e*mup*dn-sigma}, {n-dn, mu*p0*sigma*H-muH*mup*p0-muN*muH*dn-muH*mup*dn}, {n-dn, muN*e*dn*H+e*mup*dn*H+mup*r-sigma*H}, {dp-dn, ph-p0-dn}, {dp-dn, mu*r-muH}, {dp-dn, e*p0*H-r}, {dp-dn, mup*p0*r+muN*dn*r+mup*dn*r-p0*sigma*H}, {dp-dn, e*mup*p0+muN*e*dn+e*mup*dn-sigma}, {dp-dn, mu*p0*sigma*H-muH*mup*p0-muN*muH*dn-muH*mup*dn}, {dp-dn, muN*e*dn*H+e*mup*dn*H+mup*r-sigma*H}, {ph-p0-dn, mu*r-muH}, {ph-p0-dn, e*p0*H-r}, {ph-p0-dn, mup*p0*r+muN*dn*r+mup*dn*r-p0*sigma*H}, {ph-p0-dn, e*mup*p0+muN*e*dn+e*mup*dn-sigma}, {ph-p0-dn, mu*p0*sigma*H-muH*mup*p0-muN*muH*dn-muH*mup*dn}, {ph-p0-dn, muN*e*dn*H+e*mup*dn*H+mup*r-sigma*H}, {mu*r-muH, e*p0*H-r}, {mu*r-muH, mup*p0*r+muN*dn*r+mup*dn*r-p0*sigma*H}, {mu*r-muH, e*mup*p0+muN*e*dn+e*mup*dn-sigma}, {mu*r-muH, mu*p0*sigma*H-muH*mup*p0-muN*muH*dn-muH*mup*dn}, {mu*r-muH, muN*e*dn*H+e*mup*dn*H+mup*r-sigma*H}, {e*p0*H-r, mup*p0*r+muN*dn*r+mup*dn*r-p0*sigma*H}, {e*p0*H-r, e*mup*p0+muN*e*dn+e*mup*dn-sigma}, {e*p0*H-r, mu*p0*sigma*H-muH*mup*p0-muN*muH*dn-muH*mup*dn}, {e*p0*H-r, muN*e*dn*H+e*mup*dn*H+mup*r-sigma*H}, {mup*p0*r+muN*dn*r+mup*dn*r-p0*sigma*H, e*mup*p0+muN*e*dn+e*mup*dn-sigma}, {mup*p0*r+muN*dn*r+mup*dn*r-p0*sigma*H, mu*p0*sigma*H-muH*mup*p0-muN*muH*dn-muH*mup*dn}, {mup*p0*r+muN*dn*r+mup*dn*r-p0*sigma*H, muN*e*dn*H+e*mup*dn*H+mup*r-sigma*H}, {e*mup*p0+muN*e*dn+e*mup*dn-sigma, mu*p0*sigma*H-muH*mup*p0-muN*muH*dn-muH*mup*dn}, {e*mup*p0+muN*e*dn+e*mup*dn-sigma, muN*e*dn*H+e*mup*dn*H+mup*r-sigma*H}, {mu*p0*sigma*H-muH*mup*p0-muN*muH*dn-muH*mup*dn, muN*e*dn*H+e*mup*dn*H+mup*r-sigma*H}};

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
f = openOut "results/photoHall/abduction/noiseless/1_axiom(s)_removed/combo_1/reasoning/reasoning_output.txt";
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

print("Reasoning complete. Output written to results/photoHall/abduction/noiseless/1_axiom(s)_removed/combo_1/reasoning/reasoning_output.txt");
