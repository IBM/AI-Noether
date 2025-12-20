-- AI-Noether: Reasoning Template (Noiseless)
-- Tests if candidate axiom sets, when added to remaining axioms, prove targets

needsPackage("PrimaryDecomposition", Reload => true)

-- Ring definition
R = QQ[F, ad, T, Fd, omega, theta, sintheta, m, d, g, L, j, Pi, Tj, MonomialOrder => Lex];

-- Input data
remainingAxioms = toList([ad-g*sintheta, d-L*theta, Tj-j*T, sintheta - theta]);
qList = toList([d*g*Tj^2-4*d*L*j^2*Pi^2]);
k = #qList;

-- Per-target variable partitions
measuredPerTarget = {{d, g, L, j, Pi, Tj}};
nonMeasuredPerTarget = {{F, ad, T, Fd, omega, theta, sintheta, m}};

-- Candidate axiom sets to test (list of lists)
candidateSets = {{}, {L}, {d}, {theta-sintheta}, {T*j-Tj}, {sintheta*g-ad}, {L, d}, {L, theta-sintheta}, {L, T*j-Tj}, {L, sintheta*g-ad}, {d, theta-sintheta}, {d, T*j-Tj}, {d, sintheta*g-ad}, {theta-sintheta, T*j-Tj}, {theta-sintheta, sintheta*g-ad}, {T*j-Tj, sintheta*g-ad}, {L, d, theta-sintheta}, {L, d, T*j-Tj}, {L, d, sintheta*g-ad}, {L, theta-sintheta, T*j-Tj}, {L, theta-sintheta, sintheta*g-ad}, {L, T*j-Tj, sintheta*g-ad}, {d, theta-sintheta, T*j-Tj}, {d, theta-sintheta, sintheta*g-ad}, {d, T*j-Tj, sintheta*g-ad}, {theta-sintheta, T*j-Tj, sintheta*g-ad}, {L, d, theta-sintheta, T*j-Tj}, {L, d, theta-sintheta, sintheta*g-ad}, {L, d, T*j-Tj, sintheta*g-ad}, {L, theta-sintheta, T*j-Tj, sintheta*g-ad}, {d, theta-sintheta, T*j-Tj, sintheta*g-ad}, {d}, {sintheta}, {theta}, {ad}, {T*j-Tj}, {d, sintheta}, {d, theta}, {d, ad}, {d, T*j-Tj}, {sintheta, theta}, {sintheta, ad}, {sintheta, T*j-Tj}, {theta, ad}, {theta, T*j-Tj}, {ad, T*j-Tj}, {d, sintheta, theta}, {d, sintheta, ad}, {d, sintheta, T*j-Tj}, {d, theta, ad}, {d, theta, T*j-Tj}, {d, ad, T*j-Tj}, {sintheta, theta, ad}, {sintheta, theta, T*j-Tj}, {sintheta, ad, T*j-Tj}, {theta, ad, T*j-Tj}, {d, sintheta, theta, ad}, {d, sintheta, theta, T*j-Tj}, {d, sintheta, ad, T*j-Tj}, {d, theta, ad, T*j-Tj}, {sintheta, theta, ad, T*j-Tj}, {Tj}, {j}, {theta-sintheta}, {sintheta*L-d}, {d*g-ad*L}, {sintheta*g-ad}, {Tj, j}, {Tj, theta-sintheta}, {Tj, sintheta*L-d}, {Tj, d*g-ad*L}, {Tj, sintheta*g-ad}, {j, theta-sintheta}, {j, sintheta*L-d}, {j, d*g-ad*L}, {j, sintheta*g-ad}, {theta-sintheta, sintheta*L-d}, {theta-sintheta, d*g-ad*L}, {theta-sintheta, sintheta*g-ad}, {sintheta*L-d, d*g-ad*L}, {sintheta*L-d, sintheta*g-ad}, {d*g-ad*L, sintheta*g-ad}, {Tj, j, theta-sintheta}, {Tj, j, sintheta*L-d}, {Tj, j, d*g-ad*L}, {Tj, j, sintheta*g-ad}, {Tj, theta-sintheta, sintheta*L-d}, {Tj, theta-sintheta, d*g-ad*L}, {Tj, theta-sintheta, sintheta*g-ad}, {Tj, sintheta*L-d, d*g-ad*L}, {Tj, sintheta*L-d, sintheta*g-ad}, {Tj, d*g-ad*L, sintheta*g-ad}, {j, theta-sintheta, sintheta*L-d}, {j, theta-sintheta, d*g-ad*L}, {j, theta-sintheta, sintheta*g-ad}, {j, sintheta*L-d, d*g-ad*L}, {j, sintheta*L-d, sintheta*g-ad}, {j, d*g-ad*L, sintheta*g-ad}, {theta-sintheta, sintheta*L-d, d*g-ad*L}, {theta-sintheta, sintheta*L-d, sintheta*g-ad}, {theta-sintheta, d*g-ad*L, sintheta*g-ad}, {sintheta*L-d, d*g-ad*L, sintheta*g-ad}, {Tj, j, theta-sintheta, sintheta*L-d}, {Tj, j, theta-sintheta, d*g-ad*L}, {Tj, j, theta-sintheta, sintheta*g-ad}, {Tj, j, sintheta*L-d, d*g-ad*L}, {Tj, j, sintheta*L-d, sintheta*g-ad}, {Tj, j, d*g-ad*L, sintheta*g-ad}, {Tj, theta-sintheta, sintheta*L-d, d*g-ad*L}, {Tj, theta-sintheta, sintheta*L-d, sintheta*g-ad}, {Tj, theta-sintheta, d*g-ad*L, sintheta*g-ad}, {Tj, sintheta*L-d, d*g-ad*L, sintheta*g-ad}, {j, theta-sintheta, sintheta*L-d, d*g-ad*L}, {j, theta-sintheta, sintheta*L-d, sintheta*g-ad}, {j, theta-sintheta, d*g-ad*L, sintheta*g-ad}, {j, sintheta*L-d, d*g-ad*L, sintheta*g-ad}, {theta-sintheta, sintheta*L-d, d*g-ad*L, sintheta*g-ad}, {theta-sintheta}, {T*j-Tj}, {sintheta*L-d}, {d*g-ad*L}, {sintheta*g-ad}, {T^2*g-4*L*Pi^2}, {ad*T^2-4*d*Pi^2}, {4*L*j*Pi^2-T*g*Tj}, {4*d*j*Pi^2-ad*T*Tj}, {theta-sintheta, T*j-Tj}, {theta-sintheta, sintheta*L-d}, {theta-sintheta, d*g-ad*L}, {theta-sintheta, sintheta*g-ad}, {theta-sintheta, T^2*g-4*L*Pi^2}, {theta-sintheta, ad*T^2-4*d*Pi^2}, {theta-sintheta, 4*L*j*Pi^2-T*g*Tj}, {theta-sintheta, 4*d*j*Pi^2-ad*T*Tj}, {T*j-Tj, sintheta*L-d}, {T*j-Tj, d*g-ad*L}, {T*j-Tj, sintheta*g-ad}, {T*j-Tj, T^2*g-4*L*Pi^2}, {T*j-Tj, ad*T^2-4*d*Pi^2}, {T*j-Tj, 4*L*j*Pi^2-T*g*Tj}, {T*j-Tj, 4*d*j*Pi^2-ad*T*Tj}, {sintheta*L-d, d*g-ad*L}, {sintheta*L-d, sintheta*g-ad}, {sintheta*L-d, T^2*g-4*L*Pi^2}, {sintheta*L-d, ad*T^2-4*d*Pi^2}, {sintheta*L-d, 4*L*j*Pi^2-T*g*Tj}, {sintheta*L-d, 4*d*j*Pi^2-ad*T*Tj}, {d*g-ad*L, sintheta*g-ad}, {d*g-ad*L, T^2*g-4*L*Pi^2}, {d*g-ad*L, ad*T^2-4*d*Pi^2}, {d*g-ad*L, 4*L*j*Pi^2-T*g*Tj}, {d*g-ad*L, 4*d*j*Pi^2-ad*T*Tj}, {sintheta*g-ad, T^2*g-4*L*Pi^2}, {sintheta*g-ad, ad*T^2-4*d*Pi^2}, {sintheta*g-ad, 4*L*j*Pi^2-T*g*Tj}, {sintheta*g-ad, 4*d*j*Pi^2-ad*T*Tj}, {T^2*g-4*L*Pi^2, ad*T^2-4*d*Pi^2}, {T^2*g-4*L*Pi^2, 4*L*j*Pi^2-T*g*Tj}, {T^2*g-4*L*Pi^2, 4*d*j*Pi^2-ad*T*Tj}, {ad*T^2-4*d*Pi^2, 4*L*j*Pi^2-T*g*Tj}, {ad*T^2-4*d*Pi^2, 4*d*j*Pi^2-ad*T*Tj}, {4*L*j*Pi^2-T*g*Tj, 4*d*j*Pi^2-ad*T*Tj}, {theta-sintheta, T*j-Tj, sintheta*L-d}, {theta-sintheta, T*j-Tj, d*g-ad*L}, {theta-sintheta, T*j-Tj, sintheta*g-ad}, {theta-sintheta, T*j-Tj, T^2*g-4*L*Pi^2}, {theta-sintheta, T*j-Tj, ad*T^2-4*d*Pi^2}, {theta-sintheta, T*j-Tj, 4*L*j*Pi^2-T*g*Tj}, {theta-sintheta, T*j-Tj, 4*d*j*Pi^2-ad*T*Tj}, {theta-sintheta, sintheta*L-d, d*g-ad*L}, {theta-sintheta, sintheta*L-d, sintheta*g-ad}, {theta-sintheta, sintheta*L-d, T^2*g-4*L*Pi^2}, {theta-sintheta, sintheta*L-d, ad*T^2-4*d*Pi^2}, {theta-sintheta, sintheta*L-d, 4*L*j*Pi^2-T*g*Tj}, {theta-sintheta, sintheta*L-d, 4*d*j*Pi^2-ad*T*Tj}, {theta-sintheta, d*g-ad*L, sintheta*g-ad}, {theta-sintheta, d*g-ad*L, T^2*g-4*L*Pi^2}, {theta-sintheta, d*g-ad*L, ad*T^2-4*d*Pi^2}, {theta-sintheta, d*g-ad*L, 4*L*j*Pi^2-T*g*Tj}, {theta-sintheta, d*g-ad*L, 4*d*j*Pi^2-ad*T*Tj}, {theta-sintheta, sintheta*g-ad, T^2*g-4*L*Pi^2}, {theta-sintheta, sintheta*g-ad, ad*T^2-4*d*Pi^2}, {theta-sintheta, sintheta*g-ad, 4*L*j*Pi^2-T*g*Tj}, {theta-sintheta, sintheta*g-ad, 4*d*j*Pi^2-ad*T*Tj}, {theta-sintheta, T^2*g-4*L*Pi^2, ad*T^2-4*d*Pi^2}, {theta-sintheta, T^2*g-4*L*Pi^2, 4*L*j*Pi^2-T*g*Tj}, {theta-sintheta, T^2*g-4*L*Pi^2, 4*d*j*Pi^2-ad*T*Tj}, {theta-sintheta, ad*T^2-4*d*Pi^2, 4*L*j*Pi^2-T*g*Tj}, {theta-sintheta, ad*T^2-4*d*Pi^2, 4*d*j*Pi^2-ad*T*Tj}, {theta-sintheta, 4*L*j*Pi^2-T*g*Tj, 4*d*j*Pi^2-ad*T*Tj}, {T*j-Tj, sintheta*L-d, d*g-ad*L}, {T*j-Tj, sintheta*L-d, sintheta*g-ad}, {T*j-Tj, sintheta*L-d, T^2*g-4*L*Pi^2}, {T*j-Tj, sintheta*L-d, ad*T^2-4*d*Pi^2}, {T*j-Tj, sintheta*L-d, 4*L*j*Pi^2-T*g*Tj}, {T*j-Tj, sintheta*L-d, 4*d*j*Pi^2-ad*T*Tj}, {T*j-Tj, d*g-ad*L, sintheta*g-ad}, {T*j-Tj, d*g-ad*L, T^2*g-4*L*Pi^2}, {T*j-Tj, d*g-ad*L, ad*T^2-4*d*Pi^2}, {T*j-Tj, d*g-ad*L, 4*L*j*Pi^2-T*g*Tj}, {T*j-Tj, d*g-ad*L, 4*d*j*Pi^2-ad*T*Tj}, {T*j-Tj, sintheta*g-ad, T^2*g-4*L*Pi^2}, {T*j-Tj, sintheta*g-ad, ad*T^2-4*d*Pi^2}, {T*j-Tj, sintheta*g-ad, 4*L*j*Pi^2-T*g*Tj}, {T*j-Tj, sintheta*g-ad, 4*d*j*Pi^2-ad*T*Tj}, {T*j-Tj, T^2*g-4*L*Pi^2, ad*T^2-4*d*Pi^2}, {T*j-Tj, T^2*g-4*L*Pi^2, 4*L*j*Pi^2-T*g*Tj}, {T*j-Tj, T^2*g-4*L*Pi^2, 4*d*j*Pi^2-ad*T*Tj}, {T*j-Tj, ad*T^2-4*d*Pi^2, 4*L*j*Pi^2-T*g*Tj}, {T*j-Tj, ad*T^2-4*d*Pi^2, 4*d*j*Pi^2-ad*T*Tj}, {T*j-Tj, 4*L*j*Pi^2-T*g*Tj, 4*d*j*Pi^2-ad*T*Tj}, {sintheta*L-d, d*g-ad*L, sintheta*g-ad}, {sintheta*L-d, d*g-ad*L, T^2*g-4*L*Pi^2}, {sintheta*L-d, d*g-ad*L, ad*T^2-4*d*Pi^2}, {sintheta*L-d, d*g-ad*L, 4*L*j*Pi^2-T*g*Tj}, {sintheta*L-d, d*g-ad*L, 4*d*j*Pi^2-ad*T*Tj}, {sintheta*L-d, sintheta*g-ad, T^2*g-4*L*Pi^2}, {sintheta*L-d, sintheta*g-ad, ad*T^2-4*d*Pi^2}, {sintheta*L-d, sintheta*g-ad, 4*L*j*Pi^2-T*g*Tj}, {sintheta*L-d, sintheta*g-ad, 4*d*j*Pi^2-ad*T*Tj}, {sintheta*L-d, T^2*g-4*L*Pi^2, ad*T^2-4*d*Pi^2}, {sintheta*L-d, T^2*g-4*L*Pi^2, 4*L*j*Pi^2-T*g*Tj}, {sintheta*L-d, T^2*g-4*L*Pi^2, 4*d*j*Pi^2-ad*T*Tj}, {sintheta*L-d, ad*T^2-4*d*Pi^2, 4*L*j*Pi^2-T*g*Tj}, {sintheta*L-d, ad*T^2-4*d*Pi^2, 4*d*j*Pi^2-ad*T*Tj}, {sintheta*L-d, 4*L*j*Pi^2-T*g*Tj, 4*d*j*Pi^2-ad*T*Tj}, {d*g-ad*L, sintheta*g-ad, T^2*g-4*L*Pi^2}, {d*g-ad*L, sintheta*g-ad, ad*T^2-4*d*Pi^2}, {d*g-ad*L, sintheta*g-ad, 4*L*j*Pi^2-T*g*Tj}, {d*g-ad*L, sintheta*g-ad, 4*d*j*Pi^2-ad*T*Tj}, {d*g-ad*L, T^2*g-4*L*Pi^2, ad*T^2-4*d*Pi^2}, {d*g-ad*L, T^2*g-4*L*Pi^2, 4*L*j*Pi^2-T*g*Tj}, {d*g-ad*L, T^2*g-4*L*Pi^2, 4*d*j*Pi^2-ad*T*Tj}, {d*g-ad*L, ad*T^2-4*d*Pi^2, 4*L*j*Pi^2-T*g*Tj}, {d*g-ad*L, ad*T^2-4*d*Pi^2, 4*d*j*Pi^2-ad*T*Tj}, {d*g-ad*L, 4*L*j*Pi^2-T*g*Tj, 4*d*j*Pi^2-ad*T*Tj}, {sintheta*g-ad, T^2*g-4*L*Pi^2, ad*T^2-4*d*Pi^2}, {sintheta*g-ad, T^2*g-4*L*Pi^2, 4*L*j*Pi^2-T*g*Tj}, {sintheta*g-ad, T^2*g-4*L*Pi^2, 4*d*j*Pi^2-ad*T*Tj}, {sintheta*g-ad, ad*T^2-4*d*Pi^2, 4*L*j*Pi^2-T*g*Tj}, {sintheta*g-ad, ad*T^2-4*d*Pi^2, 4*d*j*Pi^2-ad*T*Tj}, {sintheta*g-ad, 4*L*j*Pi^2-T*g*Tj, 4*d*j*Pi^2-ad*T*Tj}, {T^2*g-4*L*Pi^2, ad*T^2-4*d*Pi^2, 4*L*j*Pi^2-T*g*Tj}, {T^2*g-4*L*Pi^2, ad*T^2-4*d*Pi^2, 4*d*j*Pi^2-ad*T*Tj}, {T^2*g-4*L*Pi^2, 4*L*j*Pi^2-T*g*Tj, 4*d*j*Pi^2-ad*T*Tj}, {ad*T^2-4*d*Pi^2, 4*L*j*Pi^2-T*g*Tj, 4*d*j*Pi^2-ad*T*Tj}, {theta-sintheta, T*j-Tj, sintheta*L-d, d*g-ad*L}, {theta-sintheta, T*j-Tj, sintheta*L-d, sintheta*g-ad}, {theta-sintheta, T*j-Tj, sintheta*L-d, T^2*g-4*L*Pi^2}, {theta-sintheta, T*j-Tj, sintheta*L-d, ad*T^2-4*d*Pi^2}, {theta-sintheta, T*j-Tj, sintheta*L-d, 4*L*j*Pi^2-T*g*Tj}, {theta-sintheta, T*j-Tj, sintheta*L-d, 4*d*j*Pi^2-ad*T*Tj}, {theta-sintheta, T*j-Tj, d*g-ad*L, sintheta*g-ad}, {theta-sintheta, T*j-Tj, d*g-ad*L, T^2*g-4*L*Pi^2}, {theta-sintheta, T*j-Tj, d*g-ad*L, ad*T^2-4*d*Pi^2}, {theta-sintheta, T*j-Tj, d*g-ad*L, 4*L*j*Pi^2-T*g*Tj}, {theta-sintheta, T*j-Tj, d*g-ad*L, 4*d*j*Pi^2-ad*T*Tj}, {theta-sintheta, T*j-Tj, sintheta*g-ad, T^2*g-4*L*Pi^2}, {theta-sintheta, T*j-Tj, sintheta*g-ad, ad*T^2-4*d*Pi^2}, {theta-sintheta, T*j-Tj, sintheta*g-ad, 4*L*j*Pi^2-T*g*Tj}, {theta-sintheta, T*j-Tj, sintheta*g-ad, 4*d*j*Pi^2-ad*T*Tj}, {theta-sintheta, T*j-Tj, T^2*g-4*L*Pi^2, ad*T^2-4*d*Pi^2}, {theta-sintheta, T*j-Tj, T^2*g-4*L*Pi^2, 4*L*j*Pi^2-T*g*Tj}, {theta-sintheta, T*j-Tj, T^2*g-4*L*Pi^2, 4*d*j*Pi^2-ad*T*Tj}, {theta-sintheta, T*j-Tj, ad*T^2-4*d*Pi^2, 4*L*j*Pi^2-T*g*Tj}, {theta-sintheta, T*j-Tj, ad*T^2-4*d*Pi^2, 4*d*j*Pi^2-ad*T*Tj}, {theta-sintheta, T*j-Tj, 4*L*j*Pi^2-T*g*Tj, 4*d*j*Pi^2-ad*T*Tj}, {theta-sintheta, sintheta*L-d, d*g-ad*L, sintheta*g-ad}, {theta-sintheta, sintheta*L-d, d*g-ad*L, T^2*g-4*L*Pi^2}, {theta-sintheta, sintheta*L-d, d*g-ad*L, ad*T^2-4*d*Pi^2}, {theta-sintheta, sintheta*L-d, d*g-ad*L, 4*L*j*Pi^2-T*g*Tj}, {theta-sintheta, sintheta*L-d, d*g-ad*L, 4*d*j*Pi^2-ad*T*Tj}, {theta-sintheta, sintheta*L-d, sintheta*g-ad, T^2*g-4*L*Pi^2}, {theta-sintheta, sintheta*L-d, sintheta*g-ad, ad*T^2-4*d*Pi^2}, {theta-sintheta, sintheta*L-d, sintheta*g-ad, 4*L*j*Pi^2-T*g*Tj}, {theta-sintheta, sintheta*L-d, sintheta*g-ad, 4*d*j*Pi^2-ad*T*Tj}, {theta-sintheta, sintheta*L-d, T^2*g-4*L*Pi^2, ad*T^2-4*d*Pi^2}, {theta-sintheta, sintheta*L-d, T^2*g-4*L*Pi^2, 4*L*j*Pi^2-T*g*Tj}, {theta-sintheta, sintheta*L-d, T^2*g-4*L*Pi^2, 4*d*j*Pi^2-ad*T*Tj}, {theta-sintheta, sintheta*L-d, ad*T^2-4*d*Pi^2, 4*L*j*Pi^2-T*g*Tj}, {theta-sintheta, sintheta*L-d, ad*T^2-4*d*Pi^2, 4*d*j*Pi^2-ad*T*Tj}, {theta-sintheta, sintheta*L-d, 4*L*j*Pi^2-T*g*Tj, 4*d*j*Pi^2-ad*T*Tj}, {theta-sintheta, d*g-ad*L, sintheta*g-ad, T^2*g-4*L*Pi^2}, {theta-sintheta, d*g-ad*L, sintheta*g-ad, ad*T^2-4*d*Pi^2}, {theta-sintheta, d*g-ad*L, sintheta*g-ad, 4*L*j*Pi^2-T*g*Tj}, {theta-sintheta, d*g-ad*L, sintheta*g-ad, 4*d*j*Pi^2-ad*T*Tj}, {theta-sintheta, d*g-ad*L, T^2*g-4*L*Pi^2, ad*T^2-4*d*Pi^2}, {theta-sintheta, d*g-ad*L, T^2*g-4*L*Pi^2, 4*L*j*Pi^2-T*g*Tj}, {theta-sintheta, d*g-ad*L, T^2*g-4*L*Pi^2, 4*d*j*Pi^2-ad*T*Tj}, {theta-sintheta, d*g-ad*L, ad*T^2-4*d*Pi^2, 4*L*j*Pi^2-T*g*Tj}, {theta-sintheta, d*g-ad*L, ad*T^2-4*d*Pi^2, 4*d*j*Pi^2-ad*T*Tj}, {theta-sintheta, d*g-ad*L, 4*L*j*Pi^2-T*g*Tj, 4*d*j*Pi^2-ad*T*Tj}, {theta-sintheta, sintheta*g-ad, T^2*g-4*L*Pi^2, ad*T^2-4*d*Pi^2}, {theta-sintheta, sintheta*g-ad, T^2*g-4*L*Pi^2, 4*L*j*Pi^2-T*g*Tj}, {theta-sintheta, sintheta*g-ad, T^2*g-4*L*Pi^2, 4*d*j*Pi^2-ad*T*Tj}, {theta-sintheta, sintheta*g-ad, ad*T^2-4*d*Pi^2, 4*L*j*Pi^2-T*g*Tj}, {theta-sintheta, sintheta*g-ad, ad*T^2-4*d*Pi^2, 4*d*j*Pi^2-ad*T*Tj}, {theta-sintheta, sintheta*g-ad, 4*L*j*Pi^2-T*g*Tj, 4*d*j*Pi^2-ad*T*Tj}, {theta-sintheta, T^2*g-4*L*Pi^2, ad*T^2-4*d*Pi^2, 4*L*j*Pi^2-T*g*Tj}, {theta-sintheta, T^2*g-4*L*Pi^2, ad*T^2-4*d*Pi^2, 4*d*j*Pi^2-ad*T*Tj}, {theta-sintheta, T^2*g-4*L*Pi^2, 4*L*j*Pi^2-T*g*Tj, 4*d*j*Pi^2-ad*T*Tj}, {theta-sintheta, ad*T^2-4*d*Pi^2, 4*L*j*Pi^2-T*g*Tj, 4*d*j*Pi^2-ad*T*Tj}, {T*j-Tj, sintheta*L-d, d*g-ad*L, sintheta*g-ad}, {T*j-Tj, sintheta*L-d, d*g-ad*L, T^2*g-4*L*Pi^2}, {T*j-Tj, sintheta*L-d, d*g-ad*L, ad*T^2-4*d*Pi^2}, {T*j-Tj, sintheta*L-d, d*g-ad*L, 4*L*j*Pi^2-T*g*Tj}, {T*j-Tj, sintheta*L-d, d*g-ad*L, 4*d*j*Pi^2-ad*T*Tj}, {T*j-Tj, sintheta*L-d, sintheta*g-ad, T^2*g-4*L*Pi^2}, {T*j-Tj, sintheta*L-d, sintheta*g-ad, ad*T^2-4*d*Pi^2}, {T*j-Tj, sintheta*L-d, sintheta*g-ad, 4*L*j*Pi^2-T*g*Tj}, {T*j-Tj, sintheta*L-d, sintheta*g-ad, 4*d*j*Pi^2-ad*T*Tj}, {T*j-Tj, sintheta*L-d, T^2*g-4*L*Pi^2, ad*T^2-4*d*Pi^2}, {T*j-Tj, sintheta*L-d, T^2*g-4*L*Pi^2, 4*L*j*Pi^2-T*g*Tj}, {T*j-Tj, sintheta*L-d, T^2*g-4*L*Pi^2, 4*d*j*Pi^2-ad*T*Tj}, {T*j-Tj, sintheta*L-d, ad*T^2-4*d*Pi^2, 4*L*j*Pi^2-T*g*Tj}, {T*j-Tj, sintheta*L-d, ad*T^2-4*d*Pi^2, 4*d*j*Pi^2-ad*T*Tj}, {T*j-Tj, sintheta*L-d, 4*L*j*Pi^2-T*g*Tj, 4*d*j*Pi^2-ad*T*Tj}, {T*j-Tj, d*g-ad*L, sintheta*g-ad, T^2*g-4*L*Pi^2}, {T*j-Tj, d*g-ad*L, sintheta*g-ad, ad*T^2-4*d*Pi^2}, {T*j-Tj, d*g-ad*L, sintheta*g-ad, 4*L*j*Pi^2-T*g*Tj}, {T*j-Tj, d*g-ad*L, sintheta*g-ad, 4*d*j*Pi^2-ad*T*Tj}, {T*j-Tj, d*g-ad*L, T^2*g-4*L*Pi^2, ad*T^2-4*d*Pi^2}, {T*j-Tj, d*g-ad*L, T^2*g-4*L*Pi^2, 4*L*j*Pi^2-T*g*Tj}, {T*j-Tj, d*g-ad*L, T^2*g-4*L*Pi^2, 4*d*j*Pi^2-ad*T*Tj}, {T*j-Tj, d*g-ad*L, ad*T^2-4*d*Pi^2, 4*L*j*Pi^2-T*g*Tj}, {T*j-Tj, d*g-ad*L, ad*T^2-4*d*Pi^2, 4*d*j*Pi^2-ad*T*Tj}, {T*j-Tj, d*g-ad*L, 4*L*j*Pi^2-T*g*Tj, 4*d*j*Pi^2-ad*T*Tj}, {T*j-Tj, sintheta*g-ad, T^2*g-4*L*Pi^2, ad*T^2-4*d*Pi^2}, {T*j-Tj, sintheta*g-ad, T^2*g-4*L*Pi^2, 4*L*j*Pi^2-T*g*Tj}, {T*j-Tj, sintheta*g-ad, T^2*g-4*L*Pi^2, 4*d*j*Pi^2-ad*T*Tj}, {T*j-Tj, sintheta*g-ad, ad*T^2-4*d*Pi^2, 4*L*j*Pi^2-T*g*Tj}, {T*j-Tj, sintheta*g-ad, ad*T^2-4*d*Pi^2, 4*d*j*Pi^2-ad*T*Tj}, {T*j-Tj, sintheta*g-ad, 4*L*j*Pi^2-T*g*Tj, 4*d*j*Pi^2-ad*T*Tj}, {T*j-Tj, T^2*g-4*L*Pi^2, ad*T^2-4*d*Pi^2, 4*L*j*Pi^2-T*g*Tj}, {T*j-Tj, T^2*g-4*L*Pi^2, ad*T^2-4*d*Pi^2, 4*d*j*Pi^2-ad*T*Tj}, {T*j-Tj, T^2*g-4*L*Pi^2, 4*L*j*Pi^2-T*g*Tj, 4*d*j*Pi^2-ad*T*Tj}, {T*j-Tj, ad*T^2-4*d*Pi^2, 4*L*j*Pi^2-T*g*Tj, 4*d*j*Pi^2-ad*T*Tj}, {sintheta*L-d, d*g-ad*L, sintheta*g-ad, T^2*g-4*L*Pi^2}, {sintheta*L-d, d*g-ad*L, sintheta*g-ad, ad*T^2-4*d*Pi^2}, {sintheta*L-d, d*g-ad*L, sintheta*g-ad, 4*L*j*Pi^2-T*g*Tj}, {sintheta*L-d, d*g-ad*L, sintheta*g-ad, 4*d*j*Pi^2-ad*T*Tj}, {sintheta*L-d, d*g-ad*L, T^2*g-4*L*Pi^2, ad*T^2-4*d*Pi^2}, {sintheta*L-d, d*g-ad*L, T^2*g-4*L*Pi^2, 4*L*j*Pi^2-T*g*Tj}, {sintheta*L-d, d*g-ad*L, T^2*g-4*L*Pi^2, 4*d*j*Pi^2-ad*T*Tj}, {sintheta*L-d, d*g-ad*L, ad*T^2-4*d*Pi^2, 4*L*j*Pi^2-T*g*Tj}, {sintheta*L-d, d*g-ad*L, ad*T^2-4*d*Pi^2, 4*d*j*Pi^2-ad*T*Tj}, {sintheta*L-d, d*g-ad*L, 4*L*j*Pi^2-T*g*Tj, 4*d*j*Pi^2-ad*T*Tj}, {sintheta*L-d, sintheta*g-ad, T^2*g-4*L*Pi^2, ad*T^2-4*d*Pi^2}, {sintheta*L-d, sintheta*g-ad, T^2*g-4*L*Pi^2, 4*L*j*Pi^2-T*g*Tj}, {sintheta*L-d, sintheta*g-ad, T^2*g-4*L*Pi^2, 4*d*j*Pi^2-ad*T*Tj}, {sintheta*L-d, sintheta*g-ad, ad*T^2-4*d*Pi^2, 4*L*j*Pi^2-T*g*Tj}, {sintheta*L-d, sintheta*g-ad, ad*T^2-4*d*Pi^2, 4*d*j*Pi^2-ad*T*Tj}, {sintheta*L-d, sintheta*g-ad, 4*L*j*Pi^2-T*g*Tj, 4*d*j*Pi^2-ad*T*Tj}, {sintheta*L-d, T^2*g-4*L*Pi^2, ad*T^2-4*d*Pi^2, 4*L*j*Pi^2-T*g*Tj}, {sintheta*L-d, T^2*g-4*L*Pi^2, ad*T^2-4*d*Pi^2, 4*d*j*Pi^2-ad*T*Tj}, {sintheta*L-d, T^2*g-4*L*Pi^2, 4*L*j*Pi^2-T*g*Tj, 4*d*j*Pi^2-ad*T*Tj}, {sintheta*L-d, ad*T^2-4*d*Pi^2, 4*L*j*Pi^2-T*g*Tj, 4*d*j*Pi^2-ad*T*Tj}, {d*g-ad*L, sintheta*g-ad, T^2*g-4*L*Pi^2, ad*T^2-4*d*Pi^2}, {d*g-ad*L, sintheta*g-ad, T^2*g-4*L*Pi^2, 4*L*j*Pi^2-T*g*Tj}, {d*g-ad*L, sintheta*g-ad, T^2*g-4*L*Pi^2, 4*d*j*Pi^2-ad*T*Tj}, {d*g-ad*L, sintheta*g-ad, ad*T^2-4*d*Pi^2, 4*L*j*Pi^2-T*g*Tj}, {d*g-ad*L, sintheta*g-ad, ad*T^2-4*d*Pi^2, 4*d*j*Pi^2-ad*T*Tj}, {d*g-ad*L, sintheta*g-ad, 4*L*j*Pi^2-T*g*Tj, 4*d*j*Pi^2-ad*T*Tj}, {d*g-ad*L, T^2*g-4*L*Pi^2, ad*T^2-4*d*Pi^2, 4*L*j*Pi^2-T*g*Tj}, {d*g-ad*L, T^2*g-4*L*Pi^2, ad*T^2-4*d*Pi^2, 4*d*j*Pi^2-ad*T*Tj}, {d*g-ad*L, T^2*g-4*L*Pi^2, 4*L*j*Pi^2-T*g*Tj, 4*d*j*Pi^2-ad*T*Tj}, {d*g-ad*L, ad*T^2-4*d*Pi^2, 4*L*j*Pi^2-T*g*Tj, 4*d*j*Pi^2-ad*T*Tj}, {sintheta*g-ad, T^2*g-4*L*Pi^2, ad*T^2-4*d*Pi^2, 4*L*j*Pi^2-T*g*Tj}, {sintheta*g-ad, T^2*g-4*L*Pi^2, ad*T^2-4*d*Pi^2, 4*d*j*Pi^2-ad*T*Tj}, {sintheta*g-ad, T^2*g-4*L*Pi^2, 4*L*j*Pi^2-T*g*Tj, 4*d*j*Pi^2-ad*T*Tj}, {sintheta*g-ad, ad*T^2-4*d*Pi^2, 4*L*j*Pi^2-T*g*Tj, 4*d*j*Pi^2-ad*T*Tj}, {T^2*g-4*L*Pi^2, ad*T^2-4*d*Pi^2, 4*L*j*Pi^2-T*g*Tj, 4*d*j*Pi^2-ad*T*Tj}};

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
f = openOut "results/pendulum/abduction/noiseless/3_axiom(s)_removed/combo_2_4_5/reasoning/reasoning_output.txt";
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

print("Reasoning complete. Output written to results/pendulum/abduction/noiseless/3_axiom(s)_removed/combo_2_4_5/reasoning/reasoning_output.txt");
