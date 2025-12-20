-- AI-Noether: Reasoning Template (Noiseless)
-- Tests if candidate axiom sets, when added to remaining axioms, prove targets

needsPackage("PrimaryDecomposition", Reload => true)

-- Ring definition
R = QQ[F, ad, T, Fd, omega, theta, sintheta, m, d, g, L, j, Pi, Tj, MonomialOrder => Lex];

-- Input data
remainingAxioms = toList([ad-g*sintheta, d-L*theta, T*omega-2*Pi, Tj-j*T, sintheta - theta]);
qList = toList([d*g*Tj^2-4*d*L*j^2*Pi^2]);
k = #qList;

-- Per-target variable partitions
measuredPerTarget = {{d, g, L, j, Pi, Tj}};
nonMeasuredPerTarget = {{F, ad, T, Fd, omega, theta, sintheta, m}};

-- Candidate axiom sets to test (list of lists)
candidateSets = {{}, {d}, {sintheta}, {theta}, {ad}, {2*j*Pi-omega*Tj}, {T*j-Tj}, {T*omega-2*Pi}, {d, sintheta}, {d, theta}, {d, ad}, {d, 2*j*Pi-omega*Tj}, {d, T*j-Tj}, {d, T*omega-2*Pi}, {sintheta, theta}, {sintheta, ad}, {sintheta, 2*j*Pi-omega*Tj}, {sintheta, T*j-Tj}, {sintheta, T*omega-2*Pi}, {theta, ad}, {theta, 2*j*Pi-omega*Tj}, {theta, T*j-Tj}, {theta, T*omega-2*Pi}, {ad, 2*j*Pi-omega*Tj}, {ad, T*j-Tj}, {ad, T*omega-2*Pi}, {2*j*Pi-omega*Tj, T*j-Tj}, {2*j*Pi-omega*Tj, T*omega-2*Pi}, {T*j-Tj, T*omega-2*Pi}, {d, sintheta, theta}, {d, sintheta, ad}, {d, sintheta, 2*j*Pi-omega*Tj}, {d, sintheta, T*j-Tj}, {d, sintheta, T*omega-2*Pi}, {d, theta, ad}, {d, theta, 2*j*Pi-omega*Tj}, {d, theta, T*j-Tj}, {d, theta, T*omega-2*Pi}, {d, ad, 2*j*Pi-omega*Tj}, {d, ad, T*j-Tj}, {d, ad, T*omega-2*Pi}, {d, 2*j*Pi-omega*Tj, T*j-Tj}, {d, 2*j*Pi-omega*Tj, T*omega-2*Pi}, {d, T*j-Tj, T*omega-2*Pi}, {sintheta, theta, ad}, {sintheta, theta, 2*j*Pi-omega*Tj}, {sintheta, theta, T*j-Tj}, {sintheta, theta, T*omega-2*Pi}, {sintheta, ad, 2*j*Pi-omega*Tj}, {sintheta, ad, T*j-Tj}, {sintheta, ad, T*omega-2*Pi}, {sintheta, 2*j*Pi-omega*Tj, T*j-Tj}, {sintheta, 2*j*Pi-omega*Tj, T*omega-2*Pi}, {sintheta, T*j-Tj, T*omega-2*Pi}, {theta, ad, 2*j*Pi-omega*Tj}, {theta, ad, T*j-Tj}, {theta, ad, T*omega-2*Pi}, {theta, 2*j*Pi-omega*Tj, T*j-Tj}, {theta, 2*j*Pi-omega*Tj, T*omega-2*Pi}, {theta, T*j-Tj, T*omega-2*Pi}, {ad, 2*j*Pi-omega*Tj, T*j-Tj}, {ad, 2*j*Pi-omega*Tj, T*omega-2*Pi}, {ad, T*j-Tj, T*omega-2*Pi}, {2*j*Pi-omega*Tj, T*j-Tj, T*omega-2*Pi}, {L}, {d}, {theta-sintheta}, {2*j*Pi-omega*Tj}, {T*j-Tj}, {sintheta*g-ad}, {T*omega-2*Pi}, {L, d}, {L, theta-sintheta}, {L, 2*j*Pi-omega*Tj}, {L, T*j-Tj}, {L, sintheta*g-ad}, {L, T*omega-2*Pi}, {d, theta-sintheta}, {d, 2*j*Pi-omega*Tj}, {d, T*j-Tj}, {d, sintheta*g-ad}, {d, T*omega-2*Pi}, {theta-sintheta, 2*j*Pi-omega*Tj}, {theta-sintheta, T*j-Tj}, {theta-sintheta, sintheta*g-ad}, {theta-sintheta, T*omega-2*Pi}, {2*j*Pi-omega*Tj, T*j-Tj}, {2*j*Pi-omega*Tj, sintheta*g-ad}, {2*j*Pi-omega*Tj, T*omega-2*Pi}, {T*j-Tj, sintheta*g-ad}, {T*j-Tj, T*omega-2*Pi}, {sintheta*g-ad, T*omega-2*Pi}, {L, d, theta-sintheta}, {L, d, 2*j*Pi-omega*Tj}, {L, d, T*j-Tj}, {L, d, sintheta*g-ad}, {L, d, T*omega-2*Pi}, {L, theta-sintheta, 2*j*Pi-omega*Tj}, {L, theta-sintheta, T*j-Tj}, {L, theta-sintheta, sintheta*g-ad}, {L, theta-sintheta, T*omega-2*Pi}, {L, 2*j*Pi-omega*Tj, T*j-Tj}, {L, 2*j*Pi-omega*Tj, sintheta*g-ad}, {L, 2*j*Pi-omega*Tj, T*omega-2*Pi}, {L, T*j-Tj, sintheta*g-ad}, {L, T*j-Tj, T*omega-2*Pi}, {L, sintheta*g-ad, T*omega-2*Pi}, {d, theta-sintheta, 2*j*Pi-omega*Tj}, {d, theta-sintheta, T*j-Tj}, {d, theta-sintheta, sintheta*g-ad}, {d, theta-sintheta, T*omega-2*Pi}, {d, 2*j*Pi-omega*Tj, T*j-Tj}, {d, 2*j*Pi-omega*Tj, sintheta*g-ad}, {d, 2*j*Pi-omega*Tj, T*omega-2*Pi}, {d, T*j-Tj, sintheta*g-ad}, {d, T*j-Tj, T*omega-2*Pi}, {d, sintheta*g-ad, T*omega-2*Pi}, {theta-sintheta, 2*j*Pi-omega*Tj, T*j-Tj}, {theta-sintheta, 2*j*Pi-omega*Tj, sintheta*g-ad}, {theta-sintheta, 2*j*Pi-omega*Tj, T*omega-2*Pi}, {theta-sintheta, T*j-Tj, sintheta*g-ad}, {theta-sintheta, T*j-Tj, T*omega-2*Pi}, {theta-sintheta, sintheta*g-ad, T*omega-2*Pi}, {2*j*Pi-omega*Tj, T*j-Tj, sintheta*g-ad}, {2*j*Pi-omega*Tj, T*j-Tj, T*omega-2*Pi}, {2*j*Pi-omega*Tj, sintheta*g-ad, T*omega-2*Pi}, {T*j-Tj, sintheta*g-ad, T*omega-2*Pi}, {Tj}, {Pi}, {theta-sintheta}, {T}, {sintheta*L-d}, {d*g-ad*L}, {sintheta*g-ad}, {Tj, Pi}, {Tj, theta-sintheta}, {Tj, T}, {Tj, sintheta*L-d}, {Tj, d*g-ad*L}, {Tj, sintheta*g-ad}, {Pi, theta-sintheta}, {Pi, T}, {Pi, sintheta*L-d}, {Pi, d*g-ad*L}, {Pi, sintheta*g-ad}, {theta-sintheta, T}, {theta-sintheta, sintheta*L-d}, {theta-sintheta, d*g-ad*L}, {theta-sintheta, sintheta*g-ad}, {T, sintheta*L-d}, {T, d*g-ad*L}, {T, sintheta*g-ad}, {sintheta*L-d, d*g-ad*L}, {sintheta*L-d, sintheta*g-ad}, {d*g-ad*L, sintheta*g-ad}, {Tj, Pi, theta-sintheta}, {Tj, Pi, T}, {Tj, Pi, sintheta*L-d}, {Tj, Pi, d*g-ad*L}, {Tj, Pi, sintheta*g-ad}, {Tj, theta-sintheta, T}, {Tj, theta-sintheta, sintheta*L-d}, {Tj, theta-sintheta, d*g-ad*L}, {Tj, theta-sintheta, sintheta*g-ad}, {Tj, T, sintheta*L-d}, {Tj, T, d*g-ad*L}, {Tj, T, sintheta*g-ad}, {Tj, sintheta*L-d, d*g-ad*L}, {Tj, sintheta*L-d, sintheta*g-ad}, {Tj, d*g-ad*L, sintheta*g-ad}, {Pi, theta-sintheta, T}, {Pi, theta-sintheta, sintheta*L-d}, {Pi, theta-sintheta, d*g-ad*L}, {Pi, theta-sintheta, sintheta*g-ad}, {Pi, T, sintheta*L-d}, {Pi, T, d*g-ad*L}, {Pi, T, sintheta*g-ad}, {Pi, sintheta*L-d, d*g-ad*L}, {Pi, sintheta*L-d, sintheta*g-ad}, {Pi, d*g-ad*L, sintheta*g-ad}, {theta-sintheta, T, sintheta*L-d}, {theta-sintheta, T, d*g-ad*L}, {theta-sintheta, T, sintheta*g-ad}, {theta-sintheta, sintheta*L-d, d*g-ad*L}, {theta-sintheta, sintheta*L-d, sintheta*g-ad}, {theta-sintheta, d*g-ad*L, sintheta*g-ad}, {T, sintheta*L-d, d*g-ad*L}, {T, sintheta*L-d, sintheta*g-ad}, {T, d*g-ad*L, sintheta*g-ad}, {sintheta*L-d, d*g-ad*L, sintheta*g-ad}, {Tj}, {j}, {theta-sintheta}, {sintheta*L-d}, {d*g-ad*L}, {sintheta*g-ad}, {T*omega-2*Pi}, {Tj, j}, {Tj, theta-sintheta}, {Tj, sintheta*L-d}, {Tj, d*g-ad*L}, {Tj, sintheta*g-ad}, {Tj, T*omega-2*Pi}, {j, theta-sintheta}, {j, sintheta*L-d}, {j, d*g-ad*L}, {j, sintheta*g-ad}, {j, T*omega-2*Pi}, {theta-sintheta, sintheta*L-d}, {theta-sintheta, d*g-ad*L}, {theta-sintheta, sintheta*g-ad}, {theta-sintheta, T*omega-2*Pi}, {sintheta*L-d, d*g-ad*L}, {sintheta*L-d, sintheta*g-ad}, {sintheta*L-d, T*omega-2*Pi}, {d*g-ad*L, sintheta*g-ad}, {d*g-ad*L, T*omega-2*Pi}, {sintheta*g-ad, T*omega-2*Pi}, {Tj, j, theta-sintheta}, {Tj, j, sintheta*L-d}, {Tj, j, d*g-ad*L}, {Tj, j, sintheta*g-ad}, {Tj, j, T*omega-2*Pi}, {Tj, theta-sintheta, sintheta*L-d}, {Tj, theta-sintheta, d*g-ad*L}, {Tj, theta-sintheta, sintheta*g-ad}, {Tj, theta-sintheta, T*omega-2*Pi}, {Tj, sintheta*L-d, d*g-ad*L}, {Tj, sintheta*L-d, sintheta*g-ad}, {Tj, sintheta*L-d, T*omega-2*Pi}, {Tj, d*g-ad*L, sintheta*g-ad}, {Tj, d*g-ad*L, T*omega-2*Pi}, {Tj, sintheta*g-ad, T*omega-2*Pi}, {j, theta-sintheta, sintheta*L-d}, {j, theta-sintheta, d*g-ad*L}, {j, theta-sintheta, sintheta*g-ad}, {j, theta-sintheta, T*omega-2*Pi}, {j, sintheta*L-d, d*g-ad*L}, {j, sintheta*L-d, sintheta*g-ad}, {j, sintheta*L-d, T*omega-2*Pi}, {j, d*g-ad*L, sintheta*g-ad}, {j, d*g-ad*L, T*omega-2*Pi}, {j, sintheta*g-ad, T*omega-2*Pi}, {theta-sintheta, sintheta*L-d, d*g-ad*L}, {theta-sintheta, sintheta*L-d, sintheta*g-ad}, {theta-sintheta, sintheta*L-d, T*omega-2*Pi}, {theta-sintheta, d*g-ad*L, sintheta*g-ad}, {theta-sintheta, d*g-ad*L, T*omega-2*Pi}, {theta-sintheta, sintheta*g-ad, T*omega-2*Pi}, {sintheta*L-d, d*g-ad*L, sintheta*g-ad}, {sintheta*L-d, d*g-ad*L, T*omega-2*Pi}, {sintheta*L-d, sintheta*g-ad, T*omega-2*Pi}, {d*g-ad*L, sintheta*g-ad, T*omega-2*Pi}, {theta-sintheta}, {2*j*Pi-omega*Tj}, {T*j-Tj}, {sintheta*L-d}, {d*g-ad*L}, {sintheta*g-ad}, {T*omega-2*Pi}, {2*omega*L*Pi-T*g}, {2*omega*d*Pi-ad*T}, {omega^2*L-g}, {T^2*g-4*L*Pi^2}, {omega^2*d-ad}, {ad*T^2-4*d*Pi^2}, {theta-sintheta, 2*j*Pi-omega*Tj}, {theta-sintheta, T*j-Tj}, {theta-sintheta, sintheta*L-d}, {theta-sintheta, d*g-ad*L}, {theta-sintheta, sintheta*g-ad}, {theta-sintheta, T*omega-2*Pi}, {theta-sintheta, 2*omega*L*Pi-T*g}, {theta-sintheta, 2*omega*d*Pi-ad*T}, {theta-sintheta, omega^2*L-g}, {theta-sintheta, T^2*g-4*L*Pi^2}, {theta-sintheta, omega^2*d-ad}, {theta-sintheta, ad*T^2-4*d*Pi^2}, {2*j*Pi-omega*Tj, T*j-Tj}, {2*j*Pi-omega*Tj, sintheta*L-d}, {2*j*Pi-omega*Tj, d*g-ad*L}, {2*j*Pi-omega*Tj, sintheta*g-ad}, {2*j*Pi-omega*Tj, T*omega-2*Pi}, {2*j*Pi-omega*Tj, 2*omega*L*Pi-T*g}, {2*j*Pi-omega*Tj, 2*omega*d*Pi-ad*T}, {2*j*Pi-omega*Tj, omega^2*L-g}, {2*j*Pi-omega*Tj, T^2*g-4*L*Pi^2}, {2*j*Pi-omega*Tj, omega^2*d-ad}, {2*j*Pi-omega*Tj, ad*T^2-4*d*Pi^2}, {T*j-Tj, sintheta*L-d}, {T*j-Tj, d*g-ad*L}, {T*j-Tj, sintheta*g-ad}, {T*j-Tj, T*omega-2*Pi}, {T*j-Tj, 2*omega*L*Pi-T*g}, {T*j-Tj, 2*omega*d*Pi-ad*T}, {T*j-Tj, omega^2*L-g}, {T*j-Tj, T^2*g-4*L*Pi^2}, {T*j-Tj, omega^2*d-ad}, {T*j-Tj, ad*T^2-4*d*Pi^2}, {sintheta*L-d, d*g-ad*L}, {sintheta*L-d, sintheta*g-ad}, {sintheta*L-d, T*omega-2*Pi}, {sintheta*L-d, 2*omega*L*Pi-T*g}, {sintheta*L-d, 2*omega*d*Pi-ad*T}, {sintheta*L-d, omega^2*L-g}, {sintheta*L-d, T^2*g-4*L*Pi^2}, {sintheta*L-d, omega^2*d-ad}, {sintheta*L-d, ad*T^2-4*d*Pi^2}, {d*g-ad*L, sintheta*g-ad}, {d*g-ad*L, T*omega-2*Pi}, {d*g-ad*L, 2*omega*L*Pi-T*g}, {d*g-ad*L, 2*omega*d*Pi-ad*T}, {d*g-ad*L, omega^2*L-g}, {d*g-ad*L, T^2*g-4*L*Pi^2}, {d*g-ad*L, omega^2*d-ad}, {d*g-ad*L, ad*T^2-4*d*Pi^2}, {sintheta*g-ad, T*omega-2*Pi}, {sintheta*g-ad, 2*omega*L*Pi-T*g}, {sintheta*g-ad, 2*omega*d*Pi-ad*T}, {sintheta*g-ad, omega^2*L-g}, {sintheta*g-ad, T^2*g-4*L*Pi^2}, {sintheta*g-ad, omega^2*d-ad}, {sintheta*g-ad, ad*T^2-4*d*Pi^2}, {T*omega-2*Pi, 2*omega*L*Pi-T*g}, {T*omega-2*Pi, 2*omega*d*Pi-ad*T}, {T*omega-2*Pi, omega^2*L-g}, {T*omega-2*Pi, T^2*g-4*L*Pi^2}, {T*omega-2*Pi, omega^2*d-ad}, {T*omega-2*Pi, ad*T^2-4*d*Pi^2}, {2*omega*L*Pi-T*g, 2*omega*d*Pi-ad*T}, {2*omega*L*Pi-T*g, omega^2*L-g}, {2*omega*L*Pi-T*g, T^2*g-4*L*Pi^2}, {2*omega*L*Pi-T*g, omega^2*d-ad}, {2*omega*L*Pi-T*g, ad*T^2-4*d*Pi^2}, {2*omega*d*Pi-ad*T, omega^2*L-g}, {2*omega*d*Pi-ad*T, T^2*g-4*L*Pi^2}, {2*omega*d*Pi-ad*T, omega^2*d-ad}, {2*omega*d*Pi-ad*T, ad*T^2-4*d*Pi^2}, {omega^2*L-g, T^2*g-4*L*Pi^2}, {omega^2*L-g, omega^2*d-ad}, {omega^2*L-g, ad*T^2-4*d*Pi^2}, {T^2*g-4*L*Pi^2, omega^2*d-ad}, {T^2*g-4*L*Pi^2, ad*T^2-4*d*Pi^2}, {omega^2*d-ad, ad*T^2-4*d*Pi^2}, {theta-sintheta, 2*j*Pi-omega*Tj, T*j-Tj}, {theta-sintheta, 2*j*Pi-omega*Tj, sintheta*L-d}, {theta-sintheta, 2*j*Pi-omega*Tj, d*g-ad*L}, {theta-sintheta, 2*j*Pi-omega*Tj, sintheta*g-ad}, {theta-sintheta, 2*j*Pi-omega*Tj, T*omega-2*Pi}, {theta-sintheta, 2*j*Pi-omega*Tj, 2*omega*L*Pi-T*g}, {theta-sintheta, 2*j*Pi-omega*Tj, 2*omega*d*Pi-ad*T}, {theta-sintheta, 2*j*Pi-omega*Tj, omega^2*L-g}, {theta-sintheta, 2*j*Pi-omega*Tj, T^2*g-4*L*Pi^2}, {theta-sintheta, 2*j*Pi-omega*Tj, omega^2*d-ad}, {theta-sintheta, 2*j*Pi-omega*Tj, ad*T^2-4*d*Pi^2}, {theta-sintheta, T*j-Tj, sintheta*L-d}, {theta-sintheta, T*j-Tj, d*g-ad*L}, {theta-sintheta, T*j-Tj, sintheta*g-ad}, {theta-sintheta, T*j-Tj, T*omega-2*Pi}, {theta-sintheta, T*j-Tj, 2*omega*L*Pi-T*g}, {theta-sintheta, T*j-Tj, 2*omega*d*Pi-ad*T}, {theta-sintheta, T*j-Tj, omega^2*L-g}, {theta-sintheta, T*j-Tj, T^2*g-4*L*Pi^2}, {theta-sintheta, T*j-Tj, omega^2*d-ad}, {theta-sintheta, T*j-Tj, ad*T^2-4*d*Pi^2}, {theta-sintheta, sintheta*L-d, d*g-ad*L}, {theta-sintheta, sintheta*L-d, sintheta*g-ad}, {theta-sintheta, sintheta*L-d, T*omega-2*Pi}, {theta-sintheta, sintheta*L-d, 2*omega*L*Pi-T*g}, {theta-sintheta, sintheta*L-d, 2*omega*d*Pi-ad*T}, {theta-sintheta, sintheta*L-d, omega^2*L-g}, {theta-sintheta, sintheta*L-d, T^2*g-4*L*Pi^2}, {theta-sintheta, sintheta*L-d, omega^2*d-ad}, {theta-sintheta, sintheta*L-d, ad*T^2-4*d*Pi^2}, {theta-sintheta, d*g-ad*L, sintheta*g-ad}, {theta-sintheta, d*g-ad*L, T*omega-2*Pi}, {theta-sintheta, d*g-ad*L, 2*omega*L*Pi-T*g}, {theta-sintheta, d*g-ad*L, 2*omega*d*Pi-ad*T}, {theta-sintheta, d*g-ad*L, omega^2*L-g}, {theta-sintheta, d*g-ad*L, T^2*g-4*L*Pi^2}, {theta-sintheta, d*g-ad*L, omega^2*d-ad}, {theta-sintheta, d*g-ad*L, ad*T^2-4*d*Pi^2}, {theta-sintheta, sintheta*g-ad, T*omega-2*Pi}, {theta-sintheta, sintheta*g-ad, 2*omega*L*Pi-T*g}, {theta-sintheta, sintheta*g-ad, 2*omega*d*Pi-ad*T}, {theta-sintheta, sintheta*g-ad, omega^2*L-g}, {theta-sintheta, sintheta*g-ad, T^2*g-4*L*Pi^2}, {theta-sintheta, sintheta*g-ad, omega^2*d-ad}, {theta-sintheta, sintheta*g-ad, ad*T^2-4*d*Pi^2}, {theta-sintheta, T*omega-2*Pi, 2*omega*L*Pi-T*g}, {theta-sintheta, T*omega-2*Pi, 2*omega*d*Pi-ad*T}, {theta-sintheta, T*omega-2*Pi, omega^2*L-g}, {theta-sintheta, T*omega-2*Pi, T^2*g-4*L*Pi^2}, {theta-sintheta, T*omega-2*Pi, omega^2*d-ad}, {theta-sintheta, T*omega-2*Pi, ad*T^2-4*d*Pi^2}, {theta-sintheta, 2*omega*L*Pi-T*g, 2*omega*d*Pi-ad*T}, {theta-sintheta, 2*omega*L*Pi-T*g, omega^2*L-g}, {theta-sintheta, 2*omega*L*Pi-T*g, T^2*g-4*L*Pi^2}, {theta-sintheta, 2*omega*L*Pi-T*g, omega^2*d-ad}, {theta-sintheta, 2*omega*L*Pi-T*g, ad*T^2-4*d*Pi^2}, {theta-sintheta, 2*omega*d*Pi-ad*T, omega^2*L-g}, {theta-sintheta, 2*omega*d*Pi-ad*T, T^2*g-4*L*Pi^2}, {theta-sintheta, 2*omega*d*Pi-ad*T, omega^2*d-ad}, {theta-sintheta, 2*omega*d*Pi-ad*T, ad*T^2-4*d*Pi^2}, {theta-sintheta, omega^2*L-g, T^2*g-4*L*Pi^2}, {theta-sintheta, omega^2*L-g, omega^2*d-ad}, {theta-sintheta, omega^2*L-g, ad*T^2-4*d*Pi^2}, {theta-sintheta, T^2*g-4*L*Pi^2, omega^2*d-ad}, {theta-sintheta, T^2*g-4*L*Pi^2, ad*T^2-4*d*Pi^2}, {theta-sintheta, omega^2*d-ad, ad*T^2-4*d*Pi^2}, {2*j*Pi-omega*Tj, T*j-Tj, sintheta*L-d}, {2*j*Pi-omega*Tj, T*j-Tj, d*g-ad*L}, {2*j*Pi-omega*Tj, T*j-Tj, sintheta*g-ad}, {2*j*Pi-omega*Tj, T*j-Tj, T*omega-2*Pi}, {2*j*Pi-omega*Tj, T*j-Tj, 2*omega*L*Pi-T*g}, {2*j*Pi-omega*Tj, T*j-Tj, 2*omega*d*Pi-ad*T}, {2*j*Pi-omega*Tj, T*j-Tj, omega^2*L-g}, {2*j*Pi-omega*Tj, T*j-Tj, T^2*g-4*L*Pi^2}, {2*j*Pi-omega*Tj, T*j-Tj, omega^2*d-ad}, {2*j*Pi-omega*Tj, T*j-Tj, ad*T^2-4*d*Pi^2}, {2*j*Pi-omega*Tj, sintheta*L-d, d*g-ad*L}, {2*j*Pi-omega*Tj, sintheta*L-d, sintheta*g-ad}, {2*j*Pi-omega*Tj, sintheta*L-d, T*omega-2*Pi}, {2*j*Pi-omega*Tj, sintheta*L-d, 2*omega*L*Pi-T*g}, {2*j*Pi-omega*Tj, sintheta*L-d, 2*omega*d*Pi-ad*T}, {2*j*Pi-omega*Tj, sintheta*L-d, omega^2*L-g}, {2*j*Pi-omega*Tj, sintheta*L-d, T^2*g-4*L*Pi^2}, {2*j*Pi-omega*Tj, sintheta*L-d, omega^2*d-ad}, {2*j*Pi-omega*Tj, sintheta*L-d, ad*T^2-4*d*Pi^2}, {2*j*Pi-omega*Tj, d*g-ad*L, sintheta*g-ad}, {2*j*Pi-omega*Tj, d*g-ad*L, T*omega-2*Pi}, {2*j*Pi-omega*Tj, d*g-ad*L, 2*omega*L*Pi-T*g}, {2*j*Pi-omega*Tj, d*g-ad*L, 2*omega*d*Pi-ad*T}, {2*j*Pi-omega*Tj, d*g-ad*L, omega^2*L-g}, {2*j*Pi-omega*Tj, d*g-ad*L, T^2*g-4*L*Pi^2}, {2*j*Pi-omega*Tj, d*g-ad*L, omega^2*d-ad}, {2*j*Pi-omega*Tj, d*g-ad*L, ad*T^2-4*d*Pi^2}, {2*j*Pi-omega*Tj, sintheta*g-ad, T*omega-2*Pi}, {2*j*Pi-omega*Tj, sintheta*g-ad, 2*omega*L*Pi-T*g}, {2*j*Pi-omega*Tj, sintheta*g-ad, 2*omega*d*Pi-ad*T}, {2*j*Pi-omega*Tj, sintheta*g-ad, omega^2*L-g}, {2*j*Pi-omega*Tj, sintheta*g-ad, T^2*g-4*L*Pi^2}, {2*j*Pi-omega*Tj, sintheta*g-ad, omega^2*d-ad}, {2*j*Pi-omega*Tj, sintheta*g-ad, ad*T^2-4*d*Pi^2}, {2*j*Pi-omega*Tj, T*omega-2*Pi, 2*omega*L*Pi-T*g}, {2*j*Pi-omega*Tj, T*omega-2*Pi, 2*omega*d*Pi-ad*T}, {2*j*Pi-omega*Tj, T*omega-2*Pi, omega^2*L-g}, {2*j*Pi-omega*Tj, T*omega-2*Pi, T^2*g-4*L*Pi^2}, {2*j*Pi-omega*Tj, T*omega-2*Pi, omega^2*d-ad}, {2*j*Pi-omega*Tj, T*omega-2*Pi, ad*T^2-4*d*Pi^2}, {2*j*Pi-omega*Tj, 2*omega*L*Pi-T*g, 2*omega*d*Pi-ad*T}, {2*j*Pi-omega*Tj, 2*omega*L*Pi-T*g, omega^2*L-g}, {2*j*Pi-omega*Tj, 2*omega*L*Pi-T*g, T^2*g-4*L*Pi^2}, {2*j*Pi-omega*Tj, 2*omega*L*Pi-T*g, omega^2*d-ad}, {2*j*Pi-omega*Tj, 2*omega*L*Pi-T*g, ad*T^2-4*d*Pi^2}, {2*j*Pi-omega*Tj, 2*omega*d*Pi-ad*T, omega^2*L-g}, {2*j*Pi-omega*Tj, 2*omega*d*Pi-ad*T, T^2*g-4*L*Pi^2}, {2*j*Pi-omega*Tj, 2*omega*d*Pi-ad*T, omega^2*d-ad}, {2*j*Pi-omega*Tj, 2*omega*d*Pi-ad*T, ad*T^2-4*d*Pi^2}, {2*j*Pi-omega*Tj, omega^2*L-g, T^2*g-4*L*Pi^2}, {2*j*Pi-omega*Tj, omega^2*L-g, omega^2*d-ad}, {2*j*Pi-omega*Tj, omega^2*L-g, ad*T^2-4*d*Pi^2}, {2*j*Pi-omega*Tj, T^2*g-4*L*Pi^2, omega^2*d-ad}, {2*j*Pi-omega*Tj, T^2*g-4*L*Pi^2, ad*T^2-4*d*Pi^2}, {2*j*Pi-omega*Tj, omega^2*d-ad, ad*T^2-4*d*Pi^2}, {T*j-Tj, sintheta*L-d, d*g-ad*L}, {T*j-Tj, sintheta*L-d, sintheta*g-ad}, {T*j-Tj, sintheta*L-d, T*omega-2*Pi}, {T*j-Tj, sintheta*L-d, 2*omega*L*Pi-T*g}, {T*j-Tj, sintheta*L-d, 2*omega*d*Pi-ad*T}, {T*j-Tj, sintheta*L-d, omega^2*L-g}, {T*j-Tj, sintheta*L-d, T^2*g-4*L*Pi^2}, {T*j-Tj, sintheta*L-d, omega^2*d-ad}, {T*j-Tj, sintheta*L-d, ad*T^2-4*d*Pi^2}, {T*j-Tj, d*g-ad*L, sintheta*g-ad}, {T*j-Tj, d*g-ad*L, T*omega-2*Pi}, {T*j-Tj, d*g-ad*L, 2*omega*L*Pi-T*g}, {T*j-Tj, d*g-ad*L, 2*omega*d*Pi-ad*T}, {T*j-Tj, d*g-ad*L, omega^2*L-g}, {T*j-Tj, d*g-ad*L, T^2*g-4*L*Pi^2}, {T*j-Tj, d*g-ad*L, omega^2*d-ad}, {T*j-Tj, d*g-ad*L, ad*T^2-4*d*Pi^2}, {T*j-Tj, sintheta*g-ad, T*omega-2*Pi}, {T*j-Tj, sintheta*g-ad, 2*omega*L*Pi-T*g}, {T*j-Tj, sintheta*g-ad, 2*omega*d*Pi-ad*T}, {T*j-Tj, sintheta*g-ad, omega^2*L-g}, {T*j-Tj, sintheta*g-ad, T^2*g-4*L*Pi^2}, {T*j-Tj, sintheta*g-ad, omega^2*d-ad}, {T*j-Tj, sintheta*g-ad, ad*T^2-4*d*Pi^2}, {T*j-Tj, T*omega-2*Pi, 2*omega*L*Pi-T*g}, {T*j-Tj, T*omega-2*Pi, 2*omega*d*Pi-ad*T}, {T*j-Tj, T*omega-2*Pi, omega^2*L-g}, {T*j-Tj, T*omega-2*Pi, T^2*g-4*L*Pi^2}, {T*j-Tj, T*omega-2*Pi, omega^2*d-ad}, {T*j-Tj, T*omega-2*Pi, ad*T^2-4*d*Pi^2}, {T*j-Tj, 2*omega*L*Pi-T*g, 2*omega*d*Pi-ad*T}, {T*j-Tj, 2*omega*L*Pi-T*g, omega^2*L-g}, {T*j-Tj, 2*omega*L*Pi-T*g, T^2*g-4*L*Pi^2}, {T*j-Tj, 2*omega*L*Pi-T*g, omega^2*d-ad}, {T*j-Tj, 2*omega*L*Pi-T*g, ad*T^2-4*d*Pi^2}, {T*j-Tj, 2*omega*d*Pi-ad*T, omega^2*L-g}, {T*j-Tj, 2*omega*d*Pi-ad*T, T^2*g-4*L*Pi^2}, {T*j-Tj, 2*omega*d*Pi-ad*T, omega^2*d-ad}, {T*j-Tj, 2*omega*d*Pi-ad*T, ad*T^2-4*d*Pi^2}, {T*j-Tj, omega^2*L-g, T^2*g-4*L*Pi^2}, {T*j-Tj, omega^2*L-g, omega^2*d-ad}, {T*j-Tj, omega^2*L-g, ad*T^2-4*d*Pi^2}, {T*j-Tj, T^2*g-4*L*Pi^2, omega^2*d-ad}, {T*j-Tj, T^2*g-4*L*Pi^2, ad*T^2-4*d*Pi^2}, {T*j-Tj, omega^2*d-ad, ad*T^2-4*d*Pi^2}, {sintheta*L-d, d*g-ad*L, sintheta*g-ad}, {sintheta*L-d, d*g-ad*L, T*omega-2*Pi}, {sintheta*L-d, d*g-ad*L, 2*omega*L*Pi-T*g}, {sintheta*L-d, d*g-ad*L, 2*omega*d*Pi-ad*T}, {sintheta*L-d, d*g-ad*L, omega^2*L-g}, {sintheta*L-d, d*g-ad*L, T^2*g-4*L*Pi^2}, {sintheta*L-d, d*g-ad*L, omega^2*d-ad}, {sintheta*L-d, d*g-ad*L, ad*T^2-4*d*Pi^2}, {sintheta*L-d, sintheta*g-ad, T*omega-2*Pi}, {sintheta*L-d, sintheta*g-ad, 2*omega*L*Pi-T*g}, {sintheta*L-d, sintheta*g-ad, 2*omega*d*Pi-ad*T}, {sintheta*L-d, sintheta*g-ad, omega^2*L-g}, {sintheta*L-d, sintheta*g-ad, T^2*g-4*L*Pi^2}, {sintheta*L-d, sintheta*g-ad, omega^2*d-ad}, {sintheta*L-d, sintheta*g-ad, ad*T^2-4*d*Pi^2}, {sintheta*L-d, T*omega-2*Pi, 2*omega*L*Pi-T*g}, {sintheta*L-d, T*omega-2*Pi, 2*omega*d*Pi-ad*T}, {sintheta*L-d, T*omega-2*Pi, omega^2*L-g}, {sintheta*L-d, T*omega-2*Pi, T^2*g-4*L*Pi^2}, {sintheta*L-d, T*omega-2*Pi, omega^2*d-ad}, {sintheta*L-d, T*omega-2*Pi, ad*T^2-4*d*Pi^2}, {sintheta*L-d, 2*omega*L*Pi-T*g, 2*omega*d*Pi-ad*T}, {sintheta*L-d, 2*omega*L*Pi-T*g, omega^2*L-g}, {sintheta*L-d, 2*omega*L*Pi-T*g, T^2*g-4*L*Pi^2}, {sintheta*L-d, 2*omega*L*Pi-T*g, omega^2*d-ad}, {sintheta*L-d, 2*omega*L*Pi-T*g, ad*T^2-4*d*Pi^2}, {sintheta*L-d, 2*omega*d*Pi-ad*T, omega^2*L-g}, {sintheta*L-d, 2*omega*d*Pi-ad*T, T^2*g-4*L*Pi^2}, {sintheta*L-d, 2*omega*d*Pi-ad*T, omega^2*d-ad}, {sintheta*L-d, 2*omega*d*Pi-ad*T, ad*T^2-4*d*Pi^2}, {sintheta*L-d, omega^2*L-g, T^2*g-4*L*Pi^2}, {sintheta*L-d, omega^2*L-g, omega^2*d-ad}, {sintheta*L-d, omega^2*L-g, ad*T^2-4*d*Pi^2}, {sintheta*L-d, T^2*g-4*L*Pi^2, omega^2*d-ad}, {sintheta*L-d, T^2*g-4*L*Pi^2, ad*T^2-4*d*Pi^2}, {sintheta*L-d, omega^2*d-ad, ad*T^2-4*d*Pi^2}, {d*g-ad*L, sintheta*g-ad, T*omega-2*Pi}, {d*g-ad*L, sintheta*g-ad, 2*omega*L*Pi-T*g}, {d*g-ad*L, sintheta*g-ad, 2*omega*d*Pi-ad*T}, {d*g-ad*L, sintheta*g-ad, omega^2*L-g}, {d*g-ad*L, sintheta*g-ad, T^2*g-4*L*Pi^2}, {d*g-ad*L, sintheta*g-ad, omega^2*d-ad}, {d*g-ad*L, sintheta*g-ad, ad*T^2-4*d*Pi^2}, {d*g-ad*L, T*omega-2*Pi, 2*omega*L*Pi-T*g}, {d*g-ad*L, T*omega-2*Pi, 2*omega*d*Pi-ad*T}, {d*g-ad*L, T*omega-2*Pi, omega^2*L-g}, {d*g-ad*L, T*omega-2*Pi, T^2*g-4*L*Pi^2}, {d*g-ad*L, T*omega-2*Pi, omega^2*d-ad}, {d*g-ad*L, T*omega-2*Pi, ad*T^2-4*d*Pi^2}, {d*g-ad*L, 2*omega*L*Pi-T*g, 2*omega*d*Pi-ad*T}, {d*g-ad*L, 2*omega*L*Pi-T*g, omega^2*L-g}, {d*g-ad*L, 2*omega*L*Pi-T*g, T^2*g-4*L*Pi^2}, {d*g-ad*L, 2*omega*L*Pi-T*g, omega^2*d-ad}, {d*g-ad*L, 2*omega*L*Pi-T*g, ad*T^2-4*d*Pi^2}, {d*g-ad*L, 2*omega*d*Pi-ad*T, omega^2*L-g}, {d*g-ad*L, 2*omega*d*Pi-ad*T, T^2*g-4*L*Pi^2}, {d*g-ad*L, 2*omega*d*Pi-ad*T, omega^2*d-ad}, {d*g-ad*L, 2*omega*d*Pi-ad*T, ad*T^2-4*d*Pi^2}, {d*g-ad*L, omega^2*L-g, T^2*g-4*L*Pi^2}, {d*g-ad*L, omega^2*L-g, omega^2*d-ad}, {d*g-ad*L, omega^2*L-g, ad*T^2-4*d*Pi^2}, {d*g-ad*L, T^2*g-4*L*Pi^2, omega^2*d-ad}, {d*g-ad*L, T^2*g-4*L*Pi^2, ad*T^2-4*d*Pi^2}, {d*g-ad*L, omega^2*d-ad, ad*T^2-4*d*Pi^2}, {sintheta*g-ad, T*omega-2*Pi, 2*omega*L*Pi-T*g}, {sintheta*g-ad, T*omega-2*Pi, 2*omega*d*Pi-ad*T}, {sintheta*g-ad, T*omega-2*Pi, omega^2*L-g}, {sintheta*g-ad, T*omega-2*Pi, T^2*g-4*L*Pi^2}, {sintheta*g-ad, T*omega-2*Pi, omega^2*d-ad}, {sintheta*g-ad, T*omega-2*Pi, ad*T^2-4*d*Pi^2}, {sintheta*g-ad, 2*omega*L*Pi-T*g, 2*omega*d*Pi-ad*T}, {sintheta*g-ad, 2*omega*L*Pi-T*g, omega^2*L-g}, {sintheta*g-ad, 2*omega*L*Pi-T*g, T^2*g-4*L*Pi^2}, {sintheta*g-ad, 2*omega*L*Pi-T*g, omega^2*d-ad}, {sintheta*g-ad, 2*omega*L*Pi-T*g, ad*T^2-4*d*Pi^2}, {sintheta*g-ad, 2*omega*d*Pi-ad*T, omega^2*L-g}, {sintheta*g-ad, 2*omega*d*Pi-ad*T, T^2*g-4*L*Pi^2}, {sintheta*g-ad, 2*omega*d*Pi-ad*T, omega^2*d-ad}, {sintheta*g-ad, 2*omega*d*Pi-ad*T, ad*T^2-4*d*Pi^2}, {sintheta*g-ad, omega^2*L-g, T^2*g-4*L*Pi^2}, {sintheta*g-ad, omega^2*L-g, omega^2*d-ad}, {sintheta*g-ad, omega^2*L-g, ad*T^2-4*d*Pi^2}, {sintheta*g-ad, T^2*g-4*L*Pi^2, omega^2*d-ad}, {sintheta*g-ad, T^2*g-4*L*Pi^2, ad*T^2-4*d*Pi^2}, {sintheta*g-ad, omega^2*d-ad, ad*T^2-4*d*Pi^2}, {T*omega-2*Pi, 2*omega*L*Pi-T*g, 2*omega*d*Pi-ad*T}, {T*omega-2*Pi, 2*omega*L*Pi-T*g, omega^2*L-g}, {T*omega-2*Pi, 2*omega*L*Pi-T*g, T^2*g-4*L*Pi^2}, {T*omega-2*Pi, 2*omega*L*Pi-T*g, omega^2*d-ad}, {T*omega-2*Pi, 2*omega*L*Pi-T*g, ad*T^2-4*d*Pi^2}, {T*omega-2*Pi, 2*omega*d*Pi-ad*T, omega^2*L-g}, {T*omega-2*Pi, 2*omega*d*Pi-ad*T, T^2*g-4*L*Pi^2}, {T*omega-2*Pi, 2*omega*d*Pi-ad*T, omega^2*d-ad}, {T*omega-2*Pi, 2*omega*d*Pi-ad*T, ad*T^2-4*d*Pi^2}, {T*omega-2*Pi, omega^2*L-g, T^2*g-4*L*Pi^2}, {T*omega-2*Pi, omega^2*L-g, omega^2*d-ad}, {T*omega-2*Pi, omega^2*L-g, ad*T^2-4*d*Pi^2}, {T*omega-2*Pi, T^2*g-4*L*Pi^2, omega^2*d-ad}, {T*omega-2*Pi, T^2*g-4*L*Pi^2, ad*T^2-4*d*Pi^2}, {T*omega-2*Pi, omega^2*d-ad, ad*T^2-4*d*Pi^2}, {2*omega*L*Pi-T*g, 2*omega*d*Pi-ad*T, omega^2*L-g}, {2*omega*L*Pi-T*g, 2*omega*d*Pi-ad*T, T^2*g-4*L*Pi^2}, {2*omega*L*Pi-T*g, 2*omega*d*Pi-ad*T, omega^2*d-ad}, {2*omega*L*Pi-T*g, 2*omega*d*Pi-ad*T, ad*T^2-4*d*Pi^2}, {2*omega*L*Pi-T*g, omega^2*L-g, T^2*g-4*L*Pi^2}, {2*omega*L*Pi-T*g, omega^2*L-g, omega^2*d-ad}, {2*omega*L*Pi-T*g, omega^2*L-g, ad*T^2-4*d*Pi^2}, {2*omega*L*Pi-T*g, T^2*g-4*L*Pi^2, omega^2*d-ad}, {2*omega*L*Pi-T*g, T^2*g-4*L*Pi^2, ad*T^2-4*d*Pi^2}, {2*omega*L*Pi-T*g, omega^2*d-ad, ad*T^2-4*d*Pi^2}, {2*omega*d*Pi-ad*T, omega^2*L-g, T^2*g-4*L*Pi^2}, {2*omega*d*Pi-ad*T, omega^2*L-g, omega^2*d-ad}, {2*omega*d*Pi-ad*T, omega^2*L-g, ad*T^2-4*d*Pi^2}, {2*omega*d*Pi-ad*T, T^2*g-4*L*Pi^2, omega^2*d-ad}, {2*omega*d*Pi-ad*T, T^2*g-4*L*Pi^2, ad*T^2-4*d*Pi^2}, {2*omega*d*Pi-ad*T, omega^2*d-ad, ad*T^2-4*d*Pi^2}, {omega^2*L-g, T^2*g-4*L*Pi^2, omega^2*d-ad}, {omega^2*L-g, T^2*g-4*L*Pi^2, ad*T^2-4*d*Pi^2}, {omega^2*L-g, omega^2*d-ad, ad*T^2-4*d*Pi^2}, {T^2*g-4*L*Pi^2, omega^2*d-ad, ad*T^2-4*d*Pi^2}};

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
f = openOut "results/pendulum/abduction/noiseless/2_axiom(s)_removed/combo_2_5/reasoning/reasoning_output.txt";
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

print("Reasoning complete. Output written to results/pendulum/abduction/noiseless/2_axiom(s)_removed/combo_2_5/reasoning/reasoning_output.txt");
