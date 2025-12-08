-- AI-Noether: Reasoning Template (Noiseless)
-- Tests if candidate axiom sets, when added to remaining axioms, prove targets

needsPackage("PrimaryDecomposition", Reload => true)

-- Ring definition
R = QQ[Fm, d, v, Fe, E, dt, Q, N, V, i, n, qe, B, h, L, UH, MonomialOrder => Lex];

-- Input data
remainingAxioms = toList([Fe - qe*E, Fm - Fe, E*h - UH, v*dt - L, i*dt - Q, Q - N*qe, n*V - N]);
qList = toList([N*qe*UH - i*B*h*L]);
k = #qList;

-- Per-target variable partitions
measuredPerTarget = {{UH, h, L, i, B, N, qe}};
nonMeasuredPerTarget = {{Fm, d, v, Fe, E, dt, Q, V, n}};

-- Candidate axiom sets to test (list of lists)
candidateSets = {{}, {-V*n*qe+dt*i}, {-E*h+UH}, {-v*dt+L}, {h}, {-V*n+N}, {-dt*i+Q}, {-E*qe+Fe}, {Fm-Fe}, {-V*n*qe+dt*i, -E*h+UH}, {-V*n*qe+dt*i, -v*dt+L}, {-V*n*qe+dt*i, h}, {-V*n*qe+dt*i, -V*n+N}, {-V*n*qe+dt*i, -dt*i+Q}, {-V*n*qe+dt*i, -E*qe+Fe}, {-V*n*qe+dt*i, Fm-Fe}, {-E*h+UH, -v*dt+L}, {-E*h+UH, h}, {-E*h+UH, -V*n+N}, {-E*h+UH, -dt*i+Q}, {-E*h+UH, -E*qe+Fe}, {-E*h+UH, Fm-Fe}, {-v*dt+L, h}, {-v*dt+L, -V*n+N}, {-v*dt+L, -dt*i+Q}, {-v*dt+L, -E*qe+Fe}, {-v*dt+L, Fm-Fe}, {h, -V*n+N}, {h, -dt*i+Q}, {h, -E*qe+Fe}, {h, Fm-Fe}, {-V*n+N, -dt*i+Q}, {-V*n+N, -E*qe+Fe}, {-V*n+N, Fm-Fe}, {-dt*i+Q, -E*qe+Fe}, {-dt*i+Q, Fm-Fe}, {-E*qe+Fe, Fm-Fe}, {-V*n*qe+dt*i, -E*h+UH, -v*dt+L}, {-V*n*qe+dt*i, -E*h+UH, h}, {-V*n*qe+dt*i, -E*h+UH, -V*n+N}, {-V*n*qe+dt*i, -E*h+UH, -dt*i+Q}, {-V*n*qe+dt*i, -E*h+UH, -E*qe+Fe}, {-V*n*qe+dt*i, -E*h+UH, Fm-Fe}, {-V*n*qe+dt*i, -v*dt+L, h}, {-V*n*qe+dt*i, -v*dt+L, -V*n+N}, {-V*n*qe+dt*i, -v*dt+L, -dt*i+Q}, {-V*n*qe+dt*i, -v*dt+L, -E*qe+Fe}, {-V*n*qe+dt*i, -v*dt+L, Fm-Fe}, {-V*n*qe+dt*i, h, -V*n+N}, {-V*n*qe+dt*i, h, -dt*i+Q}, {-V*n*qe+dt*i, h, -E*qe+Fe}, {-V*n*qe+dt*i, h, Fm-Fe}, {-V*n*qe+dt*i, -V*n+N, -dt*i+Q}, {-V*n*qe+dt*i, -V*n+N, -E*qe+Fe}, {-V*n*qe+dt*i, -V*n+N, Fm-Fe}, {-V*n*qe+dt*i, -dt*i+Q, -E*qe+Fe}, {-V*n*qe+dt*i, -dt*i+Q, Fm-Fe}, {-V*n*qe+dt*i, -E*qe+Fe, Fm-Fe}, {-E*h+UH, -v*dt+L, h}, {-E*h+UH, -v*dt+L, -V*n+N}, {-E*h+UH, -v*dt+L, -dt*i+Q}, {-E*h+UH, -v*dt+L, -E*qe+Fe}, {-E*h+UH, -v*dt+L, Fm-Fe}, {-E*h+UH, h, -V*n+N}, {-E*h+UH, h, -dt*i+Q}, {-E*h+UH, h, -E*qe+Fe}, {-E*h+UH, h, Fm-Fe}, {-E*h+UH, -V*n+N, -dt*i+Q}, {-E*h+UH, -V*n+N, -E*qe+Fe}, {-E*h+UH, -V*n+N, Fm-Fe}, {-E*h+UH, -dt*i+Q, -E*qe+Fe}, {-E*h+UH, -dt*i+Q, Fm-Fe}, {-E*h+UH, -E*qe+Fe, Fm-Fe}, {-v*dt+L, h, -V*n+N}, {-v*dt+L, h, -dt*i+Q}, {-v*dt+L, h, -E*qe+Fe}, {-v*dt+L, h, Fm-Fe}, {-v*dt+L, -V*n+N, -dt*i+Q}, {-v*dt+L, -V*n+N, -E*qe+Fe}, {-v*dt+L, -V*n+N, Fm-Fe}, {-v*dt+L, -dt*i+Q, -E*qe+Fe}, {-v*dt+L, -dt*i+Q, Fm-Fe}, {-v*dt+L, -E*qe+Fe, Fm-Fe}, {h, -V*n+N, -dt*i+Q}, {h, -V*n+N, -E*qe+Fe}, {h, -V*n+N, Fm-Fe}, {h, -dt*i+Q, -E*qe+Fe}, {h, -dt*i+Q, Fm-Fe}, {h, -E*qe+Fe, Fm-Fe}, {-V*n+N, -dt*i+Q, -E*qe+Fe}, {-V*n+N, -dt*i+Q, Fm-Fe}, {-V*n+N, -E*qe+Fe, Fm-Fe}, {-dt*i+Q, -E*qe+Fe, Fm-Fe}, {-V*n*qe+dt*i}, {v*B-E}, {-E*h+UH}, {-v*dt+L}, {-V*n+N}, {-dt*i+Q}, {-E*qe+Fe}, {Fm-Fe}, {-V*n*qe+dt*i, v*B-E}, {-V*n*qe+dt*i, -E*h+UH}, {-V*n*qe+dt*i, -v*dt+L}, {-V*n*qe+dt*i, -V*n+N}, {-V*n*qe+dt*i, -dt*i+Q}, {-V*n*qe+dt*i, -E*qe+Fe}, {-V*n*qe+dt*i, Fm-Fe}, {v*B-E, -E*h+UH}, {v*B-E, -v*dt+L}, {v*B-E, -V*n+N}, {v*B-E, -dt*i+Q}, {v*B-E, -E*qe+Fe}, {v*B-E, Fm-Fe}, {-E*h+UH, -v*dt+L}, {-E*h+UH, -V*n+N}, {-E*h+UH, -dt*i+Q}, {-E*h+UH, -E*qe+Fe}, {-E*h+UH, Fm-Fe}, {-v*dt+L, -V*n+N}, {-v*dt+L, -dt*i+Q}, {-v*dt+L, -E*qe+Fe}, {-v*dt+L, Fm-Fe}, {-V*n+N, -dt*i+Q}, {-V*n+N, -E*qe+Fe}, {-V*n+N, Fm-Fe}, {-dt*i+Q, -E*qe+Fe}, {-dt*i+Q, Fm-Fe}, {-E*qe+Fe, Fm-Fe}, {-V*n*qe+dt*i, v*B-E, -E*h+UH}, {-V*n*qe+dt*i, v*B-E, -v*dt+L}, {-V*n*qe+dt*i, v*B-E, -V*n+N}, {-V*n*qe+dt*i, v*B-E, -dt*i+Q}, {-V*n*qe+dt*i, v*B-E, -E*qe+Fe}, {-V*n*qe+dt*i, v*B-E, Fm-Fe}, {-V*n*qe+dt*i, -E*h+UH, -v*dt+L}, {-V*n*qe+dt*i, -E*h+UH, -V*n+N}, {-V*n*qe+dt*i, -E*h+UH, -dt*i+Q}, {-V*n*qe+dt*i, -E*h+UH, -E*qe+Fe}, {-V*n*qe+dt*i, -E*h+UH, Fm-Fe}, {-V*n*qe+dt*i, -v*dt+L, -V*n+N}, {-V*n*qe+dt*i, -v*dt+L, -dt*i+Q}, {-V*n*qe+dt*i, -v*dt+L, -E*qe+Fe}, {-V*n*qe+dt*i, -v*dt+L, Fm-Fe}, {-V*n*qe+dt*i, -V*n+N, -dt*i+Q}, {-V*n*qe+dt*i, -V*n+N, -E*qe+Fe}, {-V*n*qe+dt*i, -V*n+N, Fm-Fe}, {-V*n*qe+dt*i, -dt*i+Q, -E*qe+Fe}, {-V*n*qe+dt*i, -dt*i+Q, Fm-Fe}, {-V*n*qe+dt*i, -E*qe+Fe, Fm-Fe}, {v*B-E, -E*h+UH, -v*dt+L}, {v*B-E, -E*h+UH, -V*n+N}, {v*B-E, -E*h+UH, -dt*i+Q}, {v*B-E, -E*h+UH, -E*qe+Fe}, {v*B-E, -E*h+UH, Fm-Fe}, {v*B-E, -v*dt+L, -V*n+N}, {v*B-E, -v*dt+L, -dt*i+Q}, {v*B-E, -v*dt+L, -E*qe+Fe}, {v*B-E, -v*dt+L, Fm-Fe}, {v*B-E, -V*n+N, -dt*i+Q}, {v*B-E, -V*n+N, -E*qe+Fe}, {v*B-E, -V*n+N, Fm-Fe}, {v*B-E, -dt*i+Q, -E*qe+Fe}, {v*B-E, -dt*i+Q, Fm-Fe}, {v*B-E, -E*qe+Fe, Fm-Fe}, {-E*h+UH, -v*dt+L, -V*n+N}, {-E*h+UH, -v*dt+L, -dt*i+Q}, {-E*h+UH, -v*dt+L, -E*qe+Fe}, {-E*h+UH, -v*dt+L, Fm-Fe}, {-E*h+UH, -V*n+N, -dt*i+Q}, {-E*h+UH, -V*n+N, -E*qe+Fe}, {-E*h+UH, -V*n+N, Fm-Fe}, {-E*h+UH, -dt*i+Q, -E*qe+Fe}, {-E*h+UH, -dt*i+Q, Fm-Fe}, {-E*h+UH, -E*qe+Fe, Fm-Fe}, {-v*dt+L, -V*n+N, -dt*i+Q}, {-v*dt+L, -V*n+N, -E*qe+Fe}, {-v*dt+L, -V*n+N, Fm-Fe}, {-v*dt+L, -dt*i+Q, -E*qe+Fe}, {-v*dt+L, -dt*i+Q, Fm-Fe}, {-v*dt+L, -E*qe+Fe, Fm-Fe}, {-V*n+N, -dt*i+Q, -E*qe+Fe}, {-V*n+N, -dt*i+Q, Fm-Fe}, {-V*n+N, -E*qe+Fe, Fm-Fe}, {-dt*i+Q, -E*qe+Fe, Fm-Fe}, {-E*h+UH}, {-v*dt+L}, {qe}, {i}, {-V*n+N}, {-dt*i+Q}, {-E*qe+Fe}, {Fm-Fe}, {-E*h+UH, -v*dt+L}, {-E*h+UH, qe}, {-E*h+UH, i}, {-E*h+UH, -V*n+N}, {-E*h+UH, -dt*i+Q}, {-E*h+UH, -E*qe+Fe}, {-E*h+UH, Fm-Fe}, {-v*dt+L, qe}, {-v*dt+L, i}, {-v*dt+L, -V*n+N}, {-v*dt+L, -dt*i+Q}, {-v*dt+L, -E*qe+Fe}, {-v*dt+L, Fm-Fe}, {qe, i}, {qe, -V*n+N}, {qe, -dt*i+Q}, {qe, -E*qe+Fe}, {qe, Fm-Fe}, {i, -V*n+N}, {i, -dt*i+Q}, {i, -E*qe+Fe}, {i, Fm-Fe}, {-V*n+N, -dt*i+Q}, {-V*n+N, -E*qe+Fe}, {-V*n+N, Fm-Fe}, {-dt*i+Q, -E*qe+Fe}, {-dt*i+Q, Fm-Fe}, {-E*qe+Fe, Fm-Fe}, {-E*h+UH, -v*dt+L, qe}, {-E*h+UH, -v*dt+L, i}, {-E*h+UH, -v*dt+L, -V*n+N}, {-E*h+UH, -v*dt+L, -dt*i+Q}, {-E*h+UH, -v*dt+L, -E*qe+Fe}, {-E*h+UH, -v*dt+L, Fm-Fe}, {-E*h+UH, qe, i}, {-E*h+UH, qe, -V*n+N}, {-E*h+UH, qe, -dt*i+Q}, {-E*h+UH, qe, -E*qe+Fe}, {-E*h+UH, qe, Fm-Fe}, {-E*h+UH, i, -V*n+N}, {-E*h+UH, i, -dt*i+Q}, {-E*h+UH, i, -E*qe+Fe}, {-E*h+UH, i, Fm-Fe}, {-E*h+UH, -V*n+N, -dt*i+Q}, {-E*h+UH, -V*n+N, -E*qe+Fe}, {-E*h+UH, -V*n+N, Fm-Fe}, {-E*h+UH, -dt*i+Q, -E*qe+Fe}, {-E*h+UH, -dt*i+Q, Fm-Fe}, {-E*h+UH, -E*qe+Fe, Fm-Fe}, {-v*dt+L, qe, i}, {-v*dt+L, qe, -V*n+N}, {-v*dt+L, qe, -dt*i+Q}, {-v*dt+L, qe, -E*qe+Fe}, {-v*dt+L, qe, Fm-Fe}, {-v*dt+L, i, -V*n+N}, {-v*dt+L, i, -dt*i+Q}, {-v*dt+L, i, -E*qe+Fe}, {-v*dt+L, i, Fm-Fe}, {-v*dt+L, -V*n+N, -dt*i+Q}, {-v*dt+L, -V*n+N, -E*qe+Fe}, {-v*dt+L, -V*n+N, Fm-Fe}, {-v*dt+L, -dt*i+Q, -E*qe+Fe}, {-v*dt+L, -dt*i+Q, Fm-Fe}, {-v*dt+L, -E*qe+Fe, Fm-Fe}, {qe, i, -V*n+N}, {qe, i, -dt*i+Q}, {qe, i, -E*qe+Fe}, {qe, i, Fm-Fe}, {qe, -V*n+N, -dt*i+Q}, {qe, -V*n+N, -E*qe+Fe}, {qe, -V*n+N, Fm-Fe}, {qe, -dt*i+Q, -E*qe+Fe}, {qe, -dt*i+Q, Fm-Fe}, {qe, -E*qe+Fe, Fm-Fe}, {i, -V*n+N, -dt*i+Q}, {i, -V*n+N, -E*qe+Fe}, {i, -V*n+N, Fm-Fe}, {i, -dt*i+Q, -E*qe+Fe}, {i, -dt*i+Q, Fm-Fe}, {i, -E*qe+Fe, Fm-Fe}, {-V*n+N, -dt*i+Q, -E*qe+Fe}, {-V*n+N, -dt*i+Q, Fm-Fe}, {-V*n+N, -E*qe+Fe, Fm-Fe}, {-dt*i+Q, -E*qe+Fe, Fm-Fe}, {-E*h+UH}, {-v*dt+L}, {n}, {i}, {-V*n+N}, {-dt*i+Q}, {-E*qe+Fe}, {Fm-Fe}, {-E*h+UH, -v*dt+L}, {-E*h+UH, n}, {-E*h+UH, i}, {-E*h+UH, -V*n+N}, {-E*h+UH, -dt*i+Q}, {-E*h+UH, -E*qe+Fe}, {-E*h+UH, Fm-Fe}, {-v*dt+L, n}, {-v*dt+L, i}, {-v*dt+L, -V*n+N}, {-v*dt+L, -dt*i+Q}, {-v*dt+L, -E*qe+Fe}, {-v*dt+L, Fm-Fe}, {n, i}, {n, -V*n+N}, {n, -dt*i+Q}, {n, -E*qe+Fe}, {n, Fm-Fe}, {i, -V*n+N}, {i, -dt*i+Q}, {i, -E*qe+Fe}, {i, Fm-Fe}, {-V*n+N, -dt*i+Q}, {-V*n+N, -E*qe+Fe}, {-V*n+N, Fm-Fe}, {-dt*i+Q, -E*qe+Fe}, {-dt*i+Q, Fm-Fe}, {-E*qe+Fe, Fm-Fe}, {-E*h+UH, -v*dt+L, n}, {-E*h+UH, -v*dt+L, i}, {-E*h+UH, -v*dt+L, -V*n+N}, {-E*h+UH, -v*dt+L, -dt*i+Q}, {-E*h+UH, -v*dt+L, -E*qe+Fe}, {-E*h+UH, -v*dt+L, Fm-Fe}, {-E*h+UH, n, i}, {-E*h+UH, n, -V*n+N}, {-E*h+UH, n, -dt*i+Q}, {-E*h+UH, n, -E*qe+Fe}, {-E*h+UH, n, Fm-Fe}, {-E*h+UH, i, -V*n+N}, {-E*h+UH, i, -dt*i+Q}, {-E*h+UH, i, -E*qe+Fe}, {-E*h+UH, i, Fm-Fe}, {-E*h+UH, -V*n+N, -dt*i+Q}, {-E*h+UH, -V*n+N, -E*qe+Fe}, {-E*h+UH, -V*n+N, Fm-Fe}, {-E*h+UH, -dt*i+Q, -E*qe+Fe}, {-E*h+UH, -dt*i+Q, Fm-Fe}, {-E*h+UH, -E*qe+Fe, Fm-Fe}, {-v*dt+L, n, i}, {-v*dt+L, n, -V*n+N}, {-v*dt+L, n, -dt*i+Q}, {-v*dt+L, n, -E*qe+Fe}, {-v*dt+L, n, Fm-Fe}, {-v*dt+L, i, -V*n+N}, {-v*dt+L, i, -dt*i+Q}, {-v*dt+L, i, -E*qe+Fe}, {-v*dt+L, i, Fm-Fe}, {-v*dt+L, -V*n+N, -dt*i+Q}, {-v*dt+L, -V*n+N, -E*qe+Fe}, {-v*dt+L, -V*n+N, Fm-Fe}, {-v*dt+L, -dt*i+Q, -E*qe+Fe}, {-v*dt+L, -dt*i+Q, Fm-Fe}, {-v*dt+L, -E*qe+Fe, Fm-Fe}, {n, i, -V*n+N}, {n, i, -dt*i+Q}, {n, i, -E*qe+Fe}, {n, i, Fm-Fe}, {n, -V*n+N, -dt*i+Q}, {n, -V*n+N, -E*qe+Fe}, {n, -V*n+N, Fm-Fe}, {n, -dt*i+Q, -E*qe+Fe}, {n, -dt*i+Q, Fm-Fe}, {n, -E*qe+Fe, Fm-Fe}, {i, -V*n+N, -dt*i+Q}, {i, -V*n+N, -E*qe+Fe}, {i, -V*n+N, Fm-Fe}, {i, -dt*i+Q, -E*qe+Fe}, {i, -dt*i+Q, Fm-Fe}, {i, -E*qe+Fe, Fm-Fe}, {-V*n+N, -dt*i+Q, -E*qe+Fe}, {-V*n+N, -dt*i+Q, Fm-Fe}, {-V*n+N, -E*qe+Fe, Fm-Fe}, {-dt*i+Q, -E*qe+Fe, Fm-Fe}, {-E*h+UH}, {-v*dt+L}, {i}, {V}, {-V*n+N}, {-dt*i+Q}, {-E*qe+Fe}, {Fm-Fe}, {-E*h+UH, -v*dt+L}, {-E*h+UH, i}, {-E*h+UH, V}, {-E*h+UH, -V*n+N}, {-E*h+UH, -dt*i+Q}, {-E*h+UH, -E*qe+Fe}, {-E*h+UH, Fm-Fe}, {-v*dt+L, i}, {-v*dt+L, V}, {-v*dt+L, -V*n+N}, {-v*dt+L, -dt*i+Q}, {-v*dt+L, -E*qe+Fe}, {-v*dt+L, Fm-Fe}, {i, V}, {i, -V*n+N}, {i, -dt*i+Q}, {i, -E*qe+Fe}, {i, Fm-Fe}, {V, -V*n+N}, {V, -dt*i+Q}, {V, -E*qe+Fe}, {V, Fm-Fe}, {-V*n+N, -dt*i+Q}, {-V*n+N, -E*qe+Fe}, {-V*n+N, Fm-Fe}, {-dt*i+Q, -E*qe+Fe}, {-dt*i+Q, Fm-Fe}, {-E*qe+Fe, Fm-Fe}, {-E*h+UH, -v*dt+L, i}, {-E*h+UH, -v*dt+L, V}, {-E*h+UH, -v*dt+L, -V*n+N}, {-E*h+UH, -v*dt+L, -dt*i+Q}, {-E*h+UH, -v*dt+L, -E*qe+Fe}, {-E*h+UH, -v*dt+L, Fm-Fe}, {-E*h+UH, i, V}, {-E*h+UH, i, -V*n+N}, {-E*h+UH, i, -dt*i+Q}, {-E*h+UH, i, -E*qe+Fe}, {-E*h+UH, i, Fm-Fe}, {-E*h+UH, V, -V*n+N}, {-E*h+UH, V, -dt*i+Q}, {-E*h+UH, V, -E*qe+Fe}, {-E*h+UH, V, Fm-Fe}, {-E*h+UH, -V*n+N, -dt*i+Q}, {-E*h+UH, -V*n+N, -E*qe+Fe}, {-E*h+UH, -V*n+N, Fm-Fe}, {-E*h+UH, -dt*i+Q, -E*qe+Fe}, {-E*h+UH, -dt*i+Q, Fm-Fe}, {-E*h+UH, -E*qe+Fe, Fm-Fe}, {-v*dt+L, i, V}, {-v*dt+L, i, -V*n+N}, {-v*dt+L, i, -dt*i+Q}, {-v*dt+L, i, -E*qe+Fe}, {-v*dt+L, i, Fm-Fe}, {-v*dt+L, V, -V*n+N}, {-v*dt+L, V, -dt*i+Q}, {-v*dt+L, V, -E*qe+Fe}, {-v*dt+L, V, Fm-Fe}, {-v*dt+L, -V*n+N, -dt*i+Q}, {-v*dt+L, -V*n+N, -E*qe+Fe}, {-v*dt+L, -V*n+N, Fm-Fe}, {-v*dt+L, -dt*i+Q, -E*qe+Fe}, {-v*dt+L, -dt*i+Q, Fm-Fe}, {-v*dt+L, -E*qe+Fe, Fm-Fe}, {i, V, -V*n+N}, {i, V, -dt*i+Q}, {i, V, -E*qe+Fe}, {i, V, Fm-Fe}, {i, -V*n+N, -dt*i+Q}, {i, -V*n+N, -E*qe+Fe}, {i, -V*n+N, Fm-Fe}, {i, -dt*i+Q, -E*qe+Fe}, {i, -dt*i+Q, Fm-Fe}, {i, -E*qe+Fe, Fm-Fe}, {V, -V*n+N, -dt*i+Q}, {V, -V*n+N, -E*qe+Fe}, {V, -V*n+N, Fm-Fe}, {V, -dt*i+Q, -E*qe+Fe}, {V, -dt*i+Q, Fm-Fe}, {V, -E*qe+Fe, Fm-Fe}, {-V*n+N, -dt*i+Q, -E*qe+Fe}, {-V*n+N, -dt*i+Q, Fm-Fe}, {-V*n+N, -E*qe+Fe, Fm-Fe}, {-dt*i+Q, -E*qe+Fe, Fm-Fe}, {-E*h+UH}, {-v*dt+L}, {qe}, {-V*n+N}, {-dt*i+Q}, {dt}, {-E*qe+Fe}, {Fm-Fe}, {-E*h+UH, -v*dt+L}, {-E*h+UH, qe}, {-E*h+UH, -V*n+N}, {-E*h+UH, -dt*i+Q}, {-E*h+UH, dt}, {-E*h+UH, -E*qe+Fe}, {-E*h+UH, Fm-Fe}, {-v*dt+L, qe}, {-v*dt+L, -V*n+N}, {-v*dt+L, -dt*i+Q}, {-v*dt+L, dt}, {-v*dt+L, -E*qe+Fe}, {-v*dt+L, Fm-Fe}, {qe, -V*n+N}, {qe, -dt*i+Q}, {qe, dt}, {qe, -E*qe+Fe}, {qe, Fm-Fe}, {-V*n+N, -dt*i+Q}, {-V*n+N, dt}, {-V*n+N, -E*qe+Fe}, {-V*n+N, Fm-Fe}, {-dt*i+Q, dt}, {-dt*i+Q, -E*qe+Fe}, {-dt*i+Q, Fm-Fe}, {dt, -E*qe+Fe}, {dt, Fm-Fe}, {-E*qe+Fe, Fm-Fe}, {-E*h+UH, -v*dt+L, qe}, {-E*h+UH, -v*dt+L, -V*n+N}, {-E*h+UH, -v*dt+L, -dt*i+Q}, {-E*h+UH, -v*dt+L, dt}, {-E*h+UH, -v*dt+L, -E*qe+Fe}, {-E*h+UH, -v*dt+L, Fm-Fe}, {-E*h+UH, qe, -V*n+N}, {-E*h+UH, qe, -dt*i+Q}, {-E*h+UH, qe, dt}, {-E*h+UH, qe, -E*qe+Fe}, {-E*h+UH, qe, Fm-Fe}, {-E*h+UH, -V*n+N, -dt*i+Q}, {-E*h+UH, -V*n+N, dt}, {-E*h+UH, -V*n+N, -E*qe+Fe}, {-E*h+UH, -V*n+N, Fm-Fe}, {-E*h+UH, -dt*i+Q, dt}, {-E*h+UH, -dt*i+Q, -E*qe+Fe}, {-E*h+UH, -dt*i+Q, Fm-Fe}, {-E*h+UH, dt, -E*qe+Fe}, {-E*h+UH, dt, Fm-Fe}, {-E*h+UH, -E*qe+Fe, Fm-Fe}, {-v*dt+L, qe, -V*n+N}, {-v*dt+L, qe, -dt*i+Q}, {-v*dt+L, qe, dt}, {-v*dt+L, qe, -E*qe+Fe}, {-v*dt+L, qe, Fm-Fe}, {-v*dt+L, -V*n+N, -dt*i+Q}, {-v*dt+L, -V*n+N, dt}, {-v*dt+L, -V*n+N, -E*qe+Fe}, {-v*dt+L, -V*n+N, Fm-Fe}, {-v*dt+L, -dt*i+Q, dt}, {-v*dt+L, -dt*i+Q, -E*qe+Fe}, {-v*dt+L, -dt*i+Q, Fm-Fe}, {-v*dt+L, dt, -E*qe+Fe}, {-v*dt+L, dt, Fm-Fe}, {-v*dt+L, -E*qe+Fe, Fm-Fe}, {qe, -V*n+N, -dt*i+Q}, {qe, -V*n+N, dt}, {qe, -V*n+N, -E*qe+Fe}, {qe, -V*n+N, Fm-Fe}, {qe, -dt*i+Q, dt}, {qe, -dt*i+Q, -E*qe+Fe}, {qe, -dt*i+Q, Fm-Fe}, {qe, dt, -E*qe+Fe}, {qe, dt, Fm-Fe}, {qe, -E*qe+Fe, Fm-Fe}, {-V*n+N, -dt*i+Q, dt}, {-V*n+N, -dt*i+Q, -E*qe+Fe}, {-V*n+N, -dt*i+Q, Fm-Fe}, {-V*n+N, dt, -E*qe+Fe}, {-V*n+N, dt, Fm-Fe}, {-V*n+N, -E*qe+Fe, Fm-Fe}, {-dt*i+Q, dt, -E*qe+Fe}, {-dt*i+Q, dt, Fm-Fe}, {-dt*i+Q, -E*qe+Fe, Fm-Fe}, {dt, -E*qe+Fe, Fm-Fe}, {-E*h+UH}, {-v*dt+L}, {n}, {-V*n+N}, {-dt*i+Q}, {dt}, {-E*qe+Fe}, {Fm-Fe}, {-E*h+UH, -v*dt+L}, {-E*h+UH, n}, {-E*h+UH, -V*n+N}, {-E*h+UH, -dt*i+Q}, {-E*h+UH, dt}, {-E*h+UH, -E*qe+Fe}, {-E*h+UH, Fm-Fe}, {-v*dt+L, n}, {-v*dt+L, -V*n+N}, {-v*dt+L, -dt*i+Q}, {-v*dt+L, dt}, {-v*dt+L, -E*qe+Fe}, {-v*dt+L, Fm-Fe}, {n, -V*n+N}, {n, -dt*i+Q}, {n, dt}, {n, -E*qe+Fe}, {n, Fm-Fe}, {-V*n+N, -dt*i+Q}, {-V*n+N, dt}, {-V*n+N, -E*qe+Fe}, {-V*n+N, Fm-Fe}, {-dt*i+Q, dt}, {-dt*i+Q, -E*qe+Fe}, {-dt*i+Q, Fm-Fe}, {dt, -E*qe+Fe}, {dt, Fm-Fe}, {-E*qe+Fe, Fm-Fe}, {-E*h+UH, -v*dt+L, n}, {-E*h+UH, -v*dt+L, -V*n+N}, {-E*h+UH, -v*dt+L, -dt*i+Q}, {-E*h+UH, -v*dt+L, dt}, {-E*h+UH, -v*dt+L, -E*qe+Fe}, {-E*h+UH, -v*dt+L, Fm-Fe}, {-E*h+UH, n, -V*n+N}, {-E*h+UH, n, -dt*i+Q}, {-E*h+UH, n, dt}, {-E*h+UH, n, -E*qe+Fe}, {-E*h+UH, n, Fm-Fe}, {-E*h+UH, -V*n+N, -dt*i+Q}, {-E*h+UH, -V*n+N, dt}, {-E*h+UH, -V*n+N, -E*qe+Fe}, {-E*h+UH, -V*n+N, Fm-Fe}, {-E*h+UH, -dt*i+Q, dt}, {-E*h+UH, -dt*i+Q, -E*qe+Fe}, {-E*h+UH, -dt*i+Q, Fm-Fe}, {-E*h+UH, dt, -E*qe+Fe}, {-E*h+UH, dt, Fm-Fe}, {-E*h+UH, -E*qe+Fe, Fm-Fe}, {-v*dt+L, n, -V*n+N}, {-v*dt+L, n, -dt*i+Q}, {-v*dt+L, n, dt}, {-v*dt+L, n, -E*qe+Fe}, {-v*dt+L, n, Fm-Fe}, {-v*dt+L, -V*n+N, -dt*i+Q}, {-v*dt+L, -V*n+N, dt}, {-v*dt+L, -V*n+N, -E*qe+Fe}, {-v*dt+L, -V*n+N, Fm-Fe}, {-v*dt+L, -dt*i+Q, dt}, {-v*dt+L, -dt*i+Q, -E*qe+Fe}, {-v*dt+L, -dt*i+Q, Fm-Fe}, {-v*dt+L, dt, -E*qe+Fe}, {-v*dt+L, dt, Fm-Fe}, {-v*dt+L, -E*qe+Fe, Fm-Fe}, {n, -V*n+N, -dt*i+Q}, {n, -V*n+N, dt}, {n, -V*n+N, -E*qe+Fe}, {n, -V*n+N, Fm-Fe}, {n, -dt*i+Q, dt}, {n, -dt*i+Q, -E*qe+Fe}, {n, -dt*i+Q, Fm-Fe}, {n, dt, -E*qe+Fe}, {n, dt, Fm-Fe}, {n, -E*qe+Fe, Fm-Fe}, {-V*n+N, -dt*i+Q, dt}, {-V*n+N, -dt*i+Q, -E*qe+Fe}, {-V*n+N, -dt*i+Q, Fm-Fe}, {-V*n+N, dt, -E*qe+Fe}, {-V*n+N, dt, Fm-Fe}, {-V*n+N, -E*qe+Fe, Fm-Fe}, {-dt*i+Q, dt, -E*qe+Fe}, {-dt*i+Q, dt, Fm-Fe}, {-dt*i+Q, -E*qe+Fe, Fm-Fe}, {dt, -E*qe+Fe, Fm-Fe}, {-E*h+UH}, {-v*dt+L}, {V}, {-V*n+N}, {-dt*i+Q}, {dt}, {-E*qe+Fe}, {Fm-Fe}, {-E*h+UH, -v*dt+L}, {-E*h+UH, V}, {-E*h+UH, -V*n+N}, {-E*h+UH, -dt*i+Q}, {-E*h+UH, dt}, {-E*h+UH, -E*qe+Fe}, {-E*h+UH, Fm-Fe}, {-v*dt+L, V}, {-v*dt+L, -V*n+N}, {-v*dt+L, -dt*i+Q}, {-v*dt+L, dt}, {-v*dt+L, -E*qe+Fe}, {-v*dt+L, Fm-Fe}, {V, -V*n+N}, {V, -dt*i+Q}, {V, dt}, {V, -E*qe+Fe}, {V, Fm-Fe}, {-V*n+N, -dt*i+Q}, {-V*n+N, dt}, {-V*n+N, -E*qe+Fe}, {-V*n+N, Fm-Fe}, {-dt*i+Q, dt}, {-dt*i+Q, -E*qe+Fe}, {-dt*i+Q, Fm-Fe}, {dt, -E*qe+Fe}, {dt, Fm-Fe}, {-E*qe+Fe, Fm-Fe}, {-E*h+UH, -v*dt+L, V}, {-E*h+UH, -v*dt+L, -V*n+N}, {-E*h+UH, -v*dt+L, -dt*i+Q}, {-E*h+UH, -v*dt+L, dt}, {-E*h+UH, -v*dt+L, -E*qe+Fe}, {-E*h+UH, -v*dt+L, Fm-Fe}, {-E*h+UH, V, -V*n+N}, {-E*h+UH, V, -dt*i+Q}, {-E*h+UH, V, dt}, {-E*h+UH, V, -E*qe+Fe}, {-E*h+UH, V, Fm-Fe}, {-E*h+UH, -V*n+N, -dt*i+Q}, {-E*h+UH, -V*n+N, dt}, {-E*h+UH, -V*n+N, -E*qe+Fe}, {-E*h+UH, -V*n+N, Fm-Fe}, {-E*h+UH, -dt*i+Q, dt}, {-E*h+UH, -dt*i+Q, -E*qe+Fe}, {-E*h+UH, -dt*i+Q, Fm-Fe}, {-E*h+UH, dt, -E*qe+Fe}, {-E*h+UH, dt, Fm-Fe}, {-E*h+UH, -E*qe+Fe, Fm-Fe}, {-v*dt+L, V, -V*n+N}, {-v*dt+L, V, -dt*i+Q}, {-v*dt+L, V, dt}, {-v*dt+L, V, -E*qe+Fe}, {-v*dt+L, V, Fm-Fe}, {-v*dt+L, -V*n+N, -dt*i+Q}, {-v*dt+L, -V*n+N, dt}, {-v*dt+L, -V*n+N, -E*qe+Fe}, {-v*dt+L, -V*n+N, Fm-Fe}, {-v*dt+L, -dt*i+Q, dt}, {-v*dt+L, -dt*i+Q, -E*qe+Fe}, {-v*dt+L, -dt*i+Q, Fm-Fe}, {-v*dt+L, dt, -E*qe+Fe}, {-v*dt+L, dt, Fm-Fe}, {-v*dt+L, -E*qe+Fe, Fm-Fe}, {V, -V*n+N, -dt*i+Q}, {V, -V*n+N, dt}, {V, -V*n+N, -E*qe+Fe}, {V, -V*n+N, Fm-Fe}, {V, -dt*i+Q, dt}, {V, -dt*i+Q, -E*qe+Fe}, {V, -dt*i+Q, Fm-Fe}, {V, dt, -E*qe+Fe}, {V, dt, Fm-Fe}, {V, -E*qe+Fe, Fm-Fe}, {-V*n+N, -dt*i+Q, dt}, {-V*n+N, -dt*i+Q, -E*qe+Fe}, {-V*n+N, -dt*i+Q, Fm-Fe}, {-V*n+N, dt, -E*qe+Fe}, {-V*n+N, dt, Fm-Fe}, {-V*n+N, -E*qe+Fe, Fm-Fe}, {-dt*i+Q, dt, -E*qe+Fe}, {-dt*i+Q, dt, Fm-Fe}, {-dt*i+Q, -E*qe+Fe, Fm-Fe}, {dt, -E*qe+Fe, Fm-Fe}};

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
f = openOut "results/hall/abduction/noiseless/2_axiom(s)_removed/combo_1_9/reasoning/reasoning_output.txt";
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

print("Reasoning complete. Output written to results/hall/abduction/noiseless/2_axiom(s)_removed/combo_1_9/reasoning/reasoning_output.txt");
