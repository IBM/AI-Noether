-- AI-Noether: Reasoning Template (Noiseless)
-- Tests if candidate axiom sets, when added to remaining axioms, prove targets

needsPackage("PrimaryDecomposition", Reload => true)

-- Ring definition
R = QQ[Fm, d, v, Fe, E, dt, Q, N, V, i, n, qe, B, h, L, UH, MonomialOrder => Lex];

-- Input data
remainingAxioms = toList([Fm - Fe, E*h - UH, v*dt - L, i*dt - Q, Q - N*qe, V - L*h*d]);
qList = toList([N*qe*UH - i*B*h*L]);
k = #qList;

-- Per-target variable partitions
measuredPerTarget = {{UH, h, L, i, B, N, qe}};
nonMeasuredPerTarget = {{Fm, d, v, Fe, E, dt, Q, V, n}};

-- Candidate axiom sets to test (list of lists)
candidateSets = {{}, {dt*i-N*qe}, {-E*h+UH}, {-v*dt+L}, {h}, {-d*h*L+V}, {-dt*i+Q}, {Fm-Fe}, {dt*i-N*qe, -E*h+UH}, {dt*i-N*qe, -v*dt+L}, {dt*i-N*qe, h}, {dt*i-N*qe, -d*h*L+V}, {dt*i-N*qe, -dt*i+Q}, {dt*i-N*qe, Fm-Fe}, {-E*h+UH, -v*dt+L}, {-E*h+UH, h}, {-E*h+UH, -d*h*L+V}, {-E*h+UH, -dt*i+Q}, {-E*h+UH, Fm-Fe}, {-v*dt+L, h}, {-v*dt+L, -d*h*L+V}, {-v*dt+L, -dt*i+Q}, {-v*dt+L, Fm-Fe}, {h, -d*h*L+V}, {h, -dt*i+Q}, {h, Fm-Fe}, {-d*h*L+V, -dt*i+Q}, {-d*h*L+V, Fm-Fe}, {-dt*i+Q, Fm-Fe}, {dt*i-N*qe, -E*h+UH, -v*dt+L}, {dt*i-N*qe, -E*h+UH, h}, {dt*i-N*qe, -E*h+UH, -d*h*L+V}, {dt*i-N*qe, -E*h+UH, -dt*i+Q}, {dt*i-N*qe, -E*h+UH, Fm-Fe}, {dt*i-N*qe, -v*dt+L, h}, {dt*i-N*qe, -v*dt+L, -d*h*L+V}, {dt*i-N*qe, -v*dt+L, -dt*i+Q}, {dt*i-N*qe, -v*dt+L, Fm-Fe}, {dt*i-N*qe, h, -d*h*L+V}, {dt*i-N*qe, h, -dt*i+Q}, {dt*i-N*qe, h, Fm-Fe}, {dt*i-N*qe, -d*h*L+V, -dt*i+Q}, {dt*i-N*qe, -d*h*L+V, Fm-Fe}, {dt*i-N*qe, -dt*i+Q, Fm-Fe}, {-E*h+UH, -v*dt+L, h}, {-E*h+UH, -v*dt+L, -d*h*L+V}, {-E*h+UH, -v*dt+L, -dt*i+Q}, {-E*h+UH, -v*dt+L, Fm-Fe}, {-E*h+UH, h, -d*h*L+V}, {-E*h+UH, h, -dt*i+Q}, {-E*h+UH, h, Fm-Fe}, {-E*h+UH, -d*h*L+V, -dt*i+Q}, {-E*h+UH, -d*h*L+V, Fm-Fe}, {-E*h+UH, -dt*i+Q, Fm-Fe}, {-v*dt+L, h, -d*h*L+V}, {-v*dt+L, h, -dt*i+Q}, {-v*dt+L, h, Fm-Fe}, {-v*dt+L, -d*h*L+V, -dt*i+Q}, {-v*dt+L, -d*h*L+V, Fm-Fe}, {-v*dt+L, -dt*i+Q, Fm-Fe}, {h, -d*h*L+V, -dt*i+Q}, {h, -d*h*L+V, Fm-Fe}, {h, -dt*i+Q, Fm-Fe}, {-d*h*L+V, -dt*i+Q, Fm-Fe}, {dt*i-N*qe, -E*h+UH, -v*dt+L, h}, {dt*i-N*qe, -E*h+UH, -v*dt+L, -d*h*L+V}, {dt*i-N*qe, -E*h+UH, -v*dt+L, -dt*i+Q}, {dt*i-N*qe, -E*h+UH, -v*dt+L, Fm-Fe}, {dt*i-N*qe, -E*h+UH, h, -d*h*L+V}, {dt*i-N*qe, -E*h+UH, h, -dt*i+Q}, {dt*i-N*qe, -E*h+UH, h, Fm-Fe}, {dt*i-N*qe, -E*h+UH, -d*h*L+V, -dt*i+Q}, {dt*i-N*qe, -E*h+UH, -d*h*L+V, Fm-Fe}, {dt*i-N*qe, -E*h+UH, -dt*i+Q, Fm-Fe}, {dt*i-N*qe, -v*dt+L, h, -d*h*L+V}, {dt*i-N*qe, -v*dt+L, h, -dt*i+Q}, {dt*i-N*qe, -v*dt+L, h, Fm-Fe}, {dt*i-N*qe, -v*dt+L, -d*h*L+V, -dt*i+Q}, {dt*i-N*qe, -v*dt+L, -d*h*L+V, Fm-Fe}, {dt*i-N*qe, -v*dt+L, -dt*i+Q, Fm-Fe}, {dt*i-N*qe, h, -d*h*L+V, -dt*i+Q}, {dt*i-N*qe, h, -d*h*L+V, Fm-Fe}, {dt*i-N*qe, h, -dt*i+Q, Fm-Fe}, {dt*i-N*qe, -d*h*L+V, -dt*i+Q, Fm-Fe}, {-E*h+UH, -v*dt+L, h, -d*h*L+V}, {-E*h+UH, -v*dt+L, h, -dt*i+Q}, {-E*h+UH, -v*dt+L, h, Fm-Fe}, {-E*h+UH, -v*dt+L, -d*h*L+V, -dt*i+Q}, {-E*h+UH, -v*dt+L, -d*h*L+V, Fm-Fe}, {-E*h+UH, -v*dt+L, -dt*i+Q, Fm-Fe}, {-E*h+UH, h, -d*h*L+V, -dt*i+Q}, {-E*h+UH, h, -d*h*L+V, Fm-Fe}, {-E*h+UH, h, -dt*i+Q, Fm-Fe}, {-E*h+UH, -d*h*L+V, -dt*i+Q, Fm-Fe}, {-v*dt+L, h, -d*h*L+V, -dt*i+Q}, {-v*dt+L, h, -d*h*L+V, Fm-Fe}, {-v*dt+L, h, -dt*i+Q, Fm-Fe}, {-v*dt+L, -d*h*L+V, -dt*i+Q, Fm-Fe}, {h, -d*h*L+V, -dt*i+Q, Fm-Fe}, {dt*i-N*qe}, {v*B-E}, {-E*h+UH}, {-v*dt+L}, {-d*h*L+V}, {-dt*i+Q}, {Fm-Fe}, {dt*i-N*qe, v*B-E}, {dt*i-N*qe, -E*h+UH}, {dt*i-N*qe, -v*dt+L}, {dt*i-N*qe, -d*h*L+V}, {dt*i-N*qe, -dt*i+Q}, {dt*i-N*qe, Fm-Fe}, {v*B-E, -E*h+UH}, {v*B-E, -v*dt+L}, {v*B-E, -d*h*L+V}, {v*B-E, -dt*i+Q}, {v*B-E, Fm-Fe}, {-E*h+UH, -v*dt+L}, {-E*h+UH, -d*h*L+V}, {-E*h+UH, -dt*i+Q}, {-E*h+UH, Fm-Fe}, {-v*dt+L, -d*h*L+V}, {-v*dt+L, -dt*i+Q}, {-v*dt+L, Fm-Fe}, {-d*h*L+V, -dt*i+Q}, {-d*h*L+V, Fm-Fe}, {-dt*i+Q, Fm-Fe}, {dt*i-N*qe, v*B-E, -E*h+UH}, {dt*i-N*qe, v*B-E, -v*dt+L}, {dt*i-N*qe, v*B-E, -d*h*L+V}, {dt*i-N*qe, v*B-E, -dt*i+Q}, {dt*i-N*qe, v*B-E, Fm-Fe}, {dt*i-N*qe, -E*h+UH, -v*dt+L}, {dt*i-N*qe, -E*h+UH, -d*h*L+V}, {dt*i-N*qe, -E*h+UH, -dt*i+Q}, {dt*i-N*qe, -E*h+UH, Fm-Fe}, {dt*i-N*qe, -v*dt+L, -d*h*L+V}, {dt*i-N*qe, -v*dt+L, -dt*i+Q}, {dt*i-N*qe, -v*dt+L, Fm-Fe}, {dt*i-N*qe, -d*h*L+V, -dt*i+Q}, {dt*i-N*qe, -d*h*L+V, Fm-Fe}, {dt*i-N*qe, -dt*i+Q, Fm-Fe}, {v*B-E, -E*h+UH, -v*dt+L}, {v*B-E, -E*h+UH, -d*h*L+V}, {v*B-E, -E*h+UH, -dt*i+Q}, {v*B-E, -E*h+UH, Fm-Fe}, {v*B-E, -v*dt+L, -d*h*L+V}, {v*B-E, -v*dt+L, -dt*i+Q}, {v*B-E, -v*dt+L, Fm-Fe}, {v*B-E, -d*h*L+V, -dt*i+Q}, {v*B-E, -d*h*L+V, Fm-Fe}, {v*B-E, -dt*i+Q, Fm-Fe}, {-E*h+UH, -v*dt+L, -d*h*L+V}, {-E*h+UH, -v*dt+L, -dt*i+Q}, {-E*h+UH, -v*dt+L, Fm-Fe}, {-E*h+UH, -d*h*L+V, -dt*i+Q}, {-E*h+UH, -d*h*L+V, Fm-Fe}, {-E*h+UH, -dt*i+Q, Fm-Fe}, {-v*dt+L, -d*h*L+V, -dt*i+Q}, {-v*dt+L, -d*h*L+V, Fm-Fe}, {-v*dt+L, -dt*i+Q, Fm-Fe}, {-d*h*L+V, -dt*i+Q, Fm-Fe}, {dt*i-N*qe, v*B-E, -E*h+UH, -v*dt+L}, {dt*i-N*qe, v*B-E, -E*h+UH, -d*h*L+V}, {dt*i-N*qe, v*B-E, -E*h+UH, -dt*i+Q}, {dt*i-N*qe, v*B-E, -E*h+UH, Fm-Fe}, {dt*i-N*qe, v*B-E, -v*dt+L, -d*h*L+V}, {dt*i-N*qe, v*B-E, -v*dt+L, -dt*i+Q}, {dt*i-N*qe, v*B-E, -v*dt+L, Fm-Fe}, {dt*i-N*qe, v*B-E, -d*h*L+V, -dt*i+Q}, {dt*i-N*qe, v*B-E, -d*h*L+V, Fm-Fe}, {dt*i-N*qe, v*B-E, -dt*i+Q, Fm-Fe}, {dt*i-N*qe, -E*h+UH, -v*dt+L, -d*h*L+V}, {dt*i-N*qe, -E*h+UH, -v*dt+L, -dt*i+Q}, {dt*i-N*qe, -E*h+UH, -v*dt+L, Fm-Fe}, {dt*i-N*qe, -E*h+UH, -d*h*L+V, -dt*i+Q}, {dt*i-N*qe, -E*h+UH, -d*h*L+V, Fm-Fe}, {dt*i-N*qe, -E*h+UH, -dt*i+Q, Fm-Fe}, {dt*i-N*qe, -v*dt+L, -d*h*L+V, -dt*i+Q}, {dt*i-N*qe, -v*dt+L, -d*h*L+V, Fm-Fe}, {dt*i-N*qe, -v*dt+L, -dt*i+Q, Fm-Fe}, {dt*i-N*qe, -d*h*L+V, -dt*i+Q, Fm-Fe}, {v*B-E, -E*h+UH, -v*dt+L, -d*h*L+V}, {v*B-E, -E*h+UH, -v*dt+L, -dt*i+Q}, {v*B-E, -E*h+UH, -v*dt+L, Fm-Fe}, {v*B-E, -E*h+UH, -d*h*L+V, -dt*i+Q}, {v*B-E, -E*h+UH, -d*h*L+V, Fm-Fe}, {v*B-E, -E*h+UH, -dt*i+Q, Fm-Fe}, {v*B-E, -v*dt+L, -d*h*L+V, -dt*i+Q}, {v*B-E, -v*dt+L, -d*h*L+V, Fm-Fe}, {v*B-E, -v*dt+L, -dt*i+Q, Fm-Fe}, {v*B-E, -d*h*L+V, -dt*i+Q, Fm-Fe}, {-E*h+UH, -v*dt+L, -d*h*L+V, -dt*i+Q}, {-E*h+UH, -v*dt+L, -d*h*L+V, Fm-Fe}, {-E*h+UH, -v*dt+L, -dt*i+Q, Fm-Fe}, {-E*h+UH, -d*h*L+V, -dt*i+Q, Fm-Fe}, {-v*dt+L, -d*h*L+V, -dt*i+Q, Fm-Fe}, {-E*h+UH}, {-v*dt+L}, {qe}, {i}, {-d*h*L+V}, {-dt*i+Q}, {Fm-Fe}, {-E*h+UH, -v*dt+L}, {-E*h+UH, qe}, {-E*h+UH, i}, {-E*h+UH, -d*h*L+V}, {-E*h+UH, -dt*i+Q}, {-E*h+UH, Fm-Fe}, {-v*dt+L, qe}, {-v*dt+L, i}, {-v*dt+L, -d*h*L+V}, {-v*dt+L, -dt*i+Q}, {-v*dt+L, Fm-Fe}, {qe, i}, {qe, -d*h*L+V}, {qe, -dt*i+Q}, {qe, Fm-Fe}, {i, -d*h*L+V}, {i, -dt*i+Q}, {i, Fm-Fe}, {-d*h*L+V, -dt*i+Q}, {-d*h*L+V, Fm-Fe}, {-dt*i+Q, Fm-Fe}, {-E*h+UH, -v*dt+L, qe}, {-E*h+UH, -v*dt+L, i}, {-E*h+UH, -v*dt+L, -d*h*L+V}, {-E*h+UH, -v*dt+L, -dt*i+Q}, {-E*h+UH, -v*dt+L, Fm-Fe}, {-E*h+UH, qe, i}, {-E*h+UH, qe, -d*h*L+V}, {-E*h+UH, qe, -dt*i+Q}, {-E*h+UH, qe, Fm-Fe}, {-E*h+UH, i, -d*h*L+V}, {-E*h+UH, i, -dt*i+Q}, {-E*h+UH, i, Fm-Fe}, {-E*h+UH, -d*h*L+V, -dt*i+Q}, {-E*h+UH, -d*h*L+V, Fm-Fe}, {-E*h+UH, -dt*i+Q, Fm-Fe}, {-v*dt+L, qe, i}, {-v*dt+L, qe, -d*h*L+V}, {-v*dt+L, qe, -dt*i+Q}, {-v*dt+L, qe, Fm-Fe}, {-v*dt+L, i, -d*h*L+V}, {-v*dt+L, i, -dt*i+Q}, {-v*dt+L, i, Fm-Fe}, {-v*dt+L, -d*h*L+V, -dt*i+Q}, {-v*dt+L, -d*h*L+V, Fm-Fe}, {-v*dt+L, -dt*i+Q, Fm-Fe}, {qe, i, -d*h*L+V}, {qe, i, -dt*i+Q}, {qe, i, Fm-Fe}, {qe, -d*h*L+V, -dt*i+Q}, {qe, -d*h*L+V, Fm-Fe}, {qe, -dt*i+Q, Fm-Fe}, {i, -d*h*L+V, -dt*i+Q}, {i, -d*h*L+V, Fm-Fe}, {i, -dt*i+Q, Fm-Fe}, {-d*h*L+V, -dt*i+Q, Fm-Fe}, {-E*h+UH, -v*dt+L, qe, i}, {-E*h+UH, -v*dt+L, qe, -d*h*L+V}, {-E*h+UH, -v*dt+L, qe, -dt*i+Q}, {-E*h+UH, -v*dt+L, qe, Fm-Fe}, {-E*h+UH, -v*dt+L, i, -d*h*L+V}, {-E*h+UH, -v*dt+L, i, -dt*i+Q}, {-E*h+UH, -v*dt+L, i, Fm-Fe}, {-E*h+UH, -v*dt+L, -d*h*L+V, -dt*i+Q}, {-E*h+UH, -v*dt+L, -d*h*L+V, Fm-Fe}, {-E*h+UH, -v*dt+L, -dt*i+Q, Fm-Fe}, {-E*h+UH, qe, i, -d*h*L+V}, {-E*h+UH, qe, i, -dt*i+Q}, {-E*h+UH, qe, i, Fm-Fe}, {-E*h+UH, qe, -d*h*L+V, -dt*i+Q}, {-E*h+UH, qe, -d*h*L+V, Fm-Fe}, {-E*h+UH, qe, -dt*i+Q, Fm-Fe}, {-E*h+UH, i, -d*h*L+V, -dt*i+Q}, {-E*h+UH, i, -d*h*L+V, Fm-Fe}, {-E*h+UH, i, -dt*i+Q, Fm-Fe}, {-E*h+UH, -d*h*L+V, -dt*i+Q, Fm-Fe}, {-v*dt+L, qe, i, -d*h*L+V}, {-v*dt+L, qe, i, -dt*i+Q}, {-v*dt+L, qe, i, Fm-Fe}, {-v*dt+L, qe, -d*h*L+V, -dt*i+Q}, {-v*dt+L, qe, -d*h*L+V, Fm-Fe}, {-v*dt+L, qe, -dt*i+Q, Fm-Fe}, {-v*dt+L, i, -d*h*L+V, -dt*i+Q}, {-v*dt+L, i, -d*h*L+V, Fm-Fe}, {-v*dt+L, i, -dt*i+Q, Fm-Fe}, {-v*dt+L, -d*h*L+V, -dt*i+Q, Fm-Fe}, {qe, i, -d*h*L+V, -dt*i+Q}, {qe, i, -d*h*L+V, Fm-Fe}, {qe, i, -dt*i+Q, Fm-Fe}, {qe, -d*h*L+V, -dt*i+Q, Fm-Fe}, {i, -d*h*L+V, -dt*i+Q, Fm-Fe}, {-E*h+UH}, {-v*dt+L}, {qe}, {-d*h*L+V}, {-dt*i+Q}, {dt}, {Fm-Fe}, {-E*h+UH, -v*dt+L}, {-E*h+UH, qe}, {-E*h+UH, -d*h*L+V}, {-E*h+UH, -dt*i+Q}, {-E*h+UH, dt}, {-E*h+UH, Fm-Fe}, {-v*dt+L, qe}, {-v*dt+L, -d*h*L+V}, {-v*dt+L, -dt*i+Q}, {-v*dt+L, dt}, {-v*dt+L, Fm-Fe}, {qe, -d*h*L+V}, {qe, -dt*i+Q}, {qe, dt}, {qe, Fm-Fe}, {-d*h*L+V, -dt*i+Q}, {-d*h*L+V, dt}, {-d*h*L+V, Fm-Fe}, {-dt*i+Q, dt}, {-dt*i+Q, Fm-Fe}, {dt, Fm-Fe}, {-E*h+UH, -v*dt+L, qe}, {-E*h+UH, -v*dt+L, -d*h*L+V}, {-E*h+UH, -v*dt+L, -dt*i+Q}, {-E*h+UH, -v*dt+L, dt}, {-E*h+UH, -v*dt+L, Fm-Fe}, {-E*h+UH, qe, -d*h*L+V}, {-E*h+UH, qe, -dt*i+Q}, {-E*h+UH, qe, dt}, {-E*h+UH, qe, Fm-Fe}, {-E*h+UH, -d*h*L+V, -dt*i+Q}, {-E*h+UH, -d*h*L+V, dt}, {-E*h+UH, -d*h*L+V, Fm-Fe}, {-E*h+UH, -dt*i+Q, dt}, {-E*h+UH, -dt*i+Q, Fm-Fe}, {-E*h+UH, dt, Fm-Fe}, {-v*dt+L, qe, -d*h*L+V}, {-v*dt+L, qe, -dt*i+Q}, {-v*dt+L, qe, dt}, {-v*dt+L, qe, Fm-Fe}, {-v*dt+L, -d*h*L+V, -dt*i+Q}, {-v*dt+L, -d*h*L+V, dt}, {-v*dt+L, -d*h*L+V, Fm-Fe}, {-v*dt+L, -dt*i+Q, dt}, {-v*dt+L, -dt*i+Q, Fm-Fe}, {-v*dt+L, dt, Fm-Fe}, {qe, -d*h*L+V, -dt*i+Q}, {qe, -d*h*L+V, dt}, {qe, -d*h*L+V, Fm-Fe}, {qe, -dt*i+Q, dt}, {qe, -dt*i+Q, Fm-Fe}, {qe, dt, Fm-Fe}, {-d*h*L+V, -dt*i+Q, dt}, {-d*h*L+V, -dt*i+Q, Fm-Fe}, {-d*h*L+V, dt, Fm-Fe}, {-dt*i+Q, dt, Fm-Fe}, {-E*h+UH, -v*dt+L, qe, -d*h*L+V}, {-E*h+UH, -v*dt+L, qe, -dt*i+Q}, {-E*h+UH, -v*dt+L, qe, dt}, {-E*h+UH, -v*dt+L, qe, Fm-Fe}, {-E*h+UH, -v*dt+L, -d*h*L+V, -dt*i+Q}, {-E*h+UH, -v*dt+L, -d*h*L+V, dt}, {-E*h+UH, -v*dt+L, -d*h*L+V, Fm-Fe}, {-E*h+UH, -v*dt+L, -dt*i+Q, dt}, {-E*h+UH, -v*dt+L, -dt*i+Q, Fm-Fe}, {-E*h+UH, -v*dt+L, dt, Fm-Fe}, {-E*h+UH, qe, -d*h*L+V, -dt*i+Q}, {-E*h+UH, qe, -d*h*L+V, dt}, {-E*h+UH, qe, -d*h*L+V, Fm-Fe}, {-E*h+UH, qe, -dt*i+Q, dt}, {-E*h+UH, qe, -dt*i+Q, Fm-Fe}, {-E*h+UH, qe, dt, Fm-Fe}, {-E*h+UH, -d*h*L+V, -dt*i+Q, dt}, {-E*h+UH, -d*h*L+V, -dt*i+Q, Fm-Fe}, {-E*h+UH, -d*h*L+V, dt, Fm-Fe}, {-E*h+UH, -dt*i+Q, dt, Fm-Fe}, {-v*dt+L, qe, -d*h*L+V, -dt*i+Q}, {-v*dt+L, qe, -d*h*L+V, dt}, {-v*dt+L, qe, -d*h*L+V, Fm-Fe}, {-v*dt+L, qe, -dt*i+Q, dt}, {-v*dt+L, qe, -dt*i+Q, Fm-Fe}, {-v*dt+L, qe, dt, Fm-Fe}, {-v*dt+L, -d*h*L+V, -dt*i+Q, dt}, {-v*dt+L, -d*h*L+V, -dt*i+Q, Fm-Fe}, {-v*dt+L, -d*h*L+V, dt, Fm-Fe}, {-v*dt+L, -dt*i+Q, dt, Fm-Fe}, {qe, -d*h*L+V, -dt*i+Q, dt}, {qe, -d*h*L+V, -dt*i+Q, Fm-Fe}, {qe, -d*h*L+V, dt, Fm-Fe}, {qe, -dt*i+Q, dt, Fm-Fe}, {-d*h*L+V, -dt*i+Q, dt, Fm-Fe}, {-E*h+UH}, {-v*dt+L}, {i}, {-d*h*L+V}, {N}, {-dt*i+Q}, {Fm-Fe}, {-E*h+UH, -v*dt+L}, {-E*h+UH, i}, {-E*h+UH, -d*h*L+V}, {-E*h+UH, N}, {-E*h+UH, -dt*i+Q}, {-E*h+UH, Fm-Fe}, {-v*dt+L, i}, {-v*dt+L, -d*h*L+V}, {-v*dt+L, N}, {-v*dt+L, -dt*i+Q}, {-v*dt+L, Fm-Fe}, {i, -d*h*L+V}, {i, N}, {i, -dt*i+Q}, {i, Fm-Fe}, {-d*h*L+V, N}, {-d*h*L+V, -dt*i+Q}, {-d*h*L+V, Fm-Fe}, {N, -dt*i+Q}, {N, Fm-Fe}, {-dt*i+Q, Fm-Fe}, {-E*h+UH, -v*dt+L, i}, {-E*h+UH, -v*dt+L, -d*h*L+V}, {-E*h+UH, -v*dt+L, N}, {-E*h+UH, -v*dt+L, -dt*i+Q}, {-E*h+UH, -v*dt+L, Fm-Fe}, {-E*h+UH, i, -d*h*L+V}, {-E*h+UH, i, N}, {-E*h+UH, i, -dt*i+Q}, {-E*h+UH, i, Fm-Fe}, {-E*h+UH, -d*h*L+V, N}, {-E*h+UH, -d*h*L+V, -dt*i+Q}, {-E*h+UH, -d*h*L+V, Fm-Fe}, {-E*h+UH, N, -dt*i+Q}, {-E*h+UH, N, Fm-Fe}, {-E*h+UH, -dt*i+Q, Fm-Fe}, {-v*dt+L, i, -d*h*L+V}, {-v*dt+L, i, N}, {-v*dt+L, i, -dt*i+Q}, {-v*dt+L, i, Fm-Fe}, {-v*dt+L, -d*h*L+V, N}, {-v*dt+L, -d*h*L+V, -dt*i+Q}, {-v*dt+L, -d*h*L+V, Fm-Fe}, {-v*dt+L, N, -dt*i+Q}, {-v*dt+L, N, Fm-Fe}, {-v*dt+L, -dt*i+Q, Fm-Fe}, {i, -d*h*L+V, N}, {i, -d*h*L+V, -dt*i+Q}, {i, -d*h*L+V, Fm-Fe}, {i, N, -dt*i+Q}, {i, N, Fm-Fe}, {i, -dt*i+Q, Fm-Fe}, {-d*h*L+V, N, -dt*i+Q}, {-d*h*L+V, N, Fm-Fe}, {-d*h*L+V, -dt*i+Q, Fm-Fe}, {N, -dt*i+Q, Fm-Fe}, {-E*h+UH, -v*dt+L, i, -d*h*L+V}, {-E*h+UH, -v*dt+L, i, N}, {-E*h+UH, -v*dt+L, i, -dt*i+Q}, {-E*h+UH, -v*dt+L, i, Fm-Fe}, {-E*h+UH, -v*dt+L, -d*h*L+V, N}, {-E*h+UH, -v*dt+L, -d*h*L+V, -dt*i+Q}, {-E*h+UH, -v*dt+L, -d*h*L+V, Fm-Fe}, {-E*h+UH, -v*dt+L, N, -dt*i+Q}, {-E*h+UH, -v*dt+L, N, Fm-Fe}, {-E*h+UH, -v*dt+L, -dt*i+Q, Fm-Fe}, {-E*h+UH, i, -d*h*L+V, N}, {-E*h+UH, i, -d*h*L+V, -dt*i+Q}, {-E*h+UH, i, -d*h*L+V, Fm-Fe}, {-E*h+UH, i, N, -dt*i+Q}, {-E*h+UH, i, N, Fm-Fe}, {-E*h+UH, i, -dt*i+Q, Fm-Fe}, {-E*h+UH, -d*h*L+V, N, -dt*i+Q}, {-E*h+UH, -d*h*L+V, N, Fm-Fe}, {-E*h+UH, -d*h*L+V, -dt*i+Q, Fm-Fe}, {-E*h+UH, N, -dt*i+Q, Fm-Fe}, {-v*dt+L, i, -d*h*L+V, N}, {-v*dt+L, i, -d*h*L+V, -dt*i+Q}, {-v*dt+L, i, -d*h*L+V, Fm-Fe}, {-v*dt+L, i, N, -dt*i+Q}, {-v*dt+L, i, N, Fm-Fe}, {-v*dt+L, i, -dt*i+Q, Fm-Fe}, {-v*dt+L, -d*h*L+V, N, -dt*i+Q}, {-v*dt+L, -d*h*L+V, N, Fm-Fe}, {-v*dt+L, -d*h*L+V, -dt*i+Q, Fm-Fe}, {-v*dt+L, N, -dt*i+Q, Fm-Fe}, {i, -d*h*L+V, N, -dt*i+Q}, {i, -d*h*L+V, N, Fm-Fe}, {i, -d*h*L+V, -dt*i+Q, Fm-Fe}, {i, N, -dt*i+Q, Fm-Fe}, {-d*h*L+V, N, -dt*i+Q, Fm-Fe}, {-E*h+UH}, {-v*dt+L}, {-d*h*L+V}, {N}, {-dt*i+Q}, {dt}, {Fm-Fe}, {-E*h+UH, -v*dt+L}, {-E*h+UH, -d*h*L+V}, {-E*h+UH, N}, {-E*h+UH, -dt*i+Q}, {-E*h+UH, dt}, {-E*h+UH, Fm-Fe}, {-v*dt+L, -d*h*L+V}, {-v*dt+L, N}, {-v*dt+L, -dt*i+Q}, {-v*dt+L, dt}, {-v*dt+L, Fm-Fe}, {-d*h*L+V, N}, {-d*h*L+V, -dt*i+Q}, {-d*h*L+V, dt}, {-d*h*L+V, Fm-Fe}, {N, -dt*i+Q}, {N, dt}, {N, Fm-Fe}, {-dt*i+Q, dt}, {-dt*i+Q, Fm-Fe}, {dt, Fm-Fe}, {-E*h+UH, -v*dt+L, -d*h*L+V}, {-E*h+UH, -v*dt+L, N}, {-E*h+UH, -v*dt+L, -dt*i+Q}, {-E*h+UH, -v*dt+L, dt}, {-E*h+UH, -v*dt+L, Fm-Fe}, {-E*h+UH, -d*h*L+V, N}, {-E*h+UH, -d*h*L+V, -dt*i+Q}, {-E*h+UH, -d*h*L+V, dt}, {-E*h+UH, -d*h*L+V, Fm-Fe}, {-E*h+UH, N, -dt*i+Q}, {-E*h+UH, N, dt}, {-E*h+UH, N, Fm-Fe}, {-E*h+UH, -dt*i+Q, dt}, {-E*h+UH, -dt*i+Q, Fm-Fe}, {-E*h+UH, dt, Fm-Fe}, {-v*dt+L, -d*h*L+V, N}, {-v*dt+L, -d*h*L+V, -dt*i+Q}, {-v*dt+L, -d*h*L+V, dt}, {-v*dt+L, -d*h*L+V, Fm-Fe}, {-v*dt+L, N, -dt*i+Q}, {-v*dt+L, N, dt}, {-v*dt+L, N, Fm-Fe}, {-v*dt+L, -dt*i+Q, dt}, {-v*dt+L, -dt*i+Q, Fm-Fe}, {-v*dt+L, dt, Fm-Fe}, {-d*h*L+V, N, -dt*i+Q}, {-d*h*L+V, N, dt}, {-d*h*L+V, N, Fm-Fe}, {-d*h*L+V, -dt*i+Q, dt}, {-d*h*L+V, -dt*i+Q, Fm-Fe}, {-d*h*L+V, dt, Fm-Fe}, {N, -dt*i+Q, dt}, {N, -dt*i+Q, Fm-Fe}, {N, dt, Fm-Fe}, {-dt*i+Q, dt, Fm-Fe}, {-E*h+UH, -v*dt+L, -d*h*L+V, N}, {-E*h+UH, -v*dt+L, -d*h*L+V, -dt*i+Q}, {-E*h+UH, -v*dt+L, -d*h*L+V, dt}, {-E*h+UH, -v*dt+L, -d*h*L+V, Fm-Fe}, {-E*h+UH, -v*dt+L, N, -dt*i+Q}, {-E*h+UH, -v*dt+L, N, dt}, {-E*h+UH, -v*dt+L, N, Fm-Fe}, {-E*h+UH, -v*dt+L, -dt*i+Q, dt}, {-E*h+UH, -v*dt+L, -dt*i+Q, Fm-Fe}, {-E*h+UH, -v*dt+L, dt, Fm-Fe}, {-E*h+UH, -d*h*L+V, N, -dt*i+Q}, {-E*h+UH, -d*h*L+V, N, dt}, {-E*h+UH, -d*h*L+V, N, Fm-Fe}, {-E*h+UH, -d*h*L+V, -dt*i+Q, dt}, {-E*h+UH, -d*h*L+V, -dt*i+Q, Fm-Fe}, {-E*h+UH, -d*h*L+V, dt, Fm-Fe}, {-E*h+UH, N, -dt*i+Q, dt}, {-E*h+UH, N, -dt*i+Q, Fm-Fe}, {-E*h+UH, N, dt, Fm-Fe}, {-E*h+UH, -dt*i+Q, dt, Fm-Fe}, {-v*dt+L, -d*h*L+V, N, -dt*i+Q}, {-v*dt+L, -d*h*L+V, N, dt}, {-v*dt+L, -d*h*L+V, N, Fm-Fe}, {-v*dt+L, -d*h*L+V, -dt*i+Q, dt}, {-v*dt+L, -d*h*L+V, -dt*i+Q, Fm-Fe}, {-v*dt+L, -d*h*L+V, dt, Fm-Fe}, {-v*dt+L, N, -dt*i+Q, dt}, {-v*dt+L, N, -dt*i+Q, Fm-Fe}, {-v*dt+L, N, dt, Fm-Fe}, {-v*dt+L, -dt*i+Q, dt, Fm-Fe}, {-d*h*L+V, N, -dt*i+Q, dt}, {-d*h*L+V, N, -dt*i+Q, Fm-Fe}, {-d*h*L+V, N, dt, Fm-Fe}, {-d*h*L+V, -dt*i+Q, dt, Fm-Fe}, {N, -dt*i+Q, dt, Fm-Fe}};

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
f = openOut "results/hall/abduction/noiseless/3_axiom(s)_removed/combo_1_2_8/reasoning/reasoning_output.txt";
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

print("Reasoning complete. Output written to results/hall/abduction/noiseless/3_axiom(s)_removed/combo_1_2_8/reasoning/reasoning_output.txt");
