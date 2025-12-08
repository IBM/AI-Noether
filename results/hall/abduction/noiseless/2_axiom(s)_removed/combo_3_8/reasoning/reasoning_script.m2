-- AI-Noether: Reasoning Template (Noiseless)
-- Tests if candidate axiom sets, when added to remaining axioms, prove targets

needsPackage("PrimaryDecomposition", Reload => true)

-- Ring definition
R = QQ[Fm, d, v, Fe, E, dt, Q, N, V, i, n, qe, B, h, L, UH, MonomialOrder => Lex];

-- Input data
remainingAxioms = toList([Fm - qe*v*B, Fe - qe*E, E*h - UH, v*dt - L, i*dt - Q, Q - N*qe, V - L*h*d]);
qList = toList([N*qe*UH - i*B*h*L]);
k = #qList;

-- Per-target variable partitions
measuredPerTarget = {{UH, h, L, i, B, N, qe}};
nonMeasuredPerTarget = {{Fm, d, v, Fe, E, dt, Q, V, n}};

-- Candidate axiom sets to test (list of lists)
candidateSets = {{}, {dt*i-N*qe}, {-E*h+UH}, {-v*dt+L}, {h}, {-d*h*L+V}, {-dt*i+Q}, {-E*qe+Fe}, {-v*qe*B+Fm}, {dt*i-N*qe, -E*h+UH}, {dt*i-N*qe, -v*dt+L}, {dt*i-N*qe, h}, {dt*i-N*qe, -d*h*L+V}, {dt*i-N*qe, -dt*i+Q}, {dt*i-N*qe, -E*qe+Fe}, {dt*i-N*qe, -v*qe*B+Fm}, {-E*h+UH, -v*dt+L}, {-E*h+UH, h}, {-E*h+UH, -d*h*L+V}, {-E*h+UH, -dt*i+Q}, {-E*h+UH, -E*qe+Fe}, {-E*h+UH, -v*qe*B+Fm}, {-v*dt+L, h}, {-v*dt+L, -d*h*L+V}, {-v*dt+L, -dt*i+Q}, {-v*dt+L, -E*qe+Fe}, {-v*dt+L, -v*qe*B+Fm}, {h, -d*h*L+V}, {h, -dt*i+Q}, {h, -E*qe+Fe}, {h, -v*qe*B+Fm}, {-d*h*L+V, -dt*i+Q}, {-d*h*L+V, -E*qe+Fe}, {-d*h*L+V, -v*qe*B+Fm}, {-dt*i+Q, -E*qe+Fe}, {-dt*i+Q, -v*qe*B+Fm}, {-E*qe+Fe, -v*qe*B+Fm}, {dt*i-N*qe, -E*h+UH, -v*dt+L}, {dt*i-N*qe, -E*h+UH, h}, {dt*i-N*qe, -E*h+UH, -d*h*L+V}, {dt*i-N*qe, -E*h+UH, -dt*i+Q}, {dt*i-N*qe, -E*h+UH, -E*qe+Fe}, {dt*i-N*qe, -E*h+UH, -v*qe*B+Fm}, {dt*i-N*qe, -v*dt+L, h}, {dt*i-N*qe, -v*dt+L, -d*h*L+V}, {dt*i-N*qe, -v*dt+L, -dt*i+Q}, {dt*i-N*qe, -v*dt+L, -E*qe+Fe}, {dt*i-N*qe, -v*dt+L, -v*qe*B+Fm}, {dt*i-N*qe, h, -d*h*L+V}, {dt*i-N*qe, h, -dt*i+Q}, {dt*i-N*qe, h, -E*qe+Fe}, {dt*i-N*qe, h, -v*qe*B+Fm}, {dt*i-N*qe, -d*h*L+V, -dt*i+Q}, {dt*i-N*qe, -d*h*L+V, -E*qe+Fe}, {dt*i-N*qe, -d*h*L+V, -v*qe*B+Fm}, {dt*i-N*qe, -dt*i+Q, -E*qe+Fe}, {dt*i-N*qe, -dt*i+Q, -v*qe*B+Fm}, {dt*i-N*qe, -E*qe+Fe, -v*qe*B+Fm}, {-E*h+UH, -v*dt+L, h}, {-E*h+UH, -v*dt+L, -d*h*L+V}, {-E*h+UH, -v*dt+L, -dt*i+Q}, {-E*h+UH, -v*dt+L, -E*qe+Fe}, {-E*h+UH, -v*dt+L, -v*qe*B+Fm}, {-E*h+UH, h, -d*h*L+V}, {-E*h+UH, h, -dt*i+Q}, {-E*h+UH, h, -E*qe+Fe}, {-E*h+UH, h, -v*qe*B+Fm}, {-E*h+UH, -d*h*L+V, -dt*i+Q}, {-E*h+UH, -d*h*L+V, -E*qe+Fe}, {-E*h+UH, -d*h*L+V, -v*qe*B+Fm}, {-E*h+UH, -dt*i+Q, -E*qe+Fe}, {-E*h+UH, -dt*i+Q, -v*qe*B+Fm}, {-E*h+UH, -E*qe+Fe, -v*qe*B+Fm}, {-v*dt+L, h, -d*h*L+V}, {-v*dt+L, h, -dt*i+Q}, {-v*dt+L, h, -E*qe+Fe}, {-v*dt+L, h, -v*qe*B+Fm}, {-v*dt+L, -d*h*L+V, -dt*i+Q}, {-v*dt+L, -d*h*L+V, -E*qe+Fe}, {-v*dt+L, -d*h*L+V, -v*qe*B+Fm}, {-v*dt+L, -dt*i+Q, -E*qe+Fe}, {-v*dt+L, -dt*i+Q, -v*qe*B+Fm}, {-v*dt+L, -E*qe+Fe, -v*qe*B+Fm}, {h, -d*h*L+V, -dt*i+Q}, {h, -d*h*L+V, -E*qe+Fe}, {h, -d*h*L+V, -v*qe*B+Fm}, {h, -dt*i+Q, -E*qe+Fe}, {h, -dt*i+Q, -v*qe*B+Fm}, {h, -E*qe+Fe, -v*qe*B+Fm}, {-d*h*L+V, -dt*i+Q, -E*qe+Fe}, {-d*h*L+V, -dt*i+Q, -v*qe*B+Fm}, {-d*h*L+V, -E*qe+Fe, -v*qe*B+Fm}, {-dt*i+Q, -E*qe+Fe, -v*qe*B+Fm}, {dt*i-N*qe}, {v*B-E}, {-E*h+UH}, {-v*dt+L}, {-d*h*L+V}, {-dt*i+Q}, {-E*qe+Fe}, {-v*qe*B+Fm}, {dt*i-N*qe, v*B-E}, {dt*i-N*qe, -E*h+UH}, {dt*i-N*qe, -v*dt+L}, {dt*i-N*qe, -d*h*L+V}, {dt*i-N*qe, -dt*i+Q}, {dt*i-N*qe, -E*qe+Fe}, {dt*i-N*qe, -v*qe*B+Fm}, {v*B-E, -E*h+UH}, {v*B-E, -v*dt+L}, {v*B-E, -d*h*L+V}, {v*B-E, -dt*i+Q}, {v*B-E, -E*qe+Fe}, {v*B-E, -v*qe*B+Fm}, {-E*h+UH, -v*dt+L}, {-E*h+UH, -d*h*L+V}, {-E*h+UH, -dt*i+Q}, {-E*h+UH, -E*qe+Fe}, {-E*h+UH, -v*qe*B+Fm}, {-v*dt+L, -d*h*L+V}, {-v*dt+L, -dt*i+Q}, {-v*dt+L, -E*qe+Fe}, {-v*dt+L, -v*qe*B+Fm}, {-d*h*L+V, -dt*i+Q}, {-d*h*L+V, -E*qe+Fe}, {-d*h*L+V, -v*qe*B+Fm}, {-dt*i+Q, -E*qe+Fe}, {-dt*i+Q, -v*qe*B+Fm}, {-E*qe+Fe, -v*qe*B+Fm}, {dt*i-N*qe, v*B-E, -E*h+UH}, {dt*i-N*qe, v*B-E, -v*dt+L}, {dt*i-N*qe, v*B-E, -d*h*L+V}, {dt*i-N*qe, v*B-E, -dt*i+Q}, {dt*i-N*qe, v*B-E, -E*qe+Fe}, {dt*i-N*qe, v*B-E, -v*qe*B+Fm}, {dt*i-N*qe, -E*h+UH, -v*dt+L}, {dt*i-N*qe, -E*h+UH, -d*h*L+V}, {dt*i-N*qe, -E*h+UH, -dt*i+Q}, {dt*i-N*qe, -E*h+UH, -E*qe+Fe}, {dt*i-N*qe, -E*h+UH, -v*qe*B+Fm}, {dt*i-N*qe, -v*dt+L, -d*h*L+V}, {dt*i-N*qe, -v*dt+L, -dt*i+Q}, {dt*i-N*qe, -v*dt+L, -E*qe+Fe}, {dt*i-N*qe, -v*dt+L, -v*qe*B+Fm}, {dt*i-N*qe, -d*h*L+V, -dt*i+Q}, {dt*i-N*qe, -d*h*L+V, -E*qe+Fe}, {dt*i-N*qe, -d*h*L+V, -v*qe*B+Fm}, {dt*i-N*qe, -dt*i+Q, -E*qe+Fe}, {dt*i-N*qe, -dt*i+Q, -v*qe*B+Fm}, {dt*i-N*qe, -E*qe+Fe, -v*qe*B+Fm}, {v*B-E, -E*h+UH, -v*dt+L}, {v*B-E, -E*h+UH, -d*h*L+V}, {v*B-E, -E*h+UH, -dt*i+Q}, {v*B-E, -E*h+UH, -E*qe+Fe}, {v*B-E, -E*h+UH, -v*qe*B+Fm}, {v*B-E, -v*dt+L, -d*h*L+V}, {v*B-E, -v*dt+L, -dt*i+Q}, {v*B-E, -v*dt+L, -E*qe+Fe}, {v*B-E, -v*dt+L, -v*qe*B+Fm}, {v*B-E, -d*h*L+V, -dt*i+Q}, {v*B-E, -d*h*L+V, -E*qe+Fe}, {v*B-E, -d*h*L+V, -v*qe*B+Fm}, {v*B-E, -dt*i+Q, -E*qe+Fe}, {v*B-E, -dt*i+Q, -v*qe*B+Fm}, {v*B-E, -E*qe+Fe, -v*qe*B+Fm}, {-E*h+UH, -v*dt+L, -d*h*L+V}, {-E*h+UH, -v*dt+L, -dt*i+Q}, {-E*h+UH, -v*dt+L, -E*qe+Fe}, {-E*h+UH, -v*dt+L, -v*qe*B+Fm}, {-E*h+UH, -d*h*L+V, -dt*i+Q}, {-E*h+UH, -d*h*L+V, -E*qe+Fe}, {-E*h+UH, -d*h*L+V, -v*qe*B+Fm}, {-E*h+UH, -dt*i+Q, -E*qe+Fe}, {-E*h+UH, -dt*i+Q, -v*qe*B+Fm}, {-E*h+UH, -E*qe+Fe, -v*qe*B+Fm}, {-v*dt+L, -d*h*L+V, -dt*i+Q}, {-v*dt+L, -d*h*L+V, -E*qe+Fe}, {-v*dt+L, -d*h*L+V, -v*qe*B+Fm}, {-v*dt+L, -dt*i+Q, -E*qe+Fe}, {-v*dt+L, -dt*i+Q, -v*qe*B+Fm}, {-v*dt+L, -E*qe+Fe, -v*qe*B+Fm}, {-d*h*L+V, -dt*i+Q, -E*qe+Fe}, {-d*h*L+V, -dt*i+Q, -v*qe*B+Fm}, {-d*h*L+V, -E*qe+Fe, -v*qe*B+Fm}, {-dt*i+Q, -E*qe+Fe, -v*qe*B+Fm}, {-E*h+UH}, {-v*dt+L}, {qe}, {i}, {-d*h*L+V}, {-dt*i+Q}, {-E*qe+Fe}, {-v*qe*B+Fm}, {-E*h+UH, -v*dt+L}, {-E*h+UH, qe}, {-E*h+UH, i}, {-E*h+UH, -d*h*L+V}, {-E*h+UH, -dt*i+Q}, {-E*h+UH, -E*qe+Fe}, {-E*h+UH, -v*qe*B+Fm}, {-v*dt+L, qe}, {-v*dt+L, i}, {-v*dt+L, -d*h*L+V}, {-v*dt+L, -dt*i+Q}, {-v*dt+L, -E*qe+Fe}, {-v*dt+L, -v*qe*B+Fm}, {qe, i}, {qe, -d*h*L+V}, {qe, -dt*i+Q}, {qe, -E*qe+Fe}, {qe, -v*qe*B+Fm}, {i, -d*h*L+V}, {i, -dt*i+Q}, {i, -E*qe+Fe}, {i, -v*qe*B+Fm}, {-d*h*L+V, -dt*i+Q}, {-d*h*L+V, -E*qe+Fe}, {-d*h*L+V, -v*qe*B+Fm}, {-dt*i+Q, -E*qe+Fe}, {-dt*i+Q, -v*qe*B+Fm}, {-E*qe+Fe, -v*qe*B+Fm}, {-E*h+UH, -v*dt+L, qe}, {-E*h+UH, -v*dt+L, i}, {-E*h+UH, -v*dt+L, -d*h*L+V}, {-E*h+UH, -v*dt+L, -dt*i+Q}, {-E*h+UH, -v*dt+L, -E*qe+Fe}, {-E*h+UH, -v*dt+L, -v*qe*B+Fm}, {-E*h+UH, qe, i}, {-E*h+UH, qe, -d*h*L+V}, {-E*h+UH, qe, -dt*i+Q}, {-E*h+UH, qe, -E*qe+Fe}, {-E*h+UH, qe, -v*qe*B+Fm}, {-E*h+UH, i, -d*h*L+V}, {-E*h+UH, i, -dt*i+Q}, {-E*h+UH, i, -E*qe+Fe}, {-E*h+UH, i, -v*qe*B+Fm}, {-E*h+UH, -d*h*L+V, -dt*i+Q}, {-E*h+UH, -d*h*L+V, -E*qe+Fe}, {-E*h+UH, -d*h*L+V, -v*qe*B+Fm}, {-E*h+UH, -dt*i+Q, -E*qe+Fe}, {-E*h+UH, -dt*i+Q, -v*qe*B+Fm}, {-E*h+UH, -E*qe+Fe, -v*qe*B+Fm}, {-v*dt+L, qe, i}, {-v*dt+L, qe, -d*h*L+V}, {-v*dt+L, qe, -dt*i+Q}, {-v*dt+L, qe, -E*qe+Fe}, {-v*dt+L, qe, -v*qe*B+Fm}, {-v*dt+L, i, -d*h*L+V}, {-v*dt+L, i, -dt*i+Q}, {-v*dt+L, i, -E*qe+Fe}, {-v*dt+L, i, -v*qe*B+Fm}, {-v*dt+L, -d*h*L+V, -dt*i+Q}, {-v*dt+L, -d*h*L+V, -E*qe+Fe}, {-v*dt+L, -d*h*L+V, -v*qe*B+Fm}, {-v*dt+L, -dt*i+Q, -E*qe+Fe}, {-v*dt+L, -dt*i+Q, -v*qe*B+Fm}, {-v*dt+L, -E*qe+Fe, -v*qe*B+Fm}, {qe, i, -d*h*L+V}, {qe, i, -dt*i+Q}, {qe, i, -E*qe+Fe}, {qe, i, -v*qe*B+Fm}, {qe, -d*h*L+V, -dt*i+Q}, {qe, -d*h*L+V, -E*qe+Fe}, {qe, -d*h*L+V, -v*qe*B+Fm}, {qe, -dt*i+Q, -E*qe+Fe}, {qe, -dt*i+Q, -v*qe*B+Fm}, {qe, -E*qe+Fe, -v*qe*B+Fm}, {i, -d*h*L+V, -dt*i+Q}, {i, -d*h*L+V, -E*qe+Fe}, {i, -d*h*L+V, -v*qe*B+Fm}, {i, -dt*i+Q, -E*qe+Fe}, {i, -dt*i+Q, -v*qe*B+Fm}, {i, -E*qe+Fe, -v*qe*B+Fm}, {-d*h*L+V, -dt*i+Q, -E*qe+Fe}, {-d*h*L+V, -dt*i+Q, -v*qe*B+Fm}, {-d*h*L+V, -E*qe+Fe, -v*qe*B+Fm}, {-dt*i+Q, -E*qe+Fe, -v*qe*B+Fm}, {-E*h+UH}, {-v*dt+L}, {qe}, {-d*h*L+V}, {-dt*i+Q}, {dt}, {-E*qe+Fe}, {-v*qe*B+Fm}, {-E*h+UH, -v*dt+L}, {-E*h+UH, qe}, {-E*h+UH, -d*h*L+V}, {-E*h+UH, -dt*i+Q}, {-E*h+UH, dt}, {-E*h+UH, -E*qe+Fe}, {-E*h+UH, -v*qe*B+Fm}, {-v*dt+L, qe}, {-v*dt+L, -d*h*L+V}, {-v*dt+L, -dt*i+Q}, {-v*dt+L, dt}, {-v*dt+L, -E*qe+Fe}, {-v*dt+L, -v*qe*B+Fm}, {qe, -d*h*L+V}, {qe, -dt*i+Q}, {qe, dt}, {qe, -E*qe+Fe}, {qe, -v*qe*B+Fm}, {-d*h*L+V, -dt*i+Q}, {-d*h*L+V, dt}, {-d*h*L+V, -E*qe+Fe}, {-d*h*L+V, -v*qe*B+Fm}, {-dt*i+Q, dt}, {-dt*i+Q, -E*qe+Fe}, {-dt*i+Q, -v*qe*B+Fm}, {dt, -E*qe+Fe}, {dt, -v*qe*B+Fm}, {-E*qe+Fe, -v*qe*B+Fm}, {-E*h+UH, -v*dt+L, qe}, {-E*h+UH, -v*dt+L, -d*h*L+V}, {-E*h+UH, -v*dt+L, -dt*i+Q}, {-E*h+UH, -v*dt+L, dt}, {-E*h+UH, -v*dt+L, -E*qe+Fe}, {-E*h+UH, -v*dt+L, -v*qe*B+Fm}, {-E*h+UH, qe, -d*h*L+V}, {-E*h+UH, qe, -dt*i+Q}, {-E*h+UH, qe, dt}, {-E*h+UH, qe, -E*qe+Fe}, {-E*h+UH, qe, -v*qe*B+Fm}, {-E*h+UH, -d*h*L+V, -dt*i+Q}, {-E*h+UH, -d*h*L+V, dt}, {-E*h+UH, -d*h*L+V, -E*qe+Fe}, {-E*h+UH, -d*h*L+V, -v*qe*B+Fm}, {-E*h+UH, -dt*i+Q, dt}, {-E*h+UH, -dt*i+Q, -E*qe+Fe}, {-E*h+UH, -dt*i+Q, -v*qe*B+Fm}, {-E*h+UH, dt, -E*qe+Fe}, {-E*h+UH, dt, -v*qe*B+Fm}, {-E*h+UH, -E*qe+Fe, -v*qe*B+Fm}, {-v*dt+L, qe, -d*h*L+V}, {-v*dt+L, qe, -dt*i+Q}, {-v*dt+L, qe, dt}, {-v*dt+L, qe, -E*qe+Fe}, {-v*dt+L, qe, -v*qe*B+Fm}, {-v*dt+L, -d*h*L+V, -dt*i+Q}, {-v*dt+L, -d*h*L+V, dt}, {-v*dt+L, -d*h*L+V, -E*qe+Fe}, {-v*dt+L, -d*h*L+V, -v*qe*B+Fm}, {-v*dt+L, -dt*i+Q, dt}, {-v*dt+L, -dt*i+Q, -E*qe+Fe}, {-v*dt+L, -dt*i+Q, -v*qe*B+Fm}, {-v*dt+L, dt, -E*qe+Fe}, {-v*dt+L, dt, -v*qe*B+Fm}, {-v*dt+L, -E*qe+Fe, -v*qe*B+Fm}, {qe, -d*h*L+V, -dt*i+Q}, {qe, -d*h*L+V, dt}, {qe, -d*h*L+V, -E*qe+Fe}, {qe, -d*h*L+V, -v*qe*B+Fm}, {qe, -dt*i+Q, dt}, {qe, -dt*i+Q, -E*qe+Fe}, {qe, -dt*i+Q, -v*qe*B+Fm}, {qe, dt, -E*qe+Fe}, {qe, dt, -v*qe*B+Fm}, {qe, -E*qe+Fe, -v*qe*B+Fm}, {-d*h*L+V, -dt*i+Q, dt}, {-d*h*L+V, -dt*i+Q, -E*qe+Fe}, {-d*h*L+V, -dt*i+Q, -v*qe*B+Fm}, {-d*h*L+V, dt, -E*qe+Fe}, {-d*h*L+V, dt, -v*qe*B+Fm}, {-d*h*L+V, -E*qe+Fe, -v*qe*B+Fm}, {-dt*i+Q, dt, -E*qe+Fe}, {-dt*i+Q, dt, -v*qe*B+Fm}, {-dt*i+Q, -E*qe+Fe, -v*qe*B+Fm}, {dt, -E*qe+Fe, -v*qe*B+Fm}, {-E*h+UH}, {-v*dt+L}, {i}, {-d*h*L+V}, {N}, {-dt*i+Q}, {-E*qe+Fe}, {-v*qe*B+Fm}, {-E*h+UH, -v*dt+L}, {-E*h+UH, i}, {-E*h+UH, -d*h*L+V}, {-E*h+UH, N}, {-E*h+UH, -dt*i+Q}, {-E*h+UH, -E*qe+Fe}, {-E*h+UH, -v*qe*B+Fm}, {-v*dt+L, i}, {-v*dt+L, -d*h*L+V}, {-v*dt+L, N}, {-v*dt+L, -dt*i+Q}, {-v*dt+L, -E*qe+Fe}, {-v*dt+L, -v*qe*B+Fm}, {i, -d*h*L+V}, {i, N}, {i, -dt*i+Q}, {i, -E*qe+Fe}, {i, -v*qe*B+Fm}, {-d*h*L+V, N}, {-d*h*L+V, -dt*i+Q}, {-d*h*L+V, -E*qe+Fe}, {-d*h*L+V, -v*qe*B+Fm}, {N, -dt*i+Q}, {N, -E*qe+Fe}, {N, -v*qe*B+Fm}, {-dt*i+Q, -E*qe+Fe}, {-dt*i+Q, -v*qe*B+Fm}, {-E*qe+Fe, -v*qe*B+Fm}, {-E*h+UH, -v*dt+L, i}, {-E*h+UH, -v*dt+L, -d*h*L+V}, {-E*h+UH, -v*dt+L, N}, {-E*h+UH, -v*dt+L, -dt*i+Q}, {-E*h+UH, -v*dt+L, -E*qe+Fe}, {-E*h+UH, -v*dt+L, -v*qe*B+Fm}, {-E*h+UH, i, -d*h*L+V}, {-E*h+UH, i, N}, {-E*h+UH, i, -dt*i+Q}, {-E*h+UH, i, -E*qe+Fe}, {-E*h+UH, i, -v*qe*B+Fm}, {-E*h+UH, -d*h*L+V, N}, {-E*h+UH, -d*h*L+V, -dt*i+Q}, {-E*h+UH, -d*h*L+V, -E*qe+Fe}, {-E*h+UH, -d*h*L+V, -v*qe*B+Fm}, {-E*h+UH, N, -dt*i+Q}, {-E*h+UH, N, -E*qe+Fe}, {-E*h+UH, N, -v*qe*B+Fm}, {-E*h+UH, -dt*i+Q, -E*qe+Fe}, {-E*h+UH, -dt*i+Q, -v*qe*B+Fm}, {-E*h+UH, -E*qe+Fe, -v*qe*B+Fm}, {-v*dt+L, i, -d*h*L+V}, {-v*dt+L, i, N}, {-v*dt+L, i, -dt*i+Q}, {-v*dt+L, i, -E*qe+Fe}, {-v*dt+L, i, -v*qe*B+Fm}, {-v*dt+L, -d*h*L+V, N}, {-v*dt+L, -d*h*L+V, -dt*i+Q}, {-v*dt+L, -d*h*L+V, -E*qe+Fe}, {-v*dt+L, -d*h*L+V, -v*qe*B+Fm}, {-v*dt+L, N, -dt*i+Q}, {-v*dt+L, N, -E*qe+Fe}, {-v*dt+L, N, -v*qe*B+Fm}, {-v*dt+L, -dt*i+Q, -E*qe+Fe}, {-v*dt+L, -dt*i+Q, -v*qe*B+Fm}, {-v*dt+L, -E*qe+Fe, -v*qe*B+Fm}, {i, -d*h*L+V, N}, {i, -d*h*L+V, -dt*i+Q}, {i, -d*h*L+V, -E*qe+Fe}, {i, -d*h*L+V, -v*qe*B+Fm}, {i, N, -dt*i+Q}, {i, N, -E*qe+Fe}, {i, N, -v*qe*B+Fm}, {i, -dt*i+Q, -E*qe+Fe}, {i, -dt*i+Q, -v*qe*B+Fm}, {i, -E*qe+Fe, -v*qe*B+Fm}, {-d*h*L+V, N, -dt*i+Q}, {-d*h*L+V, N, -E*qe+Fe}, {-d*h*L+V, N, -v*qe*B+Fm}, {-d*h*L+V, -dt*i+Q, -E*qe+Fe}, {-d*h*L+V, -dt*i+Q, -v*qe*B+Fm}, {-d*h*L+V, -E*qe+Fe, -v*qe*B+Fm}, {N, -dt*i+Q, -E*qe+Fe}, {N, -dt*i+Q, -v*qe*B+Fm}, {N, -E*qe+Fe, -v*qe*B+Fm}, {-dt*i+Q, -E*qe+Fe, -v*qe*B+Fm}, {-E*h+UH}, {-v*dt+L}, {-d*h*L+V}, {N}, {-dt*i+Q}, {dt}, {-E*qe+Fe}, {-v*qe*B+Fm}, {-E*h+UH, -v*dt+L}, {-E*h+UH, -d*h*L+V}, {-E*h+UH, N}, {-E*h+UH, -dt*i+Q}, {-E*h+UH, dt}, {-E*h+UH, -E*qe+Fe}, {-E*h+UH, -v*qe*B+Fm}, {-v*dt+L, -d*h*L+V}, {-v*dt+L, N}, {-v*dt+L, -dt*i+Q}, {-v*dt+L, dt}, {-v*dt+L, -E*qe+Fe}, {-v*dt+L, -v*qe*B+Fm}, {-d*h*L+V, N}, {-d*h*L+V, -dt*i+Q}, {-d*h*L+V, dt}, {-d*h*L+V, -E*qe+Fe}, {-d*h*L+V, -v*qe*B+Fm}, {N, -dt*i+Q}, {N, dt}, {N, -E*qe+Fe}, {N, -v*qe*B+Fm}, {-dt*i+Q, dt}, {-dt*i+Q, -E*qe+Fe}, {-dt*i+Q, -v*qe*B+Fm}, {dt, -E*qe+Fe}, {dt, -v*qe*B+Fm}, {-E*qe+Fe, -v*qe*B+Fm}, {-E*h+UH, -v*dt+L, -d*h*L+V}, {-E*h+UH, -v*dt+L, N}, {-E*h+UH, -v*dt+L, -dt*i+Q}, {-E*h+UH, -v*dt+L, dt}, {-E*h+UH, -v*dt+L, -E*qe+Fe}, {-E*h+UH, -v*dt+L, -v*qe*B+Fm}, {-E*h+UH, -d*h*L+V, N}, {-E*h+UH, -d*h*L+V, -dt*i+Q}, {-E*h+UH, -d*h*L+V, dt}, {-E*h+UH, -d*h*L+V, -E*qe+Fe}, {-E*h+UH, -d*h*L+V, -v*qe*B+Fm}, {-E*h+UH, N, -dt*i+Q}, {-E*h+UH, N, dt}, {-E*h+UH, N, -E*qe+Fe}, {-E*h+UH, N, -v*qe*B+Fm}, {-E*h+UH, -dt*i+Q, dt}, {-E*h+UH, -dt*i+Q, -E*qe+Fe}, {-E*h+UH, -dt*i+Q, -v*qe*B+Fm}, {-E*h+UH, dt, -E*qe+Fe}, {-E*h+UH, dt, -v*qe*B+Fm}, {-E*h+UH, -E*qe+Fe, -v*qe*B+Fm}, {-v*dt+L, -d*h*L+V, N}, {-v*dt+L, -d*h*L+V, -dt*i+Q}, {-v*dt+L, -d*h*L+V, dt}, {-v*dt+L, -d*h*L+V, -E*qe+Fe}, {-v*dt+L, -d*h*L+V, -v*qe*B+Fm}, {-v*dt+L, N, -dt*i+Q}, {-v*dt+L, N, dt}, {-v*dt+L, N, -E*qe+Fe}, {-v*dt+L, N, -v*qe*B+Fm}, {-v*dt+L, -dt*i+Q, dt}, {-v*dt+L, -dt*i+Q, -E*qe+Fe}, {-v*dt+L, -dt*i+Q, -v*qe*B+Fm}, {-v*dt+L, dt, -E*qe+Fe}, {-v*dt+L, dt, -v*qe*B+Fm}, {-v*dt+L, -E*qe+Fe, -v*qe*B+Fm}, {-d*h*L+V, N, -dt*i+Q}, {-d*h*L+V, N, dt}, {-d*h*L+V, N, -E*qe+Fe}, {-d*h*L+V, N, -v*qe*B+Fm}, {-d*h*L+V, -dt*i+Q, dt}, {-d*h*L+V, -dt*i+Q, -E*qe+Fe}, {-d*h*L+V, -dt*i+Q, -v*qe*B+Fm}, {-d*h*L+V, dt, -E*qe+Fe}, {-d*h*L+V, dt, -v*qe*B+Fm}, {-d*h*L+V, -E*qe+Fe, -v*qe*B+Fm}, {N, -dt*i+Q, dt}, {N, -dt*i+Q, -E*qe+Fe}, {N, -dt*i+Q, -v*qe*B+Fm}, {N, dt, -E*qe+Fe}, {N, dt, -v*qe*B+Fm}, {N, -E*qe+Fe, -v*qe*B+Fm}, {-dt*i+Q, dt, -E*qe+Fe}, {-dt*i+Q, dt, -v*qe*B+Fm}, {-dt*i+Q, -E*qe+Fe, -v*qe*B+Fm}, {dt, -E*qe+Fe, -v*qe*B+Fm}};

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
f = openOut "results/hall/abduction/noiseless/2_axiom(s)_removed/combo_3_8/reasoning/reasoning_output.txt";
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

print("Reasoning complete. Output written to results/hall/abduction/noiseless/2_axiom(s)_removed/combo_3_8/reasoning/reasoning_output.txt");
