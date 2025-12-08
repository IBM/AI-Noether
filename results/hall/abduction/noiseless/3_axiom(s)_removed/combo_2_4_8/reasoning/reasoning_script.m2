-- AI-Noether: Reasoning Template (Noiseless)
-- Tests if candidate axiom sets, when added to remaining axioms, prove targets

needsPackage("PrimaryDecomposition", Reload => true)

-- Ring definition
R = QQ[Fm, d, v, Fe, E, dt, Q, N, V, i, n, qe, B, h, L, UH, MonomialOrder => Lex];

-- Input data
remainingAxioms = toList([Fm - qe*v*B, Fm - Fe, v*dt - L, i*dt - Q, Q - N*qe, V - L*h*d]);
qList = toList([N*qe*UH - i*B*h*L]);
k = #qList;

-- Per-target variable partitions
measuredPerTarget = {{UH, h, L, i, B, N, qe}};
nonMeasuredPerTarget = {{Fm, d, v, Fe, E, dt, Q, V, n}};

-- Candidate axiom sets to test (list of lists)
candidateSets = {{}, {dt*i-N*qe}, {v*B*h-UH}, {-v*dt+L}, {-d*h*L+V}, {-dt*i+Q}, {-v*qe*B+Fe}, {-v*qe*B+Fm}, {dt*i-N*qe, v*B*h-UH}, {dt*i-N*qe, -v*dt+L}, {dt*i-N*qe, -d*h*L+V}, {dt*i-N*qe, -dt*i+Q}, {dt*i-N*qe, -v*qe*B+Fe}, {dt*i-N*qe, -v*qe*B+Fm}, {v*B*h-UH, -v*dt+L}, {v*B*h-UH, -d*h*L+V}, {v*B*h-UH, -dt*i+Q}, {v*B*h-UH, -v*qe*B+Fe}, {v*B*h-UH, -v*qe*B+Fm}, {-v*dt+L, -d*h*L+V}, {-v*dt+L, -dt*i+Q}, {-v*dt+L, -v*qe*B+Fe}, {-v*dt+L, -v*qe*B+Fm}, {-d*h*L+V, -dt*i+Q}, {-d*h*L+V, -v*qe*B+Fe}, {-d*h*L+V, -v*qe*B+Fm}, {-dt*i+Q, -v*qe*B+Fe}, {-dt*i+Q, -v*qe*B+Fm}, {-v*qe*B+Fe, -v*qe*B+Fm}, {dt*i-N*qe, v*B*h-UH, -v*dt+L}, {dt*i-N*qe, v*B*h-UH, -d*h*L+V}, {dt*i-N*qe, v*B*h-UH, -dt*i+Q}, {dt*i-N*qe, v*B*h-UH, -v*qe*B+Fe}, {dt*i-N*qe, v*B*h-UH, -v*qe*B+Fm}, {dt*i-N*qe, -v*dt+L, -d*h*L+V}, {dt*i-N*qe, -v*dt+L, -dt*i+Q}, {dt*i-N*qe, -v*dt+L, -v*qe*B+Fe}, {dt*i-N*qe, -v*dt+L, -v*qe*B+Fm}, {dt*i-N*qe, -d*h*L+V, -dt*i+Q}, {dt*i-N*qe, -d*h*L+V, -v*qe*B+Fe}, {dt*i-N*qe, -d*h*L+V, -v*qe*B+Fm}, {dt*i-N*qe, -dt*i+Q, -v*qe*B+Fe}, {dt*i-N*qe, -dt*i+Q, -v*qe*B+Fm}, {dt*i-N*qe, -v*qe*B+Fe, -v*qe*B+Fm}, {v*B*h-UH, -v*dt+L, -d*h*L+V}, {v*B*h-UH, -v*dt+L, -dt*i+Q}, {v*B*h-UH, -v*dt+L, -v*qe*B+Fe}, {v*B*h-UH, -v*dt+L, -v*qe*B+Fm}, {v*B*h-UH, -d*h*L+V, -dt*i+Q}, {v*B*h-UH, -d*h*L+V, -v*qe*B+Fe}, {v*B*h-UH, -d*h*L+V, -v*qe*B+Fm}, {v*B*h-UH, -dt*i+Q, -v*qe*B+Fe}, {v*B*h-UH, -dt*i+Q, -v*qe*B+Fm}, {v*B*h-UH, -v*qe*B+Fe, -v*qe*B+Fm}, {-v*dt+L, -d*h*L+V, -dt*i+Q}, {-v*dt+L, -d*h*L+V, -v*qe*B+Fe}, {-v*dt+L, -d*h*L+V, -v*qe*B+Fm}, {-v*dt+L, -dt*i+Q, -v*qe*B+Fe}, {-v*dt+L, -dt*i+Q, -v*qe*B+Fm}, {-v*dt+L, -v*qe*B+Fe, -v*qe*B+Fm}, {-d*h*L+V, -dt*i+Q, -v*qe*B+Fe}, {-d*h*L+V, -dt*i+Q, -v*qe*B+Fm}, {-d*h*L+V, -v*qe*B+Fe, -v*qe*B+Fm}, {-dt*i+Q, -v*qe*B+Fe, -v*qe*B+Fm}, {dt*i-N*qe, v*B*h-UH, -v*dt+L, -d*h*L+V}, {dt*i-N*qe, v*B*h-UH, -v*dt+L, -dt*i+Q}, {dt*i-N*qe, v*B*h-UH, -v*dt+L, -v*qe*B+Fe}, {dt*i-N*qe, v*B*h-UH, -v*dt+L, -v*qe*B+Fm}, {dt*i-N*qe, v*B*h-UH, -d*h*L+V, -dt*i+Q}, {dt*i-N*qe, v*B*h-UH, -d*h*L+V, -v*qe*B+Fe}, {dt*i-N*qe, v*B*h-UH, -d*h*L+V, -v*qe*B+Fm}, {dt*i-N*qe, v*B*h-UH, -dt*i+Q, -v*qe*B+Fe}, {dt*i-N*qe, v*B*h-UH, -dt*i+Q, -v*qe*B+Fm}, {dt*i-N*qe, v*B*h-UH, -v*qe*B+Fe, -v*qe*B+Fm}, {dt*i-N*qe, -v*dt+L, -d*h*L+V, -dt*i+Q}, {dt*i-N*qe, -v*dt+L, -d*h*L+V, -v*qe*B+Fe}, {dt*i-N*qe, -v*dt+L, -d*h*L+V, -v*qe*B+Fm}, {dt*i-N*qe, -v*dt+L, -dt*i+Q, -v*qe*B+Fe}, {dt*i-N*qe, -v*dt+L, -dt*i+Q, -v*qe*B+Fm}, {dt*i-N*qe, -v*dt+L, -v*qe*B+Fe, -v*qe*B+Fm}, {dt*i-N*qe, -d*h*L+V, -dt*i+Q, -v*qe*B+Fe}, {dt*i-N*qe, -d*h*L+V, -dt*i+Q, -v*qe*B+Fm}, {dt*i-N*qe, -d*h*L+V, -v*qe*B+Fe, -v*qe*B+Fm}, {dt*i-N*qe, -dt*i+Q, -v*qe*B+Fe, -v*qe*B+Fm}, {v*B*h-UH, -v*dt+L, -d*h*L+V, -dt*i+Q}, {v*B*h-UH, -v*dt+L, -d*h*L+V, -v*qe*B+Fe}, {v*B*h-UH, -v*dt+L, -d*h*L+V, -v*qe*B+Fm}, {v*B*h-UH, -v*dt+L, -dt*i+Q, -v*qe*B+Fe}, {v*B*h-UH, -v*dt+L, -dt*i+Q, -v*qe*B+Fm}, {v*B*h-UH, -v*dt+L, -v*qe*B+Fe, -v*qe*B+Fm}, {v*B*h-UH, -d*h*L+V, -dt*i+Q, -v*qe*B+Fe}, {v*B*h-UH, -d*h*L+V, -dt*i+Q, -v*qe*B+Fm}, {v*B*h-UH, -d*h*L+V, -v*qe*B+Fe, -v*qe*B+Fm}, {v*B*h-UH, -dt*i+Q, -v*qe*B+Fe, -v*qe*B+Fm}, {-v*dt+L, -d*h*L+V, -dt*i+Q, -v*qe*B+Fe}, {-v*dt+L, -d*h*L+V, -dt*i+Q, -v*qe*B+Fm}, {-v*dt+L, -d*h*L+V, -v*qe*B+Fe, -v*qe*B+Fm}, {-v*dt+L, -dt*i+Q, -v*qe*B+Fe, -v*qe*B+Fm}, {-d*h*L+V, -dt*i+Q, -v*qe*B+Fe, -v*qe*B+Fm}, {-v*dt+L}, {qe}, {i}, {-d*h*L+V}, {-dt*i+Q}, {-v*qe*B+Fe}, {-v*qe*B+Fm}, {-v*dt+L, qe}, {-v*dt+L, i}, {-v*dt+L, -d*h*L+V}, {-v*dt+L, -dt*i+Q}, {-v*dt+L, -v*qe*B+Fe}, {-v*dt+L, -v*qe*B+Fm}, {qe, i}, {qe, -d*h*L+V}, {qe, -dt*i+Q}, {qe, -v*qe*B+Fe}, {qe, -v*qe*B+Fm}, {i, -d*h*L+V}, {i, -dt*i+Q}, {i, -v*qe*B+Fe}, {i, -v*qe*B+Fm}, {-d*h*L+V, -dt*i+Q}, {-d*h*L+V, -v*qe*B+Fe}, {-d*h*L+V, -v*qe*B+Fm}, {-dt*i+Q, -v*qe*B+Fe}, {-dt*i+Q, -v*qe*B+Fm}, {-v*qe*B+Fe, -v*qe*B+Fm}, {-v*dt+L, qe, i}, {-v*dt+L, qe, -d*h*L+V}, {-v*dt+L, qe, -dt*i+Q}, {-v*dt+L, qe, -v*qe*B+Fe}, {-v*dt+L, qe, -v*qe*B+Fm}, {-v*dt+L, i, -d*h*L+V}, {-v*dt+L, i, -dt*i+Q}, {-v*dt+L, i, -v*qe*B+Fe}, {-v*dt+L, i, -v*qe*B+Fm}, {-v*dt+L, -d*h*L+V, -dt*i+Q}, {-v*dt+L, -d*h*L+V, -v*qe*B+Fe}, {-v*dt+L, -d*h*L+V, -v*qe*B+Fm}, {-v*dt+L, -dt*i+Q, -v*qe*B+Fe}, {-v*dt+L, -dt*i+Q, -v*qe*B+Fm}, {-v*dt+L, -v*qe*B+Fe, -v*qe*B+Fm}, {qe, i, -d*h*L+V}, {qe, i, -dt*i+Q}, {qe, i, -v*qe*B+Fe}, {qe, i, -v*qe*B+Fm}, {qe, -d*h*L+V, -dt*i+Q}, {qe, -d*h*L+V, -v*qe*B+Fe}, {qe, -d*h*L+V, -v*qe*B+Fm}, {qe, -dt*i+Q, -v*qe*B+Fe}, {qe, -dt*i+Q, -v*qe*B+Fm}, {qe, -v*qe*B+Fe, -v*qe*B+Fm}, {i, -d*h*L+V, -dt*i+Q}, {i, -d*h*L+V, -v*qe*B+Fe}, {i, -d*h*L+V, -v*qe*B+Fm}, {i, -dt*i+Q, -v*qe*B+Fe}, {i, -dt*i+Q, -v*qe*B+Fm}, {i, -v*qe*B+Fe, -v*qe*B+Fm}, {-d*h*L+V, -dt*i+Q, -v*qe*B+Fe}, {-d*h*L+V, -dt*i+Q, -v*qe*B+Fm}, {-d*h*L+V, -v*qe*B+Fe, -v*qe*B+Fm}, {-dt*i+Q, -v*qe*B+Fe, -v*qe*B+Fm}, {-v*dt+L, qe, i, -d*h*L+V}, {-v*dt+L, qe, i, -dt*i+Q}, {-v*dt+L, qe, i, -v*qe*B+Fe}, {-v*dt+L, qe, i, -v*qe*B+Fm}, {-v*dt+L, qe, -d*h*L+V, -dt*i+Q}, {-v*dt+L, qe, -d*h*L+V, -v*qe*B+Fe}, {-v*dt+L, qe, -d*h*L+V, -v*qe*B+Fm}, {-v*dt+L, qe, -dt*i+Q, -v*qe*B+Fe}, {-v*dt+L, qe, -dt*i+Q, -v*qe*B+Fm}, {-v*dt+L, qe, -v*qe*B+Fe, -v*qe*B+Fm}, {-v*dt+L, i, -d*h*L+V, -dt*i+Q}, {-v*dt+L, i, -d*h*L+V, -v*qe*B+Fe}, {-v*dt+L, i, -d*h*L+V, -v*qe*B+Fm}, {-v*dt+L, i, -dt*i+Q, -v*qe*B+Fe}, {-v*dt+L, i, -dt*i+Q, -v*qe*B+Fm}, {-v*dt+L, i, -v*qe*B+Fe, -v*qe*B+Fm}, {-v*dt+L, -d*h*L+V, -dt*i+Q, -v*qe*B+Fe}, {-v*dt+L, -d*h*L+V, -dt*i+Q, -v*qe*B+Fm}, {-v*dt+L, -d*h*L+V, -v*qe*B+Fe, -v*qe*B+Fm}, {-v*dt+L, -dt*i+Q, -v*qe*B+Fe, -v*qe*B+Fm}, {qe, i, -d*h*L+V, -dt*i+Q}, {qe, i, -d*h*L+V, -v*qe*B+Fe}, {qe, i, -d*h*L+V, -v*qe*B+Fm}, {qe, i, -dt*i+Q, -v*qe*B+Fe}, {qe, i, -dt*i+Q, -v*qe*B+Fm}, {qe, i, -v*qe*B+Fe, -v*qe*B+Fm}, {qe, -d*h*L+V, -dt*i+Q, -v*qe*B+Fe}, {qe, -d*h*L+V, -dt*i+Q, -v*qe*B+Fm}, {qe, -d*h*L+V, -v*qe*B+Fe, -v*qe*B+Fm}, {qe, -dt*i+Q, -v*qe*B+Fe, -v*qe*B+Fm}, {i, -d*h*L+V, -dt*i+Q, -v*qe*B+Fe}, {i, -d*h*L+V, -dt*i+Q, -v*qe*B+Fm}, {i, -d*h*L+V, -v*qe*B+Fe, -v*qe*B+Fm}, {i, -dt*i+Q, -v*qe*B+Fe, -v*qe*B+Fm}, {-d*h*L+V, -dt*i+Q, -v*qe*B+Fe, -v*qe*B+Fm}, {-v*dt+L}, {qe}, {-d*h*L+V}, {-dt*i+Q}, {dt}, {-v*qe*B+Fe}, {-v*qe*B+Fm}, {-v*dt+L, qe}, {-v*dt+L, -d*h*L+V}, {-v*dt+L, -dt*i+Q}, {-v*dt+L, dt}, {-v*dt+L, -v*qe*B+Fe}, {-v*dt+L, -v*qe*B+Fm}, {qe, -d*h*L+V}, {qe, -dt*i+Q}, {qe, dt}, {qe, -v*qe*B+Fe}, {qe, -v*qe*B+Fm}, {-d*h*L+V, -dt*i+Q}, {-d*h*L+V, dt}, {-d*h*L+V, -v*qe*B+Fe}, {-d*h*L+V, -v*qe*B+Fm}, {-dt*i+Q, dt}, {-dt*i+Q, -v*qe*B+Fe}, {-dt*i+Q, -v*qe*B+Fm}, {dt, -v*qe*B+Fe}, {dt, -v*qe*B+Fm}, {-v*qe*B+Fe, -v*qe*B+Fm}, {-v*dt+L, qe, -d*h*L+V}, {-v*dt+L, qe, -dt*i+Q}, {-v*dt+L, qe, dt}, {-v*dt+L, qe, -v*qe*B+Fe}, {-v*dt+L, qe, -v*qe*B+Fm}, {-v*dt+L, -d*h*L+V, -dt*i+Q}, {-v*dt+L, -d*h*L+V, dt}, {-v*dt+L, -d*h*L+V, -v*qe*B+Fe}, {-v*dt+L, -d*h*L+V, -v*qe*B+Fm}, {-v*dt+L, -dt*i+Q, dt}, {-v*dt+L, -dt*i+Q, -v*qe*B+Fe}, {-v*dt+L, -dt*i+Q, -v*qe*B+Fm}, {-v*dt+L, dt, -v*qe*B+Fe}, {-v*dt+L, dt, -v*qe*B+Fm}, {-v*dt+L, -v*qe*B+Fe, -v*qe*B+Fm}, {qe, -d*h*L+V, -dt*i+Q}, {qe, -d*h*L+V, dt}, {qe, -d*h*L+V, -v*qe*B+Fe}, {qe, -d*h*L+V, -v*qe*B+Fm}, {qe, -dt*i+Q, dt}, {qe, -dt*i+Q, -v*qe*B+Fe}, {qe, -dt*i+Q, -v*qe*B+Fm}, {qe, dt, -v*qe*B+Fe}, {qe, dt, -v*qe*B+Fm}, {qe, -v*qe*B+Fe, -v*qe*B+Fm}, {-d*h*L+V, -dt*i+Q, dt}, {-d*h*L+V, -dt*i+Q, -v*qe*B+Fe}, {-d*h*L+V, -dt*i+Q, -v*qe*B+Fm}, {-d*h*L+V, dt, -v*qe*B+Fe}, {-d*h*L+V, dt, -v*qe*B+Fm}, {-d*h*L+V, -v*qe*B+Fe, -v*qe*B+Fm}, {-dt*i+Q, dt, -v*qe*B+Fe}, {-dt*i+Q, dt, -v*qe*B+Fm}, {-dt*i+Q, -v*qe*B+Fe, -v*qe*B+Fm}, {dt, -v*qe*B+Fe, -v*qe*B+Fm}, {-v*dt+L, qe, -d*h*L+V, -dt*i+Q}, {-v*dt+L, qe, -d*h*L+V, dt}, {-v*dt+L, qe, -d*h*L+V, -v*qe*B+Fe}, {-v*dt+L, qe, -d*h*L+V, -v*qe*B+Fm}, {-v*dt+L, qe, -dt*i+Q, dt}, {-v*dt+L, qe, -dt*i+Q, -v*qe*B+Fe}, {-v*dt+L, qe, -dt*i+Q, -v*qe*B+Fm}, {-v*dt+L, qe, dt, -v*qe*B+Fe}, {-v*dt+L, qe, dt, -v*qe*B+Fm}, {-v*dt+L, qe, -v*qe*B+Fe, -v*qe*B+Fm}, {-v*dt+L, -d*h*L+V, -dt*i+Q, dt}, {-v*dt+L, -d*h*L+V, -dt*i+Q, -v*qe*B+Fe}, {-v*dt+L, -d*h*L+V, -dt*i+Q, -v*qe*B+Fm}, {-v*dt+L, -d*h*L+V, dt, -v*qe*B+Fe}, {-v*dt+L, -d*h*L+V, dt, -v*qe*B+Fm}, {-v*dt+L, -d*h*L+V, -v*qe*B+Fe, -v*qe*B+Fm}, {-v*dt+L, -dt*i+Q, dt, -v*qe*B+Fe}, {-v*dt+L, -dt*i+Q, dt, -v*qe*B+Fm}, {-v*dt+L, -dt*i+Q, -v*qe*B+Fe, -v*qe*B+Fm}, {-v*dt+L, dt, -v*qe*B+Fe, -v*qe*B+Fm}, {qe, -d*h*L+V, -dt*i+Q, dt}, {qe, -d*h*L+V, -dt*i+Q, -v*qe*B+Fe}, {qe, -d*h*L+V, -dt*i+Q, -v*qe*B+Fm}, {qe, -d*h*L+V, dt, -v*qe*B+Fe}, {qe, -d*h*L+V, dt, -v*qe*B+Fm}, {qe, -d*h*L+V, -v*qe*B+Fe, -v*qe*B+Fm}, {qe, -dt*i+Q, dt, -v*qe*B+Fe}, {qe, -dt*i+Q, dt, -v*qe*B+Fm}, {qe, -dt*i+Q, -v*qe*B+Fe, -v*qe*B+Fm}, {qe, dt, -v*qe*B+Fe, -v*qe*B+Fm}, {-d*h*L+V, -dt*i+Q, dt, -v*qe*B+Fe}, {-d*h*L+V, -dt*i+Q, dt, -v*qe*B+Fm}, {-d*h*L+V, -dt*i+Q, -v*qe*B+Fe, -v*qe*B+Fm}, {-d*h*L+V, dt, -v*qe*B+Fe, -v*qe*B+Fm}, {-dt*i+Q, dt, -v*qe*B+Fe, -v*qe*B+Fm}, {-v*dt+L}, {i}, {-d*h*L+V}, {N}, {-dt*i+Q}, {-v*qe*B+Fe}, {-v*qe*B+Fm}, {-v*dt+L, i}, {-v*dt+L, -d*h*L+V}, {-v*dt+L, N}, {-v*dt+L, -dt*i+Q}, {-v*dt+L, -v*qe*B+Fe}, {-v*dt+L, -v*qe*B+Fm}, {i, -d*h*L+V}, {i, N}, {i, -dt*i+Q}, {i, -v*qe*B+Fe}, {i, -v*qe*B+Fm}, {-d*h*L+V, N}, {-d*h*L+V, -dt*i+Q}, {-d*h*L+V, -v*qe*B+Fe}, {-d*h*L+V, -v*qe*B+Fm}, {N, -dt*i+Q}, {N, -v*qe*B+Fe}, {N, -v*qe*B+Fm}, {-dt*i+Q, -v*qe*B+Fe}, {-dt*i+Q, -v*qe*B+Fm}, {-v*qe*B+Fe, -v*qe*B+Fm}, {-v*dt+L, i, -d*h*L+V}, {-v*dt+L, i, N}, {-v*dt+L, i, -dt*i+Q}, {-v*dt+L, i, -v*qe*B+Fe}, {-v*dt+L, i, -v*qe*B+Fm}, {-v*dt+L, -d*h*L+V, N}, {-v*dt+L, -d*h*L+V, -dt*i+Q}, {-v*dt+L, -d*h*L+V, -v*qe*B+Fe}, {-v*dt+L, -d*h*L+V, -v*qe*B+Fm}, {-v*dt+L, N, -dt*i+Q}, {-v*dt+L, N, -v*qe*B+Fe}, {-v*dt+L, N, -v*qe*B+Fm}, {-v*dt+L, -dt*i+Q, -v*qe*B+Fe}, {-v*dt+L, -dt*i+Q, -v*qe*B+Fm}, {-v*dt+L, -v*qe*B+Fe, -v*qe*B+Fm}, {i, -d*h*L+V, N}, {i, -d*h*L+V, -dt*i+Q}, {i, -d*h*L+V, -v*qe*B+Fe}, {i, -d*h*L+V, -v*qe*B+Fm}, {i, N, -dt*i+Q}, {i, N, -v*qe*B+Fe}, {i, N, -v*qe*B+Fm}, {i, -dt*i+Q, -v*qe*B+Fe}, {i, -dt*i+Q, -v*qe*B+Fm}, {i, -v*qe*B+Fe, -v*qe*B+Fm}, {-d*h*L+V, N, -dt*i+Q}, {-d*h*L+V, N, -v*qe*B+Fe}, {-d*h*L+V, N, -v*qe*B+Fm}, {-d*h*L+V, -dt*i+Q, -v*qe*B+Fe}, {-d*h*L+V, -dt*i+Q, -v*qe*B+Fm}, {-d*h*L+V, -v*qe*B+Fe, -v*qe*B+Fm}, {N, -dt*i+Q, -v*qe*B+Fe}, {N, -dt*i+Q, -v*qe*B+Fm}, {N, -v*qe*B+Fe, -v*qe*B+Fm}, {-dt*i+Q, -v*qe*B+Fe, -v*qe*B+Fm}, {-v*dt+L, i, -d*h*L+V, N}, {-v*dt+L, i, -d*h*L+V, -dt*i+Q}, {-v*dt+L, i, -d*h*L+V, -v*qe*B+Fe}, {-v*dt+L, i, -d*h*L+V, -v*qe*B+Fm}, {-v*dt+L, i, N, -dt*i+Q}, {-v*dt+L, i, N, -v*qe*B+Fe}, {-v*dt+L, i, N, -v*qe*B+Fm}, {-v*dt+L, i, -dt*i+Q, -v*qe*B+Fe}, {-v*dt+L, i, -dt*i+Q, -v*qe*B+Fm}, {-v*dt+L, i, -v*qe*B+Fe, -v*qe*B+Fm}, {-v*dt+L, -d*h*L+V, N, -dt*i+Q}, {-v*dt+L, -d*h*L+V, N, -v*qe*B+Fe}, {-v*dt+L, -d*h*L+V, N, -v*qe*B+Fm}, {-v*dt+L, -d*h*L+V, -dt*i+Q, -v*qe*B+Fe}, {-v*dt+L, -d*h*L+V, -dt*i+Q, -v*qe*B+Fm}, {-v*dt+L, -d*h*L+V, -v*qe*B+Fe, -v*qe*B+Fm}, {-v*dt+L, N, -dt*i+Q, -v*qe*B+Fe}, {-v*dt+L, N, -dt*i+Q, -v*qe*B+Fm}, {-v*dt+L, N, -v*qe*B+Fe, -v*qe*B+Fm}, {-v*dt+L, -dt*i+Q, -v*qe*B+Fe, -v*qe*B+Fm}, {i, -d*h*L+V, N, -dt*i+Q}, {i, -d*h*L+V, N, -v*qe*B+Fe}, {i, -d*h*L+V, N, -v*qe*B+Fm}, {i, -d*h*L+V, -dt*i+Q, -v*qe*B+Fe}, {i, -d*h*L+V, -dt*i+Q, -v*qe*B+Fm}, {i, -d*h*L+V, -v*qe*B+Fe, -v*qe*B+Fm}, {i, N, -dt*i+Q, -v*qe*B+Fe}, {i, N, -dt*i+Q, -v*qe*B+Fm}, {i, N, -v*qe*B+Fe, -v*qe*B+Fm}, {i, -dt*i+Q, -v*qe*B+Fe, -v*qe*B+Fm}, {-d*h*L+V, N, -dt*i+Q, -v*qe*B+Fe}, {-d*h*L+V, N, -dt*i+Q, -v*qe*B+Fm}, {-d*h*L+V, N, -v*qe*B+Fe, -v*qe*B+Fm}, {-d*h*L+V, -dt*i+Q, -v*qe*B+Fe, -v*qe*B+Fm}, {N, -dt*i+Q, -v*qe*B+Fe, -v*qe*B+Fm}, {-v*dt+L}, {-d*h*L+V}, {N}, {-dt*i+Q}, {dt}, {-v*qe*B+Fe}, {-v*qe*B+Fm}, {-v*dt+L, -d*h*L+V}, {-v*dt+L, N}, {-v*dt+L, -dt*i+Q}, {-v*dt+L, dt}, {-v*dt+L, -v*qe*B+Fe}, {-v*dt+L, -v*qe*B+Fm}, {-d*h*L+V, N}, {-d*h*L+V, -dt*i+Q}, {-d*h*L+V, dt}, {-d*h*L+V, -v*qe*B+Fe}, {-d*h*L+V, -v*qe*B+Fm}, {N, -dt*i+Q}, {N, dt}, {N, -v*qe*B+Fe}, {N, -v*qe*B+Fm}, {-dt*i+Q, dt}, {-dt*i+Q, -v*qe*B+Fe}, {-dt*i+Q, -v*qe*B+Fm}, {dt, -v*qe*B+Fe}, {dt, -v*qe*B+Fm}, {-v*qe*B+Fe, -v*qe*B+Fm}, {-v*dt+L, -d*h*L+V, N}, {-v*dt+L, -d*h*L+V, -dt*i+Q}, {-v*dt+L, -d*h*L+V, dt}, {-v*dt+L, -d*h*L+V, -v*qe*B+Fe}, {-v*dt+L, -d*h*L+V, -v*qe*B+Fm}, {-v*dt+L, N, -dt*i+Q}, {-v*dt+L, N, dt}, {-v*dt+L, N, -v*qe*B+Fe}, {-v*dt+L, N, -v*qe*B+Fm}, {-v*dt+L, -dt*i+Q, dt}, {-v*dt+L, -dt*i+Q, -v*qe*B+Fe}, {-v*dt+L, -dt*i+Q, -v*qe*B+Fm}, {-v*dt+L, dt, -v*qe*B+Fe}, {-v*dt+L, dt, -v*qe*B+Fm}, {-v*dt+L, -v*qe*B+Fe, -v*qe*B+Fm}, {-d*h*L+V, N, -dt*i+Q}, {-d*h*L+V, N, dt}, {-d*h*L+V, N, -v*qe*B+Fe}, {-d*h*L+V, N, -v*qe*B+Fm}, {-d*h*L+V, -dt*i+Q, dt}, {-d*h*L+V, -dt*i+Q, -v*qe*B+Fe}, {-d*h*L+V, -dt*i+Q, -v*qe*B+Fm}, {-d*h*L+V, dt, -v*qe*B+Fe}, {-d*h*L+V, dt, -v*qe*B+Fm}, {-d*h*L+V, -v*qe*B+Fe, -v*qe*B+Fm}, {N, -dt*i+Q, dt}, {N, -dt*i+Q, -v*qe*B+Fe}, {N, -dt*i+Q, -v*qe*B+Fm}, {N, dt, -v*qe*B+Fe}, {N, dt, -v*qe*B+Fm}, {N, -v*qe*B+Fe, -v*qe*B+Fm}, {-dt*i+Q, dt, -v*qe*B+Fe}, {-dt*i+Q, dt, -v*qe*B+Fm}, {-dt*i+Q, -v*qe*B+Fe, -v*qe*B+Fm}, {dt, -v*qe*B+Fe, -v*qe*B+Fm}, {-v*dt+L, -d*h*L+V, N, -dt*i+Q}, {-v*dt+L, -d*h*L+V, N, dt}, {-v*dt+L, -d*h*L+V, N, -v*qe*B+Fe}, {-v*dt+L, -d*h*L+V, N, -v*qe*B+Fm}, {-v*dt+L, -d*h*L+V, -dt*i+Q, dt}, {-v*dt+L, -d*h*L+V, -dt*i+Q, -v*qe*B+Fe}, {-v*dt+L, -d*h*L+V, -dt*i+Q, -v*qe*B+Fm}, {-v*dt+L, -d*h*L+V, dt, -v*qe*B+Fe}, {-v*dt+L, -d*h*L+V, dt, -v*qe*B+Fm}, {-v*dt+L, -d*h*L+V, -v*qe*B+Fe, -v*qe*B+Fm}, {-v*dt+L, N, -dt*i+Q, dt}, {-v*dt+L, N, -dt*i+Q, -v*qe*B+Fe}, {-v*dt+L, N, -dt*i+Q, -v*qe*B+Fm}, {-v*dt+L, N, dt, -v*qe*B+Fe}, {-v*dt+L, N, dt, -v*qe*B+Fm}, {-v*dt+L, N, -v*qe*B+Fe, -v*qe*B+Fm}, {-v*dt+L, -dt*i+Q, dt, -v*qe*B+Fe}, {-v*dt+L, -dt*i+Q, dt, -v*qe*B+Fm}, {-v*dt+L, -dt*i+Q, -v*qe*B+Fe, -v*qe*B+Fm}, {-v*dt+L, dt, -v*qe*B+Fe, -v*qe*B+Fm}, {-d*h*L+V, N, -dt*i+Q, dt}, {-d*h*L+V, N, -dt*i+Q, -v*qe*B+Fe}, {-d*h*L+V, N, -dt*i+Q, -v*qe*B+Fm}, {-d*h*L+V, N, dt, -v*qe*B+Fe}, {-d*h*L+V, N, dt, -v*qe*B+Fm}, {-d*h*L+V, N, -v*qe*B+Fe, -v*qe*B+Fm}, {-d*h*L+V, -dt*i+Q, dt, -v*qe*B+Fe}, {-d*h*L+V, -dt*i+Q, dt, -v*qe*B+Fm}, {-d*h*L+V, -dt*i+Q, -v*qe*B+Fe, -v*qe*B+Fm}, {-d*h*L+V, dt, -v*qe*B+Fe, -v*qe*B+Fm}, {N, -dt*i+Q, dt, -v*qe*B+Fe}, {N, -dt*i+Q, dt, -v*qe*B+Fm}, {N, -dt*i+Q, -v*qe*B+Fe, -v*qe*B+Fm}, {N, dt, -v*qe*B+Fe, -v*qe*B+Fm}, {-dt*i+Q, dt, -v*qe*B+Fe, -v*qe*B+Fm}};

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
f = openOut "results/hall/abduction/noiseless/3_axiom(s)_removed/combo_2_4_8/reasoning/reasoning_output.txt";
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

print("Reasoning complete. Output written to results/hall/abduction/noiseless/3_axiom(s)_removed/combo_2_4_8/reasoning/reasoning_output.txt");
