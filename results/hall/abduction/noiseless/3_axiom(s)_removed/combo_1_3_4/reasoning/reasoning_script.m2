-- AI-Noether: Reasoning Template (Noiseless)
-- Tests if candidate axiom sets, when added to remaining axioms, prove targets

needsPackage("PrimaryDecomposition", Reload => true)

-- Ring definition
R = QQ[Fm, d, v, Fe, E, dt, Q, N, V, i, n, qe, B, h, L, UH, MonomialOrder => Lex];

-- Input data
remainingAxioms = toList([Fe - qe*E, v*dt - L, i*dt - Q, Q - N*qe, n*V - N, V - L*h*d]);
qList = toList([N*qe*UH - i*B*h*L]);
k = #qList;

-- Per-target variable partitions
measuredPerTarget = {{UH, h, L, i, B, N, qe}};
nonMeasuredPerTarget = {{Fm, d, v, Fe, E, dt, Q, V, n}};

-- Candidate axiom sets to test (list of lists)
candidateSets = {{}, {v*B*h-UH}, {d*n*qe*UH-i*B}, {d*v*n*qe*h-i}, {-v*dt+L}, {-d*h*L+V}, {-V*n+N}, {-dt*i+Q}, {-E*qe+Fe}, {v*B*h-UH, d*n*qe*UH-i*B}, {v*B*h-UH, d*v*n*qe*h-i}, {v*B*h-UH, -v*dt+L}, {v*B*h-UH, -d*h*L+V}, {v*B*h-UH, -V*n+N}, {v*B*h-UH, -dt*i+Q}, {v*B*h-UH, -E*qe+Fe}, {d*n*qe*UH-i*B, d*v*n*qe*h-i}, {d*n*qe*UH-i*B, -v*dt+L}, {d*n*qe*UH-i*B, -d*h*L+V}, {d*n*qe*UH-i*B, -V*n+N}, {d*n*qe*UH-i*B, -dt*i+Q}, {d*n*qe*UH-i*B, -E*qe+Fe}, {d*v*n*qe*h-i, -v*dt+L}, {d*v*n*qe*h-i, -d*h*L+V}, {d*v*n*qe*h-i, -V*n+N}, {d*v*n*qe*h-i, -dt*i+Q}, {d*v*n*qe*h-i, -E*qe+Fe}, {-v*dt+L, -d*h*L+V}, {-v*dt+L, -V*n+N}, {-v*dt+L, -dt*i+Q}, {-v*dt+L, -E*qe+Fe}, {-d*h*L+V, -V*n+N}, {-d*h*L+V, -dt*i+Q}, {-d*h*L+V, -E*qe+Fe}, {-V*n+N, -dt*i+Q}, {-V*n+N, -E*qe+Fe}, {-dt*i+Q, -E*qe+Fe}, {v*B*h-UH, d*n*qe*UH-i*B, d*v*n*qe*h-i}, {v*B*h-UH, d*n*qe*UH-i*B, -v*dt+L}, {v*B*h-UH, d*n*qe*UH-i*B, -d*h*L+V}, {v*B*h-UH, d*n*qe*UH-i*B, -V*n+N}, {v*B*h-UH, d*n*qe*UH-i*B, -dt*i+Q}, {v*B*h-UH, d*n*qe*UH-i*B, -E*qe+Fe}, {v*B*h-UH, d*v*n*qe*h-i, -v*dt+L}, {v*B*h-UH, d*v*n*qe*h-i, -d*h*L+V}, {v*B*h-UH, d*v*n*qe*h-i, -V*n+N}, {v*B*h-UH, d*v*n*qe*h-i, -dt*i+Q}, {v*B*h-UH, d*v*n*qe*h-i, -E*qe+Fe}, {v*B*h-UH, -v*dt+L, -d*h*L+V}, {v*B*h-UH, -v*dt+L, -V*n+N}, {v*B*h-UH, -v*dt+L, -dt*i+Q}, {v*B*h-UH, -v*dt+L, -E*qe+Fe}, {v*B*h-UH, -d*h*L+V, -V*n+N}, {v*B*h-UH, -d*h*L+V, -dt*i+Q}, {v*B*h-UH, -d*h*L+V, -E*qe+Fe}, {v*B*h-UH, -V*n+N, -dt*i+Q}, {v*B*h-UH, -V*n+N, -E*qe+Fe}, {v*B*h-UH, -dt*i+Q, -E*qe+Fe}, {d*n*qe*UH-i*B, d*v*n*qe*h-i, -v*dt+L}, {d*n*qe*UH-i*B, d*v*n*qe*h-i, -d*h*L+V}, {d*n*qe*UH-i*B, d*v*n*qe*h-i, -V*n+N}, {d*n*qe*UH-i*B, d*v*n*qe*h-i, -dt*i+Q}, {d*n*qe*UH-i*B, d*v*n*qe*h-i, -E*qe+Fe}, {d*n*qe*UH-i*B, -v*dt+L, -d*h*L+V}, {d*n*qe*UH-i*B, -v*dt+L, -V*n+N}, {d*n*qe*UH-i*B, -v*dt+L, -dt*i+Q}, {d*n*qe*UH-i*B, -v*dt+L, -E*qe+Fe}, {d*n*qe*UH-i*B, -d*h*L+V, -V*n+N}, {d*n*qe*UH-i*B, -d*h*L+V, -dt*i+Q}, {d*n*qe*UH-i*B, -d*h*L+V, -E*qe+Fe}, {d*n*qe*UH-i*B, -V*n+N, -dt*i+Q}, {d*n*qe*UH-i*B, -V*n+N, -E*qe+Fe}, {d*n*qe*UH-i*B, -dt*i+Q, -E*qe+Fe}, {d*v*n*qe*h-i, -v*dt+L, -d*h*L+V}, {d*v*n*qe*h-i, -v*dt+L, -V*n+N}, {d*v*n*qe*h-i, -v*dt+L, -dt*i+Q}, {d*v*n*qe*h-i, -v*dt+L, -E*qe+Fe}, {d*v*n*qe*h-i, -d*h*L+V, -V*n+N}, {d*v*n*qe*h-i, -d*h*L+V, -dt*i+Q}, {d*v*n*qe*h-i, -d*h*L+V, -E*qe+Fe}, {d*v*n*qe*h-i, -V*n+N, -dt*i+Q}, {d*v*n*qe*h-i, -V*n+N, -E*qe+Fe}, {d*v*n*qe*h-i, -dt*i+Q, -E*qe+Fe}, {-v*dt+L, -d*h*L+V, -V*n+N}, {-v*dt+L, -d*h*L+V, -dt*i+Q}, {-v*dt+L, -d*h*L+V, -E*qe+Fe}, {-v*dt+L, -V*n+N, -dt*i+Q}, {-v*dt+L, -V*n+N, -E*qe+Fe}, {-v*dt+L, -dt*i+Q, -E*qe+Fe}, {-d*h*L+V, -V*n+N, -dt*i+Q}, {-d*h*L+V, -V*n+N, -E*qe+Fe}, {-d*h*L+V, -dt*i+Q, -E*qe+Fe}, {-V*n+N, -dt*i+Q, -E*qe+Fe}, {v*B*h-UH, d*n*qe*UH-i*B, d*v*n*qe*h-i, -v*dt+L}, {v*B*h-UH, d*n*qe*UH-i*B, d*v*n*qe*h-i, -d*h*L+V}, {v*B*h-UH, d*n*qe*UH-i*B, d*v*n*qe*h-i, -V*n+N}, {v*B*h-UH, d*n*qe*UH-i*B, d*v*n*qe*h-i, -dt*i+Q}, {v*B*h-UH, d*n*qe*UH-i*B, d*v*n*qe*h-i, -E*qe+Fe}, {v*B*h-UH, d*n*qe*UH-i*B, -v*dt+L, -d*h*L+V}, {v*B*h-UH, d*n*qe*UH-i*B, -v*dt+L, -V*n+N}, {v*B*h-UH, d*n*qe*UH-i*B, -v*dt+L, -dt*i+Q}, {v*B*h-UH, d*n*qe*UH-i*B, -v*dt+L, -E*qe+Fe}, {v*B*h-UH, d*n*qe*UH-i*B, -d*h*L+V, -V*n+N}, {v*B*h-UH, d*n*qe*UH-i*B, -d*h*L+V, -dt*i+Q}, {v*B*h-UH, d*n*qe*UH-i*B, -d*h*L+V, -E*qe+Fe}, {v*B*h-UH, d*n*qe*UH-i*B, -V*n+N, -dt*i+Q}, {v*B*h-UH, d*n*qe*UH-i*B, -V*n+N, -E*qe+Fe}, {v*B*h-UH, d*n*qe*UH-i*B, -dt*i+Q, -E*qe+Fe}, {v*B*h-UH, d*v*n*qe*h-i, -v*dt+L, -d*h*L+V}, {v*B*h-UH, d*v*n*qe*h-i, -v*dt+L, -V*n+N}, {v*B*h-UH, d*v*n*qe*h-i, -v*dt+L, -dt*i+Q}, {v*B*h-UH, d*v*n*qe*h-i, -v*dt+L, -E*qe+Fe}, {v*B*h-UH, d*v*n*qe*h-i, -d*h*L+V, -V*n+N}, {v*B*h-UH, d*v*n*qe*h-i, -d*h*L+V, -dt*i+Q}, {v*B*h-UH, d*v*n*qe*h-i, -d*h*L+V, -E*qe+Fe}, {v*B*h-UH, d*v*n*qe*h-i, -V*n+N, -dt*i+Q}, {v*B*h-UH, d*v*n*qe*h-i, -V*n+N, -E*qe+Fe}, {v*B*h-UH, d*v*n*qe*h-i, -dt*i+Q, -E*qe+Fe}, {v*B*h-UH, -v*dt+L, -d*h*L+V, -V*n+N}, {v*B*h-UH, -v*dt+L, -d*h*L+V, -dt*i+Q}, {v*B*h-UH, -v*dt+L, -d*h*L+V, -E*qe+Fe}, {v*B*h-UH, -v*dt+L, -V*n+N, -dt*i+Q}, {v*B*h-UH, -v*dt+L, -V*n+N, -E*qe+Fe}, {v*B*h-UH, -v*dt+L, -dt*i+Q, -E*qe+Fe}, {v*B*h-UH, -d*h*L+V, -V*n+N, -dt*i+Q}, {v*B*h-UH, -d*h*L+V, -V*n+N, -E*qe+Fe}, {v*B*h-UH, -d*h*L+V, -dt*i+Q, -E*qe+Fe}, {v*B*h-UH, -V*n+N, -dt*i+Q, -E*qe+Fe}, {d*n*qe*UH-i*B, d*v*n*qe*h-i, -v*dt+L, -d*h*L+V}, {d*n*qe*UH-i*B, d*v*n*qe*h-i, -v*dt+L, -V*n+N}, {d*n*qe*UH-i*B, d*v*n*qe*h-i, -v*dt+L, -dt*i+Q}, {d*n*qe*UH-i*B, d*v*n*qe*h-i, -v*dt+L, -E*qe+Fe}, {d*n*qe*UH-i*B, d*v*n*qe*h-i, -d*h*L+V, -V*n+N}, {d*n*qe*UH-i*B, d*v*n*qe*h-i, -d*h*L+V, -dt*i+Q}, {d*n*qe*UH-i*B, d*v*n*qe*h-i, -d*h*L+V, -E*qe+Fe}, {d*n*qe*UH-i*B, d*v*n*qe*h-i, -V*n+N, -dt*i+Q}, {d*n*qe*UH-i*B, d*v*n*qe*h-i, -V*n+N, -E*qe+Fe}, {d*n*qe*UH-i*B, d*v*n*qe*h-i, -dt*i+Q, -E*qe+Fe}, {d*n*qe*UH-i*B, -v*dt+L, -d*h*L+V, -V*n+N}, {d*n*qe*UH-i*B, -v*dt+L, -d*h*L+V, -dt*i+Q}, {d*n*qe*UH-i*B, -v*dt+L, -d*h*L+V, -E*qe+Fe}, {d*n*qe*UH-i*B, -v*dt+L, -V*n+N, -dt*i+Q}, {d*n*qe*UH-i*B, -v*dt+L, -V*n+N, -E*qe+Fe}, {d*n*qe*UH-i*B, -v*dt+L, -dt*i+Q, -E*qe+Fe}, {d*n*qe*UH-i*B, -d*h*L+V, -V*n+N, -dt*i+Q}, {d*n*qe*UH-i*B, -d*h*L+V, -V*n+N, -E*qe+Fe}, {d*n*qe*UH-i*B, -d*h*L+V, -dt*i+Q, -E*qe+Fe}, {d*n*qe*UH-i*B, -V*n+N, -dt*i+Q, -E*qe+Fe}, {d*v*n*qe*h-i, -v*dt+L, -d*h*L+V, -V*n+N}, {d*v*n*qe*h-i, -v*dt+L, -d*h*L+V, -dt*i+Q}, {d*v*n*qe*h-i, -v*dt+L, -d*h*L+V, -E*qe+Fe}, {d*v*n*qe*h-i, -v*dt+L, -V*n+N, -dt*i+Q}, {d*v*n*qe*h-i, -v*dt+L, -V*n+N, -E*qe+Fe}, {d*v*n*qe*h-i, -v*dt+L, -dt*i+Q, -E*qe+Fe}, {d*v*n*qe*h-i, -d*h*L+V, -V*n+N, -dt*i+Q}, {d*v*n*qe*h-i, -d*h*L+V, -V*n+N, -E*qe+Fe}, {d*v*n*qe*h-i, -d*h*L+V, -dt*i+Q, -E*qe+Fe}, {d*v*n*qe*h-i, -V*n+N, -dt*i+Q, -E*qe+Fe}, {-v*dt+L, -d*h*L+V, -V*n+N, -dt*i+Q}, {-v*dt+L, -d*h*L+V, -V*n+N, -E*qe+Fe}, {-v*dt+L, -d*h*L+V, -dt*i+Q, -E*qe+Fe}, {-v*dt+L, -V*n+N, -dt*i+Q, -E*qe+Fe}, {-d*h*L+V, -V*n+N, -dt*i+Q, -E*qe+Fe}, {-v*dt+L}, {h}, {i}, {-d*h*L+V}, {-V*n+N}, {-dt*i+Q}, {-E*qe+Fe}, {-v*dt+L, h}, {-v*dt+L, i}, {-v*dt+L, -d*h*L+V}, {-v*dt+L, -V*n+N}, {-v*dt+L, -dt*i+Q}, {-v*dt+L, -E*qe+Fe}, {h, i}, {h, -d*h*L+V}, {h, -V*n+N}, {h, -dt*i+Q}, {h, -E*qe+Fe}, {i, -d*h*L+V}, {i, -V*n+N}, {i, -dt*i+Q}, {i, -E*qe+Fe}, {-d*h*L+V, -V*n+N}, {-d*h*L+V, -dt*i+Q}, {-d*h*L+V, -E*qe+Fe}, {-V*n+N, -dt*i+Q}, {-V*n+N, -E*qe+Fe}, {-dt*i+Q, -E*qe+Fe}, {-v*dt+L, h, i}, {-v*dt+L, h, -d*h*L+V}, {-v*dt+L, h, -V*n+N}, {-v*dt+L, h, -dt*i+Q}, {-v*dt+L, h, -E*qe+Fe}, {-v*dt+L, i, -d*h*L+V}, {-v*dt+L, i, -V*n+N}, {-v*dt+L, i, -dt*i+Q}, {-v*dt+L, i, -E*qe+Fe}, {-v*dt+L, -d*h*L+V, -V*n+N}, {-v*dt+L, -d*h*L+V, -dt*i+Q}, {-v*dt+L, -d*h*L+V, -E*qe+Fe}, {-v*dt+L, -V*n+N, -dt*i+Q}, {-v*dt+L, -V*n+N, -E*qe+Fe}, {-v*dt+L, -dt*i+Q, -E*qe+Fe}, {h, i, -d*h*L+V}, {h, i, -V*n+N}, {h, i, -dt*i+Q}, {h, i, -E*qe+Fe}, {h, -d*h*L+V, -V*n+N}, {h, -d*h*L+V, -dt*i+Q}, {h, -d*h*L+V, -E*qe+Fe}, {h, -V*n+N, -dt*i+Q}, {h, -V*n+N, -E*qe+Fe}, {h, -dt*i+Q, -E*qe+Fe}, {i, -d*h*L+V, -V*n+N}, {i, -d*h*L+V, -dt*i+Q}, {i, -d*h*L+V, -E*qe+Fe}, {i, -V*n+N, -dt*i+Q}, {i, -V*n+N, -E*qe+Fe}, {i, -dt*i+Q, -E*qe+Fe}, {-d*h*L+V, -V*n+N, -dt*i+Q}, {-d*h*L+V, -V*n+N, -E*qe+Fe}, {-d*h*L+V, -dt*i+Q, -E*qe+Fe}, {-V*n+N, -dt*i+Q, -E*qe+Fe}, {-v*dt+L, h, i, -d*h*L+V}, {-v*dt+L, h, i, -V*n+N}, {-v*dt+L, h, i, -dt*i+Q}, {-v*dt+L, h, i, -E*qe+Fe}, {-v*dt+L, h, -d*h*L+V, -V*n+N}, {-v*dt+L, h, -d*h*L+V, -dt*i+Q}, {-v*dt+L, h, -d*h*L+V, -E*qe+Fe}, {-v*dt+L, h, -V*n+N, -dt*i+Q}, {-v*dt+L, h, -V*n+N, -E*qe+Fe}, {-v*dt+L, h, -dt*i+Q, -E*qe+Fe}, {-v*dt+L, i, -d*h*L+V, -V*n+N}, {-v*dt+L, i, -d*h*L+V, -dt*i+Q}, {-v*dt+L, i, -d*h*L+V, -E*qe+Fe}, {-v*dt+L, i, -V*n+N, -dt*i+Q}, {-v*dt+L, i, -V*n+N, -E*qe+Fe}, {-v*dt+L, i, -dt*i+Q, -E*qe+Fe}, {-v*dt+L, -d*h*L+V, -V*n+N, -dt*i+Q}, {-v*dt+L, -d*h*L+V, -V*n+N, -E*qe+Fe}, {-v*dt+L, -d*h*L+V, -dt*i+Q, -E*qe+Fe}, {-v*dt+L, -V*n+N, -dt*i+Q, -E*qe+Fe}, {h, i, -d*h*L+V, -V*n+N}, {h, i, -d*h*L+V, -dt*i+Q}, {h, i, -d*h*L+V, -E*qe+Fe}, {h, i, -V*n+N, -dt*i+Q}, {h, i, -V*n+N, -E*qe+Fe}, {h, i, -dt*i+Q, -E*qe+Fe}, {h, -d*h*L+V, -V*n+N, -dt*i+Q}, {h, -d*h*L+V, -V*n+N, -E*qe+Fe}, {h, -d*h*L+V, -dt*i+Q, -E*qe+Fe}, {h, -V*n+N, -dt*i+Q, -E*qe+Fe}, {i, -d*h*L+V, -V*n+N, -dt*i+Q}, {i, -d*h*L+V, -V*n+N, -E*qe+Fe}, {i, -d*h*L+V, -dt*i+Q, -E*qe+Fe}, {i, -V*n+N, -dt*i+Q, -E*qe+Fe}, {-d*h*L+V, -V*n+N, -dt*i+Q, -E*qe+Fe}, {-v*dt+L}, {qe}, {i}, {-d*h*L+V}, {-V*n+N}, {-dt*i+Q}, {-E*qe+Fe}, {-v*dt+L, qe}, {-v*dt+L, i}, {-v*dt+L, -d*h*L+V}, {-v*dt+L, -V*n+N}, {-v*dt+L, -dt*i+Q}, {-v*dt+L, -E*qe+Fe}, {qe, i}, {qe, -d*h*L+V}, {qe, -V*n+N}, {qe, -dt*i+Q}, {qe, -E*qe+Fe}, {i, -d*h*L+V}, {i, -V*n+N}, {i, -dt*i+Q}, {i, -E*qe+Fe}, {-d*h*L+V, -V*n+N}, {-d*h*L+V, -dt*i+Q}, {-d*h*L+V, -E*qe+Fe}, {-V*n+N, -dt*i+Q}, {-V*n+N, -E*qe+Fe}, {-dt*i+Q, -E*qe+Fe}, {-v*dt+L, qe, i}, {-v*dt+L, qe, -d*h*L+V}, {-v*dt+L, qe, -V*n+N}, {-v*dt+L, qe, -dt*i+Q}, {-v*dt+L, qe, -E*qe+Fe}, {-v*dt+L, i, -d*h*L+V}, {-v*dt+L, i, -V*n+N}, {-v*dt+L, i, -dt*i+Q}, {-v*dt+L, i, -E*qe+Fe}, {-v*dt+L, -d*h*L+V, -V*n+N}, {-v*dt+L, -d*h*L+V, -dt*i+Q}, {-v*dt+L, -d*h*L+V, -E*qe+Fe}, {-v*dt+L, -V*n+N, -dt*i+Q}, {-v*dt+L, -V*n+N, -E*qe+Fe}, {-v*dt+L, -dt*i+Q, -E*qe+Fe}, {qe, i, -d*h*L+V}, {qe, i, -V*n+N}, {qe, i, -dt*i+Q}, {qe, i, -E*qe+Fe}, {qe, -d*h*L+V, -V*n+N}, {qe, -d*h*L+V, -dt*i+Q}, {qe, -d*h*L+V, -E*qe+Fe}, {qe, -V*n+N, -dt*i+Q}, {qe, -V*n+N, -E*qe+Fe}, {qe, -dt*i+Q, -E*qe+Fe}, {i, -d*h*L+V, -V*n+N}, {i, -d*h*L+V, -dt*i+Q}, {i, -d*h*L+V, -E*qe+Fe}, {i, -V*n+N, -dt*i+Q}, {i, -V*n+N, -E*qe+Fe}, {i, -dt*i+Q, -E*qe+Fe}, {-d*h*L+V, -V*n+N, -dt*i+Q}, {-d*h*L+V, -V*n+N, -E*qe+Fe}, {-d*h*L+V, -dt*i+Q, -E*qe+Fe}, {-V*n+N, -dt*i+Q, -E*qe+Fe}, {-v*dt+L, qe, i, -d*h*L+V}, {-v*dt+L, qe, i, -V*n+N}, {-v*dt+L, qe, i, -dt*i+Q}, {-v*dt+L, qe, i, -E*qe+Fe}, {-v*dt+L, qe, -d*h*L+V, -V*n+N}, {-v*dt+L, qe, -d*h*L+V, -dt*i+Q}, {-v*dt+L, qe, -d*h*L+V, -E*qe+Fe}, {-v*dt+L, qe, -V*n+N, -dt*i+Q}, {-v*dt+L, qe, -V*n+N, -E*qe+Fe}, {-v*dt+L, qe, -dt*i+Q, -E*qe+Fe}, {-v*dt+L, i, -d*h*L+V, -V*n+N}, {-v*dt+L, i, -d*h*L+V, -dt*i+Q}, {-v*dt+L, i, -d*h*L+V, -E*qe+Fe}, {-v*dt+L, i, -V*n+N, -dt*i+Q}, {-v*dt+L, i, -V*n+N, -E*qe+Fe}, {-v*dt+L, i, -dt*i+Q, -E*qe+Fe}, {-v*dt+L, -d*h*L+V, -V*n+N, -dt*i+Q}, {-v*dt+L, -d*h*L+V, -V*n+N, -E*qe+Fe}, {-v*dt+L, -d*h*L+V, -dt*i+Q, -E*qe+Fe}, {-v*dt+L, -V*n+N, -dt*i+Q, -E*qe+Fe}, {qe, i, -d*h*L+V, -V*n+N}, {qe, i, -d*h*L+V, -dt*i+Q}, {qe, i, -d*h*L+V, -E*qe+Fe}, {qe, i, -V*n+N, -dt*i+Q}, {qe, i, -V*n+N, -E*qe+Fe}, {qe, i, -dt*i+Q, -E*qe+Fe}, {qe, -d*h*L+V, -V*n+N, -dt*i+Q}, {qe, -d*h*L+V, -V*n+N, -E*qe+Fe}, {qe, -d*h*L+V, -dt*i+Q, -E*qe+Fe}, {qe, -V*n+N, -dt*i+Q, -E*qe+Fe}, {i, -d*h*L+V, -V*n+N, -dt*i+Q}, {i, -d*h*L+V, -V*n+N, -E*qe+Fe}, {i, -d*h*L+V, -dt*i+Q, -E*qe+Fe}, {i, -V*n+N, -dt*i+Q, -E*qe+Fe}, {-d*h*L+V, -V*n+N, -dt*i+Q, -E*qe+Fe}, {-v*dt+L}, {n}, {i}, {-d*h*L+V}, {-V*n+N}, {-dt*i+Q}, {-E*qe+Fe}, {-v*dt+L, n}, {-v*dt+L, i}, {-v*dt+L, -d*h*L+V}, {-v*dt+L, -V*n+N}, {-v*dt+L, -dt*i+Q}, {-v*dt+L, -E*qe+Fe}, {n, i}, {n, -d*h*L+V}, {n, -V*n+N}, {n, -dt*i+Q}, {n, -E*qe+Fe}, {i, -d*h*L+V}, {i, -V*n+N}, {i, -dt*i+Q}, {i, -E*qe+Fe}, {-d*h*L+V, -V*n+N}, {-d*h*L+V, -dt*i+Q}, {-d*h*L+V, -E*qe+Fe}, {-V*n+N, -dt*i+Q}, {-V*n+N, -E*qe+Fe}, {-dt*i+Q, -E*qe+Fe}, {-v*dt+L, n, i}, {-v*dt+L, n, -d*h*L+V}, {-v*dt+L, n, -V*n+N}, {-v*dt+L, n, -dt*i+Q}, {-v*dt+L, n, -E*qe+Fe}, {-v*dt+L, i, -d*h*L+V}, {-v*dt+L, i, -V*n+N}, {-v*dt+L, i, -dt*i+Q}, {-v*dt+L, i, -E*qe+Fe}, {-v*dt+L, -d*h*L+V, -V*n+N}, {-v*dt+L, -d*h*L+V, -dt*i+Q}, {-v*dt+L, -d*h*L+V, -E*qe+Fe}, {-v*dt+L, -V*n+N, -dt*i+Q}, {-v*dt+L, -V*n+N, -E*qe+Fe}, {-v*dt+L, -dt*i+Q, -E*qe+Fe}, {n, i, -d*h*L+V}, {n, i, -V*n+N}, {n, i, -dt*i+Q}, {n, i, -E*qe+Fe}, {n, -d*h*L+V, -V*n+N}, {n, -d*h*L+V, -dt*i+Q}, {n, -d*h*L+V, -E*qe+Fe}, {n, -V*n+N, -dt*i+Q}, {n, -V*n+N, -E*qe+Fe}, {n, -dt*i+Q, -E*qe+Fe}, {i, -d*h*L+V, -V*n+N}, {i, -d*h*L+V, -dt*i+Q}, {i, -d*h*L+V, -E*qe+Fe}, {i, -V*n+N, -dt*i+Q}, {i, -V*n+N, -E*qe+Fe}, {i, -dt*i+Q, -E*qe+Fe}, {-d*h*L+V, -V*n+N, -dt*i+Q}, {-d*h*L+V, -V*n+N, -E*qe+Fe}, {-d*h*L+V, -dt*i+Q, -E*qe+Fe}, {-V*n+N, -dt*i+Q, -E*qe+Fe}, {-v*dt+L, n, i, -d*h*L+V}, {-v*dt+L, n, i, -V*n+N}, {-v*dt+L, n, i, -dt*i+Q}, {-v*dt+L, n, i, -E*qe+Fe}, {-v*dt+L, n, -d*h*L+V, -V*n+N}, {-v*dt+L, n, -d*h*L+V, -dt*i+Q}, {-v*dt+L, n, -d*h*L+V, -E*qe+Fe}, {-v*dt+L, n, -V*n+N, -dt*i+Q}, {-v*dt+L, n, -V*n+N, -E*qe+Fe}, {-v*dt+L, n, -dt*i+Q, -E*qe+Fe}, {-v*dt+L, i, -d*h*L+V, -V*n+N}, {-v*dt+L, i, -d*h*L+V, -dt*i+Q}, {-v*dt+L, i, -d*h*L+V, -E*qe+Fe}, {-v*dt+L, i, -V*n+N, -dt*i+Q}, {-v*dt+L, i, -V*n+N, -E*qe+Fe}, {-v*dt+L, i, -dt*i+Q, -E*qe+Fe}, {-v*dt+L, -d*h*L+V, -V*n+N, -dt*i+Q}, {-v*dt+L, -d*h*L+V, -V*n+N, -E*qe+Fe}, {-v*dt+L, -d*h*L+V, -dt*i+Q, -E*qe+Fe}, {-v*dt+L, -V*n+N, -dt*i+Q, -E*qe+Fe}, {n, i, -d*h*L+V, -V*n+N}, {n, i, -d*h*L+V, -dt*i+Q}, {n, i, -d*h*L+V, -E*qe+Fe}, {n, i, -V*n+N, -dt*i+Q}, {n, i, -V*n+N, -E*qe+Fe}, {n, i, -dt*i+Q, -E*qe+Fe}, {n, -d*h*L+V, -V*n+N, -dt*i+Q}, {n, -d*h*L+V, -V*n+N, -E*qe+Fe}, {n, -d*h*L+V, -dt*i+Q, -E*qe+Fe}, {n, -V*n+N, -dt*i+Q, -E*qe+Fe}, {i, -d*h*L+V, -V*n+N, -dt*i+Q}, {i, -d*h*L+V, -V*n+N, -E*qe+Fe}, {i, -d*h*L+V, -dt*i+Q, -E*qe+Fe}, {i, -V*n+N, -dt*i+Q, -E*qe+Fe}, {-d*h*L+V, -V*n+N, -dt*i+Q, -E*qe+Fe}, {-v*dt+L}, {i}, {-d*h*L+V}, {-V*n+N}, {-dt*i+Q}, {-E*qe+Fe}, {v}, {-v*dt+L, i}, {-v*dt+L, -d*h*L+V}, {-v*dt+L, -V*n+N}, {-v*dt+L, -dt*i+Q}, {-v*dt+L, -E*qe+Fe}, {-v*dt+L, v}, {i, -d*h*L+V}, {i, -V*n+N}, {i, -dt*i+Q}, {i, -E*qe+Fe}, {i, v}, {-d*h*L+V, -V*n+N}, {-d*h*L+V, -dt*i+Q}, {-d*h*L+V, -E*qe+Fe}, {-d*h*L+V, v}, {-V*n+N, -dt*i+Q}, {-V*n+N, -E*qe+Fe}, {-V*n+N, v}, {-dt*i+Q, -E*qe+Fe}, {-dt*i+Q, v}, {-E*qe+Fe, v}, {-v*dt+L, i, -d*h*L+V}, {-v*dt+L, i, -V*n+N}, {-v*dt+L, i, -dt*i+Q}, {-v*dt+L, i, -E*qe+Fe}, {-v*dt+L, i, v}, {-v*dt+L, -d*h*L+V, -V*n+N}, {-v*dt+L, -d*h*L+V, -dt*i+Q}, {-v*dt+L, -d*h*L+V, -E*qe+Fe}, {-v*dt+L, -d*h*L+V, v}, {-v*dt+L, -V*n+N, -dt*i+Q}, {-v*dt+L, -V*n+N, -E*qe+Fe}, {-v*dt+L, -V*n+N, v}, {-v*dt+L, -dt*i+Q, -E*qe+Fe}, {-v*dt+L, -dt*i+Q, v}, {-v*dt+L, -E*qe+Fe, v}, {i, -d*h*L+V, -V*n+N}, {i, -d*h*L+V, -dt*i+Q}, {i, -d*h*L+V, -E*qe+Fe}, {i, -d*h*L+V, v}, {i, -V*n+N, -dt*i+Q}, {i, -V*n+N, -E*qe+Fe}, {i, -V*n+N, v}, {i, -dt*i+Q, -E*qe+Fe}, {i, -dt*i+Q, v}, {i, -E*qe+Fe, v}, {-d*h*L+V, -V*n+N, -dt*i+Q}, {-d*h*L+V, -V*n+N, -E*qe+Fe}, {-d*h*L+V, -V*n+N, v}, {-d*h*L+V, -dt*i+Q, -E*qe+Fe}, {-d*h*L+V, -dt*i+Q, v}, {-d*h*L+V, -E*qe+Fe, v}, {-V*n+N, -dt*i+Q, -E*qe+Fe}, {-V*n+N, -dt*i+Q, v}, {-V*n+N, -E*qe+Fe, v}, {-dt*i+Q, -E*qe+Fe, v}, {-v*dt+L, i, -d*h*L+V, -V*n+N}, {-v*dt+L, i, -d*h*L+V, -dt*i+Q}, {-v*dt+L, i, -d*h*L+V, -E*qe+Fe}, {-v*dt+L, i, -d*h*L+V, v}, {-v*dt+L, i, -V*n+N, -dt*i+Q}, {-v*dt+L, i, -V*n+N, -E*qe+Fe}, {-v*dt+L, i, -V*n+N, v}, {-v*dt+L, i, -dt*i+Q, -E*qe+Fe}, {-v*dt+L, i, -dt*i+Q, v}, {-v*dt+L, i, -E*qe+Fe, v}, {-v*dt+L, -d*h*L+V, -V*n+N, -dt*i+Q}, {-v*dt+L, -d*h*L+V, -V*n+N, -E*qe+Fe}, {-v*dt+L, -d*h*L+V, -V*n+N, v}, {-v*dt+L, -d*h*L+V, -dt*i+Q, -E*qe+Fe}, {-v*dt+L, -d*h*L+V, -dt*i+Q, v}, {-v*dt+L, -d*h*L+V, -E*qe+Fe, v}, {-v*dt+L, -V*n+N, -dt*i+Q, -E*qe+Fe}, {-v*dt+L, -V*n+N, -dt*i+Q, v}, {-v*dt+L, -V*n+N, -E*qe+Fe, v}, {-v*dt+L, -dt*i+Q, -E*qe+Fe, v}, {i, -d*h*L+V, -V*n+N, -dt*i+Q}, {i, -d*h*L+V, -V*n+N, -E*qe+Fe}, {i, -d*h*L+V, -V*n+N, v}, {i, -d*h*L+V, -dt*i+Q, -E*qe+Fe}, {i, -d*h*L+V, -dt*i+Q, v}, {i, -d*h*L+V, -E*qe+Fe, v}, {i, -V*n+N, -dt*i+Q, -E*qe+Fe}, {i, -V*n+N, -dt*i+Q, v}, {i, -V*n+N, -E*qe+Fe, v}, {i, -dt*i+Q, -E*qe+Fe, v}, {-d*h*L+V, -V*n+N, -dt*i+Q, -E*qe+Fe}, {-d*h*L+V, -V*n+N, -dt*i+Q, v}, {-d*h*L+V, -V*n+N, -E*qe+Fe, v}, {-d*h*L+V, -dt*i+Q, -E*qe+Fe, v}, {-V*n+N, -dt*i+Q, -E*qe+Fe, v}, {-v*dt+L}, {i}, {-d*h*L+V}, {-V*n+N}, {-dt*i+Q}, {-E*qe+Fe}, {d}, {-v*dt+L, i}, {-v*dt+L, -d*h*L+V}, {-v*dt+L, -V*n+N}, {-v*dt+L, -dt*i+Q}, {-v*dt+L, -E*qe+Fe}, {-v*dt+L, d}, {i, -d*h*L+V}, {i, -V*n+N}, {i, -dt*i+Q}, {i, -E*qe+Fe}, {i, d}, {-d*h*L+V, -V*n+N}, {-d*h*L+V, -dt*i+Q}, {-d*h*L+V, -E*qe+Fe}, {-d*h*L+V, d}, {-V*n+N, -dt*i+Q}, {-V*n+N, -E*qe+Fe}, {-V*n+N, d}, {-dt*i+Q, -E*qe+Fe}, {-dt*i+Q, d}, {-E*qe+Fe, d}, {-v*dt+L, i, -d*h*L+V}, {-v*dt+L, i, -V*n+N}, {-v*dt+L, i, -dt*i+Q}, {-v*dt+L, i, -E*qe+Fe}, {-v*dt+L, i, d}, {-v*dt+L, -d*h*L+V, -V*n+N}, {-v*dt+L, -d*h*L+V, -dt*i+Q}, {-v*dt+L, -d*h*L+V, -E*qe+Fe}, {-v*dt+L, -d*h*L+V, d}, {-v*dt+L, -V*n+N, -dt*i+Q}, {-v*dt+L, -V*n+N, -E*qe+Fe}, {-v*dt+L, -V*n+N, d}, {-v*dt+L, -dt*i+Q, -E*qe+Fe}, {-v*dt+L, -dt*i+Q, d}, {-v*dt+L, -E*qe+Fe, d}, {i, -d*h*L+V, -V*n+N}, {i, -d*h*L+V, -dt*i+Q}, {i, -d*h*L+V, -E*qe+Fe}, {i, -d*h*L+V, d}, {i, -V*n+N, -dt*i+Q}, {i, -V*n+N, -E*qe+Fe}, {i, -V*n+N, d}, {i, -dt*i+Q, -E*qe+Fe}, {i, -dt*i+Q, d}, {i, -E*qe+Fe, d}, {-d*h*L+V, -V*n+N, -dt*i+Q}, {-d*h*L+V, -V*n+N, -E*qe+Fe}, {-d*h*L+V, -V*n+N, d}, {-d*h*L+V, -dt*i+Q, -E*qe+Fe}, {-d*h*L+V, -dt*i+Q, d}, {-d*h*L+V, -E*qe+Fe, d}, {-V*n+N, -dt*i+Q, -E*qe+Fe}, {-V*n+N, -dt*i+Q, d}, {-V*n+N, -E*qe+Fe, d}, {-dt*i+Q, -E*qe+Fe, d}, {-v*dt+L, i, -d*h*L+V, -V*n+N}, {-v*dt+L, i, -d*h*L+V, -dt*i+Q}, {-v*dt+L, i, -d*h*L+V, -E*qe+Fe}, {-v*dt+L, i, -d*h*L+V, d}, {-v*dt+L, i, -V*n+N, -dt*i+Q}, {-v*dt+L, i, -V*n+N, -E*qe+Fe}, {-v*dt+L, i, -V*n+N, d}, {-v*dt+L, i, -dt*i+Q, -E*qe+Fe}, {-v*dt+L, i, -dt*i+Q, d}, {-v*dt+L, i, -E*qe+Fe, d}, {-v*dt+L, -d*h*L+V, -V*n+N, -dt*i+Q}, {-v*dt+L, -d*h*L+V, -V*n+N, -E*qe+Fe}, {-v*dt+L, -d*h*L+V, -V*n+N, d}, {-v*dt+L, -d*h*L+V, -dt*i+Q, -E*qe+Fe}, {-v*dt+L, -d*h*L+V, -dt*i+Q, d}, {-v*dt+L, -d*h*L+V, -E*qe+Fe, d}, {-v*dt+L, -V*n+N, -dt*i+Q, -E*qe+Fe}, {-v*dt+L, -V*n+N, -dt*i+Q, d}, {-v*dt+L, -V*n+N, -E*qe+Fe, d}, {-v*dt+L, -dt*i+Q, -E*qe+Fe, d}, {i, -d*h*L+V, -V*n+N, -dt*i+Q}, {i, -d*h*L+V, -V*n+N, -E*qe+Fe}, {i, -d*h*L+V, -V*n+N, d}, {i, -d*h*L+V, -dt*i+Q, -E*qe+Fe}, {i, -d*h*L+V, -dt*i+Q, d}, {i, -d*h*L+V, -E*qe+Fe, d}, {i, -V*n+N, -dt*i+Q, -E*qe+Fe}, {i, -V*n+N, -dt*i+Q, d}, {i, -V*n+N, -E*qe+Fe, d}, {i, -dt*i+Q, -E*qe+Fe, d}, {-d*h*L+V, -V*n+N, -dt*i+Q, -E*qe+Fe}, {-d*h*L+V, -V*n+N, -dt*i+Q, d}, {-d*h*L+V, -V*n+N, -E*qe+Fe, d}, {-d*h*L+V, -dt*i+Q, -E*qe+Fe, d}, {-V*n+N, -dt*i+Q, -E*qe+Fe, d}, {-v*dt+L}, {-d*h*L+V}, {-V*n+N}, {-dt*i+Q}, {dt}, {-E*qe+Fe}, {-v*dt+L, -d*h*L+V}, {-v*dt+L, -V*n+N}, {-v*dt+L, -dt*i+Q}, {-v*dt+L, dt}, {-v*dt+L, -E*qe+Fe}, {-d*h*L+V, -V*n+N}, {-d*h*L+V, -dt*i+Q}, {-d*h*L+V, dt}, {-d*h*L+V, -E*qe+Fe}, {-V*n+N, -dt*i+Q}, {-V*n+N, dt}, {-V*n+N, -E*qe+Fe}, {-dt*i+Q, dt}, {-dt*i+Q, -E*qe+Fe}, {dt, -E*qe+Fe}, {-v*dt+L, -d*h*L+V, -V*n+N}, {-v*dt+L, -d*h*L+V, -dt*i+Q}, {-v*dt+L, -d*h*L+V, dt}, {-v*dt+L, -d*h*L+V, -E*qe+Fe}, {-v*dt+L, -V*n+N, -dt*i+Q}, {-v*dt+L, -V*n+N, dt}, {-v*dt+L, -V*n+N, -E*qe+Fe}, {-v*dt+L, -dt*i+Q, dt}, {-v*dt+L, -dt*i+Q, -E*qe+Fe}, {-v*dt+L, dt, -E*qe+Fe}, {-d*h*L+V, -V*n+N, -dt*i+Q}, {-d*h*L+V, -V*n+N, dt}, {-d*h*L+V, -V*n+N, -E*qe+Fe}, {-d*h*L+V, -dt*i+Q, dt}, {-d*h*L+V, -dt*i+Q, -E*qe+Fe}, {-d*h*L+V, dt, -E*qe+Fe}, {-V*n+N, -dt*i+Q, dt}, {-V*n+N, -dt*i+Q, -E*qe+Fe}, {-V*n+N, dt, -E*qe+Fe}, {-dt*i+Q, dt, -E*qe+Fe}, {-v*dt+L, -d*h*L+V, -V*n+N, -dt*i+Q}, {-v*dt+L, -d*h*L+V, -V*n+N, dt}, {-v*dt+L, -d*h*L+V, -V*n+N, -E*qe+Fe}, {-v*dt+L, -d*h*L+V, -dt*i+Q, dt}, {-v*dt+L, -d*h*L+V, -dt*i+Q, -E*qe+Fe}, {-v*dt+L, -d*h*L+V, dt, -E*qe+Fe}, {-v*dt+L, -V*n+N, -dt*i+Q, dt}, {-v*dt+L, -V*n+N, -dt*i+Q, -E*qe+Fe}, {-v*dt+L, -V*n+N, dt, -E*qe+Fe}, {-v*dt+L, -dt*i+Q, dt, -E*qe+Fe}, {-d*h*L+V, -V*n+N, -dt*i+Q, dt}, {-d*h*L+V, -V*n+N, -dt*i+Q, -E*qe+Fe}, {-d*h*L+V, -V*n+N, dt, -E*qe+Fe}, {-d*h*L+V, -dt*i+Q, dt, -E*qe+Fe}, {-V*n+N, -dt*i+Q, dt, -E*qe+Fe}};

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
f = openOut "results/hall/abduction/noiseless/3_axiom(s)_removed/combo_1_3_4/reasoning/reasoning_output.txt";
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

print("Reasoning complete. Output written to results/hall/abduction/noiseless/3_axiom(s)_removed/combo_1_3_4/reasoning/reasoning_output.txt");
