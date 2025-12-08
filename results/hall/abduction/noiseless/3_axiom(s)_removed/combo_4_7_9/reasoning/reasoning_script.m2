-- AI-Noether: Reasoning Template (Noiseless)
-- Tests if candidate axiom sets, when added to remaining axioms, prove targets

needsPackage("PrimaryDecomposition", Reload => true)

-- Ring definition
R = QQ[Fm, d, v, Fe, E, dt, Q, N, V, i, n, qe, B, h, L, UH, MonomialOrder => Lex];

-- Input data
remainingAxioms = toList([Fm - qe*v*B, Fe - qe*E, Fm - Fe, v*dt - L, i*dt - Q, n*V - N]);
qList = toList([N*qe*UH - i*B*h*L]);
k = #qList;

-- Per-target variable partitions
measuredPerTarget = {{UH, h, L, i, B, N, qe}};
nonMeasuredPerTarget = {{Fm, d, v, Fe, E, dt, Q, V, n}};

-- Candidate axiom sets to test (list of lists)
candidateSets = {{}, {E*dt*i*h-V*n*qe*UH}, {v*B-E}, {-v*dt+L}, {-V*n+N}, {-dt*i+Q}, {-E*qe+Fe}, {-v*qe*B+Fm}, {E*dt*i*h-V*n*qe*UH, v*B-E}, {E*dt*i*h-V*n*qe*UH, -v*dt+L}, {E*dt*i*h-V*n*qe*UH, -V*n+N}, {E*dt*i*h-V*n*qe*UH, -dt*i+Q}, {E*dt*i*h-V*n*qe*UH, -E*qe+Fe}, {E*dt*i*h-V*n*qe*UH, -v*qe*B+Fm}, {v*B-E, -v*dt+L}, {v*B-E, -V*n+N}, {v*B-E, -dt*i+Q}, {v*B-E, -E*qe+Fe}, {v*B-E, -v*qe*B+Fm}, {-v*dt+L, -V*n+N}, {-v*dt+L, -dt*i+Q}, {-v*dt+L, -E*qe+Fe}, {-v*dt+L, -v*qe*B+Fm}, {-V*n+N, -dt*i+Q}, {-V*n+N, -E*qe+Fe}, {-V*n+N, -v*qe*B+Fm}, {-dt*i+Q, -E*qe+Fe}, {-dt*i+Q, -v*qe*B+Fm}, {-E*qe+Fe, -v*qe*B+Fm}, {E*dt*i*h-V*n*qe*UH, v*B-E, -v*dt+L}, {E*dt*i*h-V*n*qe*UH, v*B-E, -V*n+N}, {E*dt*i*h-V*n*qe*UH, v*B-E, -dt*i+Q}, {E*dt*i*h-V*n*qe*UH, v*B-E, -E*qe+Fe}, {E*dt*i*h-V*n*qe*UH, v*B-E, -v*qe*B+Fm}, {E*dt*i*h-V*n*qe*UH, -v*dt+L, -V*n+N}, {E*dt*i*h-V*n*qe*UH, -v*dt+L, -dt*i+Q}, {E*dt*i*h-V*n*qe*UH, -v*dt+L, -E*qe+Fe}, {E*dt*i*h-V*n*qe*UH, -v*dt+L, -v*qe*B+Fm}, {E*dt*i*h-V*n*qe*UH, -V*n+N, -dt*i+Q}, {E*dt*i*h-V*n*qe*UH, -V*n+N, -E*qe+Fe}, {E*dt*i*h-V*n*qe*UH, -V*n+N, -v*qe*B+Fm}, {E*dt*i*h-V*n*qe*UH, -dt*i+Q, -E*qe+Fe}, {E*dt*i*h-V*n*qe*UH, -dt*i+Q, -v*qe*B+Fm}, {E*dt*i*h-V*n*qe*UH, -E*qe+Fe, -v*qe*B+Fm}, {v*B-E, -v*dt+L, -V*n+N}, {v*B-E, -v*dt+L, -dt*i+Q}, {v*B-E, -v*dt+L, -E*qe+Fe}, {v*B-E, -v*dt+L, -v*qe*B+Fm}, {v*B-E, -V*n+N, -dt*i+Q}, {v*B-E, -V*n+N, -E*qe+Fe}, {v*B-E, -V*n+N, -v*qe*B+Fm}, {v*B-E, -dt*i+Q, -E*qe+Fe}, {v*B-E, -dt*i+Q, -v*qe*B+Fm}, {v*B-E, -E*qe+Fe, -v*qe*B+Fm}, {-v*dt+L, -V*n+N, -dt*i+Q}, {-v*dt+L, -V*n+N, -E*qe+Fe}, {-v*dt+L, -V*n+N, -v*qe*B+Fm}, {-v*dt+L, -dt*i+Q, -E*qe+Fe}, {-v*dt+L, -dt*i+Q, -v*qe*B+Fm}, {-v*dt+L, -E*qe+Fe, -v*qe*B+Fm}, {-V*n+N, -dt*i+Q, -E*qe+Fe}, {-V*n+N, -dt*i+Q, -v*qe*B+Fm}, {-V*n+N, -E*qe+Fe, -v*qe*B+Fm}, {-dt*i+Q, -E*qe+Fe, -v*qe*B+Fm}, {E*dt*i*h-V*n*qe*UH, v*B-E, -v*dt+L, -V*n+N}, {E*dt*i*h-V*n*qe*UH, v*B-E, -v*dt+L, -dt*i+Q}, {E*dt*i*h-V*n*qe*UH, v*B-E, -v*dt+L, -E*qe+Fe}, {E*dt*i*h-V*n*qe*UH, v*B-E, -v*dt+L, -v*qe*B+Fm}, {E*dt*i*h-V*n*qe*UH, v*B-E, -V*n+N, -dt*i+Q}, {E*dt*i*h-V*n*qe*UH, v*B-E, -V*n+N, -E*qe+Fe}, {E*dt*i*h-V*n*qe*UH, v*B-E, -V*n+N, -v*qe*B+Fm}, {E*dt*i*h-V*n*qe*UH, v*B-E, -dt*i+Q, -E*qe+Fe}, {E*dt*i*h-V*n*qe*UH, v*B-E, -dt*i+Q, -v*qe*B+Fm}, {E*dt*i*h-V*n*qe*UH, v*B-E, -E*qe+Fe, -v*qe*B+Fm}, {E*dt*i*h-V*n*qe*UH, -v*dt+L, -V*n+N, -dt*i+Q}, {E*dt*i*h-V*n*qe*UH, -v*dt+L, -V*n+N, -E*qe+Fe}, {E*dt*i*h-V*n*qe*UH, -v*dt+L, -V*n+N, -v*qe*B+Fm}, {E*dt*i*h-V*n*qe*UH, -v*dt+L, -dt*i+Q, -E*qe+Fe}, {E*dt*i*h-V*n*qe*UH, -v*dt+L, -dt*i+Q, -v*qe*B+Fm}, {E*dt*i*h-V*n*qe*UH, -v*dt+L, -E*qe+Fe, -v*qe*B+Fm}, {E*dt*i*h-V*n*qe*UH, -V*n+N, -dt*i+Q, -E*qe+Fe}, {E*dt*i*h-V*n*qe*UH, -V*n+N, -dt*i+Q, -v*qe*B+Fm}, {E*dt*i*h-V*n*qe*UH, -V*n+N, -E*qe+Fe, -v*qe*B+Fm}, {E*dt*i*h-V*n*qe*UH, -dt*i+Q, -E*qe+Fe, -v*qe*B+Fm}, {v*B-E, -v*dt+L, -V*n+N, -dt*i+Q}, {v*B-E, -v*dt+L, -V*n+N, -E*qe+Fe}, {v*B-E, -v*dt+L, -V*n+N, -v*qe*B+Fm}, {v*B-E, -v*dt+L, -dt*i+Q, -E*qe+Fe}, {v*B-E, -v*dt+L, -dt*i+Q, -v*qe*B+Fm}, {v*B-E, -v*dt+L, -E*qe+Fe, -v*qe*B+Fm}, {v*B-E, -V*n+N, -dt*i+Q, -E*qe+Fe}, {v*B-E, -V*n+N, -dt*i+Q, -v*qe*B+Fm}, {v*B-E, -V*n+N, -E*qe+Fe, -v*qe*B+Fm}, {v*B-E, -dt*i+Q, -E*qe+Fe, -v*qe*B+Fm}, {-v*dt+L, -V*n+N, -dt*i+Q, -E*qe+Fe}, {-v*dt+L, -V*n+N, -dt*i+Q, -v*qe*B+Fm}, {-v*dt+L, -V*n+N, -E*qe+Fe, -v*qe*B+Fm}, {-v*dt+L, -dt*i+Q, -E*qe+Fe, -v*qe*B+Fm}, {-V*n+N, -dt*i+Q, -E*qe+Fe, -v*qe*B+Fm}, {-v*dt+L}, {h}, {qe}, {-V*n+N}, {-dt*i+Q}, {-E*qe+Fe}, {-v*qe*B+Fm}, {-v*dt+L, h}, {-v*dt+L, qe}, {-v*dt+L, -V*n+N}, {-v*dt+L, -dt*i+Q}, {-v*dt+L, -E*qe+Fe}, {-v*dt+L, -v*qe*B+Fm}, {h, qe}, {h, -V*n+N}, {h, -dt*i+Q}, {h, -E*qe+Fe}, {h, -v*qe*B+Fm}, {qe, -V*n+N}, {qe, -dt*i+Q}, {qe, -E*qe+Fe}, {qe, -v*qe*B+Fm}, {-V*n+N, -dt*i+Q}, {-V*n+N, -E*qe+Fe}, {-V*n+N, -v*qe*B+Fm}, {-dt*i+Q, -E*qe+Fe}, {-dt*i+Q, -v*qe*B+Fm}, {-E*qe+Fe, -v*qe*B+Fm}, {-v*dt+L, h, qe}, {-v*dt+L, h, -V*n+N}, {-v*dt+L, h, -dt*i+Q}, {-v*dt+L, h, -E*qe+Fe}, {-v*dt+L, h, -v*qe*B+Fm}, {-v*dt+L, qe, -V*n+N}, {-v*dt+L, qe, -dt*i+Q}, {-v*dt+L, qe, -E*qe+Fe}, {-v*dt+L, qe, -v*qe*B+Fm}, {-v*dt+L, -V*n+N, -dt*i+Q}, {-v*dt+L, -V*n+N, -E*qe+Fe}, {-v*dt+L, -V*n+N, -v*qe*B+Fm}, {-v*dt+L, -dt*i+Q, -E*qe+Fe}, {-v*dt+L, -dt*i+Q, -v*qe*B+Fm}, {-v*dt+L, -E*qe+Fe, -v*qe*B+Fm}, {h, qe, -V*n+N}, {h, qe, -dt*i+Q}, {h, qe, -E*qe+Fe}, {h, qe, -v*qe*B+Fm}, {h, -V*n+N, -dt*i+Q}, {h, -V*n+N, -E*qe+Fe}, {h, -V*n+N, -v*qe*B+Fm}, {h, -dt*i+Q, -E*qe+Fe}, {h, -dt*i+Q, -v*qe*B+Fm}, {h, -E*qe+Fe, -v*qe*B+Fm}, {qe, -V*n+N, -dt*i+Q}, {qe, -V*n+N, -E*qe+Fe}, {qe, -V*n+N, -v*qe*B+Fm}, {qe, -dt*i+Q, -E*qe+Fe}, {qe, -dt*i+Q, -v*qe*B+Fm}, {qe, -E*qe+Fe, -v*qe*B+Fm}, {-V*n+N, -dt*i+Q, -E*qe+Fe}, {-V*n+N, -dt*i+Q, -v*qe*B+Fm}, {-V*n+N, -E*qe+Fe, -v*qe*B+Fm}, {-dt*i+Q, -E*qe+Fe, -v*qe*B+Fm}, {-v*dt+L, h, qe, -V*n+N}, {-v*dt+L, h, qe, -dt*i+Q}, {-v*dt+L, h, qe, -E*qe+Fe}, {-v*dt+L, h, qe, -v*qe*B+Fm}, {-v*dt+L, h, -V*n+N, -dt*i+Q}, {-v*dt+L, h, -V*n+N, -E*qe+Fe}, {-v*dt+L, h, -V*n+N, -v*qe*B+Fm}, {-v*dt+L, h, -dt*i+Q, -E*qe+Fe}, {-v*dt+L, h, -dt*i+Q, -v*qe*B+Fm}, {-v*dt+L, h, -E*qe+Fe, -v*qe*B+Fm}, {-v*dt+L, qe, -V*n+N, -dt*i+Q}, {-v*dt+L, qe, -V*n+N, -E*qe+Fe}, {-v*dt+L, qe, -V*n+N, -v*qe*B+Fm}, {-v*dt+L, qe, -dt*i+Q, -E*qe+Fe}, {-v*dt+L, qe, -dt*i+Q, -v*qe*B+Fm}, {-v*dt+L, qe, -E*qe+Fe, -v*qe*B+Fm}, {-v*dt+L, -V*n+N, -dt*i+Q, -E*qe+Fe}, {-v*dt+L, -V*n+N, -dt*i+Q, -v*qe*B+Fm}, {-v*dt+L, -V*n+N, -E*qe+Fe, -v*qe*B+Fm}, {-v*dt+L, -dt*i+Q, -E*qe+Fe, -v*qe*B+Fm}, {h, qe, -V*n+N, -dt*i+Q}, {h, qe, -V*n+N, -E*qe+Fe}, {h, qe, -V*n+N, -v*qe*B+Fm}, {h, qe, -dt*i+Q, -E*qe+Fe}, {h, qe, -dt*i+Q, -v*qe*B+Fm}, {h, qe, -E*qe+Fe, -v*qe*B+Fm}, {h, -V*n+N, -dt*i+Q, -E*qe+Fe}, {h, -V*n+N, -dt*i+Q, -v*qe*B+Fm}, {h, -V*n+N, -E*qe+Fe, -v*qe*B+Fm}, {h, -dt*i+Q, -E*qe+Fe, -v*qe*B+Fm}, {qe, -V*n+N, -dt*i+Q, -E*qe+Fe}, {qe, -V*n+N, -dt*i+Q, -v*qe*B+Fm}, {qe, -V*n+N, -E*qe+Fe, -v*qe*B+Fm}, {qe, -dt*i+Q, -E*qe+Fe, -v*qe*B+Fm}, {-V*n+N, -dt*i+Q, -E*qe+Fe, -v*qe*B+Fm}, {-v*dt+L}, {B}, {qe}, {-V*n+N}, {-dt*i+Q}, {-E*qe+Fe}, {-v*qe*B+Fm}, {-v*dt+L, B}, {-v*dt+L, qe}, {-v*dt+L, -V*n+N}, {-v*dt+L, -dt*i+Q}, {-v*dt+L, -E*qe+Fe}, {-v*dt+L, -v*qe*B+Fm}, {B, qe}, {B, -V*n+N}, {B, -dt*i+Q}, {B, -E*qe+Fe}, {B, -v*qe*B+Fm}, {qe, -V*n+N}, {qe, -dt*i+Q}, {qe, -E*qe+Fe}, {qe, -v*qe*B+Fm}, {-V*n+N, -dt*i+Q}, {-V*n+N, -E*qe+Fe}, {-V*n+N, -v*qe*B+Fm}, {-dt*i+Q, -E*qe+Fe}, {-dt*i+Q, -v*qe*B+Fm}, {-E*qe+Fe, -v*qe*B+Fm}, {-v*dt+L, B, qe}, {-v*dt+L, B, -V*n+N}, {-v*dt+L, B, -dt*i+Q}, {-v*dt+L, B, -E*qe+Fe}, {-v*dt+L, B, -v*qe*B+Fm}, {-v*dt+L, qe, -V*n+N}, {-v*dt+L, qe, -dt*i+Q}, {-v*dt+L, qe, -E*qe+Fe}, {-v*dt+L, qe, -v*qe*B+Fm}, {-v*dt+L, -V*n+N, -dt*i+Q}, {-v*dt+L, -V*n+N, -E*qe+Fe}, {-v*dt+L, -V*n+N, -v*qe*B+Fm}, {-v*dt+L, -dt*i+Q, -E*qe+Fe}, {-v*dt+L, -dt*i+Q, -v*qe*B+Fm}, {-v*dt+L, -E*qe+Fe, -v*qe*B+Fm}, {B, qe, -V*n+N}, {B, qe, -dt*i+Q}, {B, qe, -E*qe+Fe}, {B, qe, -v*qe*B+Fm}, {B, -V*n+N, -dt*i+Q}, {B, -V*n+N, -E*qe+Fe}, {B, -V*n+N, -v*qe*B+Fm}, {B, -dt*i+Q, -E*qe+Fe}, {B, -dt*i+Q, -v*qe*B+Fm}, {B, -E*qe+Fe, -v*qe*B+Fm}, {qe, -V*n+N, -dt*i+Q}, {qe, -V*n+N, -E*qe+Fe}, {qe, -V*n+N, -v*qe*B+Fm}, {qe, -dt*i+Q, -E*qe+Fe}, {qe, -dt*i+Q, -v*qe*B+Fm}, {qe, -E*qe+Fe, -v*qe*B+Fm}, {-V*n+N, -dt*i+Q, -E*qe+Fe}, {-V*n+N, -dt*i+Q, -v*qe*B+Fm}, {-V*n+N, -E*qe+Fe, -v*qe*B+Fm}, {-dt*i+Q, -E*qe+Fe, -v*qe*B+Fm}, {-v*dt+L, B, qe, -V*n+N}, {-v*dt+L, B, qe, -dt*i+Q}, {-v*dt+L, B, qe, -E*qe+Fe}, {-v*dt+L, B, qe, -v*qe*B+Fm}, {-v*dt+L, B, -V*n+N, -dt*i+Q}, {-v*dt+L, B, -V*n+N, -E*qe+Fe}, {-v*dt+L, B, -V*n+N, -v*qe*B+Fm}, {-v*dt+L, B, -dt*i+Q, -E*qe+Fe}, {-v*dt+L, B, -dt*i+Q, -v*qe*B+Fm}, {-v*dt+L, B, -E*qe+Fe, -v*qe*B+Fm}, {-v*dt+L, qe, -V*n+N, -dt*i+Q}, {-v*dt+L, qe, -V*n+N, -E*qe+Fe}, {-v*dt+L, qe, -V*n+N, -v*qe*B+Fm}, {-v*dt+L, qe, -dt*i+Q, -E*qe+Fe}, {-v*dt+L, qe, -dt*i+Q, -v*qe*B+Fm}, {-v*dt+L, qe, -E*qe+Fe, -v*qe*B+Fm}, {-v*dt+L, -V*n+N, -dt*i+Q, -E*qe+Fe}, {-v*dt+L, -V*n+N, -dt*i+Q, -v*qe*B+Fm}, {-v*dt+L, -V*n+N, -E*qe+Fe, -v*qe*B+Fm}, {-v*dt+L, -dt*i+Q, -E*qe+Fe, -v*qe*B+Fm}, {B, qe, -V*n+N, -dt*i+Q}, {B, qe, -V*n+N, -E*qe+Fe}, {B, qe, -V*n+N, -v*qe*B+Fm}, {B, qe, -dt*i+Q, -E*qe+Fe}, {B, qe, -dt*i+Q, -v*qe*B+Fm}, {B, qe, -E*qe+Fe, -v*qe*B+Fm}, {B, -V*n+N, -dt*i+Q, -E*qe+Fe}, {B, -V*n+N, -dt*i+Q, -v*qe*B+Fm}, {B, -V*n+N, -E*qe+Fe, -v*qe*B+Fm}, {B, -dt*i+Q, -E*qe+Fe, -v*qe*B+Fm}, {qe, -V*n+N, -dt*i+Q, -E*qe+Fe}, {qe, -V*n+N, -dt*i+Q, -v*qe*B+Fm}, {qe, -V*n+N, -E*qe+Fe, -v*qe*B+Fm}, {qe, -dt*i+Q, -E*qe+Fe, -v*qe*B+Fm}, {-V*n+N, -dt*i+Q, -E*qe+Fe, -v*qe*B+Fm}, {-v*dt+L}, {qe}, {i}, {-V*n+N}, {-dt*i+Q}, {-E*qe+Fe}, {-v*qe*B+Fm}, {-v*dt+L, qe}, {-v*dt+L, i}, {-v*dt+L, -V*n+N}, {-v*dt+L, -dt*i+Q}, {-v*dt+L, -E*qe+Fe}, {-v*dt+L, -v*qe*B+Fm}, {qe, i}, {qe, -V*n+N}, {qe, -dt*i+Q}, {qe, -E*qe+Fe}, {qe, -v*qe*B+Fm}, {i, -V*n+N}, {i, -dt*i+Q}, {i, -E*qe+Fe}, {i, -v*qe*B+Fm}, {-V*n+N, -dt*i+Q}, {-V*n+N, -E*qe+Fe}, {-V*n+N, -v*qe*B+Fm}, {-dt*i+Q, -E*qe+Fe}, {-dt*i+Q, -v*qe*B+Fm}, {-E*qe+Fe, -v*qe*B+Fm}, {-v*dt+L, qe, i}, {-v*dt+L, qe, -V*n+N}, {-v*dt+L, qe, -dt*i+Q}, {-v*dt+L, qe, -E*qe+Fe}, {-v*dt+L, qe, -v*qe*B+Fm}, {-v*dt+L, i, -V*n+N}, {-v*dt+L, i, -dt*i+Q}, {-v*dt+L, i, -E*qe+Fe}, {-v*dt+L, i, -v*qe*B+Fm}, {-v*dt+L, -V*n+N, -dt*i+Q}, {-v*dt+L, -V*n+N, -E*qe+Fe}, {-v*dt+L, -V*n+N, -v*qe*B+Fm}, {-v*dt+L, -dt*i+Q, -E*qe+Fe}, {-v*dt+L, -dt*i+Q, -v*qe*B+Fm}, {-v*dt+L, -E*qe+Fe, -v*qe*B+Fm}, {qe, i, -V*n+N}, {qe, i, -dt*i+Q}, {qe, i, -E*qe+Fe}, {qe, i, -v*qe*B+Fm}, {qe, -V*n+N, -dt*i+Q}, {qe, -V*n+N, -E*qe+Fe}, {qe, -V*n+N, -v*qe*B+Fm}, {qe, -dt*i+Q, -E*qe+Fe}, {qe, -dt*i+Q, -v*qe*B+Fm}, {qe, -E*qe+Fe, -v*qe*B+Fm}, {i, -V*n+N, -dt*i+Q}, {i, -V*n+N, -E*qe+Fe}, {i, -V*n+N, -v*qe*B+Fm}, {i, -dt*i+Q, -E*qe+Fe}, {i, -dt*i+Q, -v*qe*B+Fm}, {i, -E*qe+Fe, -v*qe*B+Fm}, {-V*n+N, -dt*i+Q, -E*qe+Fe}, {-V*n+N, -dt*i+Q, -v*qe*B+Fm}, {-V*n+N, -E*qe+Fe, -v*qe*B+Fm}, {-dt*i+Q, -E*qe+Fe, -v*qe*B+Fm}, {-v*dt+L, qe, i, -V*n+N}, {-v*dt+L, qe, i, -dt*i+Q}, {-v*dt+L, qe, i, -E*qe+Fe}, {-v*dt+L, qe, i, -v*qe*B+Fm}, {-v*dt+L, qe, -V*n+N, -dt*i+Q}, {-v*dt+L, qe, -V*n+N, -E*qe+Fe}, {-v*dt+L, qe, -V*n+N, -v*qe*B+Fm}, {-v*dt+L, qe, -dt*i+Q, -E*qe+Fe}, {-v*dt+L, qe, -dt*i+Q, -v*qe*B+Fm}, {-v*dt+L, qe, -E*qe+Fe, -v*qe*B+Fm}, {-v*dt+L, i, -V*n+N, -dt*i+Q}, {-v*dt+L, i, -V*n+N, -E*qe+Fe}, {-v*dt+L, i, -V*n+N, -v*qe*B+Fm}, {-v*dt+L, i, -dt*i+Q, -E*qe+Fe}, {-v*dt+L, i, -dt*i+Q, -v*qe*B+Fm}, {-v*dt+L, i, -E*qe+Fe, -v*qe*B+Fm}, {-v*dt+L, -V*n+N, -dt*i+Q, -E*qe+Fe}, {-v*dt+L, -V*n+N, -dt*i+Q, -v*qe*B+Fm}, {-v*dt+L, -V*n+N, -E*qe+Fe, -v*qe*B+Fm}, {-v*dt+L, -dt*i+Q, -E*qe+Fe, -v*qe*B+Fm}, {qe, i, -V*n+N, -dt*i+Q}, {qe, i, -V*n+N, -E*qe+Fe}, {qe, i, -V*n+N, -v*qe*B+Fm}, {qe, i, -dt*i+Q, -E*qe+Fe}, {qe, i, -dt*i+Q, -v*qe*B+Fm}, {qe, i, -E*qe+Fe, -v*qe*B+Fm}, {qe, -V*n+N, -dt*i+Q, -E*qe+Fe}, {qe, -V*n+N, -dt*i+Q, -v*qe*B+Fm}, {qe, -V*n+N, -E*qe+Fe, -v*qe*B+Fm}, {qe, -dt*i+Q, -E*qe+Fe, -v*qe*B+Fm}, {i, -V*n+N, -dt*i+Q, -E*qe+Fe}, {i, -V*n+N, -dt*i+Q, -v*qe*B+Fm}, {i, -V*n+N, -E*qe+Fe, -v*qe*B+Fm}, {i, -dt*i+Q, -E*qe+Fe, -v*qe*B+Fm}, {-V*n+N, -dt*i+Q, -E*qe+Fe, -v*qe*B+Fm}, {-v*dt+L}, {qe}, {-V*n+N}, {-dt*i+Q}, {dt}, {-E*qe+Fe}, {-v*qe*B+Fm}, {-v*dt+L, qe}, {-v*dt+L, -V*n+N}, {-v*dt+L, -dt*i+Q}, {-v*dt+L, dt}, {-v*dt+L, -E*qe+Fe}, {-v*dt+L, -v*qe*B+Fm}, {qe, -V*n+N}, {qe, -dt*i+Q}, {qe, dt}, {qe, -E*qe+Fe}, {qe, -v*qe*B+Fm}, {-V*n+N, -dt*i+Q}, {-V*n+N, dt}, {-V*n+N, -E*qe+Fe}, {-V*n+N, -v*qe*B+Fm}, {-dt*i+Q, dt}, {-dt*i+Q, -E*qe+Fe}, {-dt*i+Q, -v*qe*B+Fm}, {dt, -E*qe+Fe}, {dt, -v*qe*B+Fm}, {-E*qe+Fe, -v*qe*B+Fm}, {-v*dt+L, qe, -V*n+N}, {-v*dt+L, qe, -dt*i+Q}, {-v*dt+L, qe, dt}, {-v*dt+L, qe, -E*qe+Fe}, {-v*dt+L, qe, -v*qe*B+Fm}, {-v*dt+L, -V*n+N, -dt*i+Q}, {-v*dt+L, -V*n+N, dt}, {-v*dt+L, -V*n+N, -E*qe+Fe}, {-v*dt+L, -V*n+N, -v*qe*B+Fm}, {-v*dt+L, -dt*i+Q, dt}, {-v*dt+L, -dt*i+Q, -E*qe+Fe}, {-v*dt+L, -dt*i+Q, -v*qe*B+Fm}, {-v*dt+L, dt, -E*qe+Fe}, {-v*dt+L, dt, -v*qe*B+Fm}, {-v*dt+L, -E*qe+Fe, -v*qe*B+Fm}, {qe, -V*n+N, -dt*i+Q}, {qe, -V*n+N, dt}, {qe, -V*n+N, -E*qe+Fe}, {qe, -V*n+N, -v*qe*B+Fm}, {qe, -dt*i+Q, dt}, {qe, -dt*i+Q, -E*qe+Fe}, {qe, -dt*i+Q, -v*qe*B+Fm}, {qe, dt, -E*qe+Fe}, {qe, dt, -v*qe*B+Fm}, {qe, -E*qe+Fe, -v*qe*B+Fm}, {-V*n+N, -dt*i+Q, dt}, {-V*n+N, -dt*i+Q, -E*qe+Fe}, {-V*n+N, -dt*i+Q, -v*qe*B+Fm}, {-V*n+N, dt, -E*qe+Fe}, {-V*n+N, dt, -v*qe*B+Fm}, {-V*n+N, -E*qe+Fe, -v*qe*B+Fm}, {-dt*i+Q, dt, -E*qe+Fe}, {-dt*i+Q, dt, -v*qe*B+Fm}, {-dt*i+Q, -E*qe+Fe, -v*qe*B+Fm}, {dt, -E*qe+Fe, -v*qe*B+Fm}, {-v*dt+L, qe, -V*n+N, -dt*i+Q}, {-v*dt+L, qe, -V*n+N, dt}, {-v*dt+L, qe, -V*n+N, -E*qe+Fe}, {-v*dt+L, qe, -V*n+N, -v*qe*B+Fm}, {-v*dt+L, qe, -dt*i+Q, dt}, {-v*dt+L, qe, -dt*i+Q, -E*qe+Fe}, {-v*dt+L, qe, -dt*i+Q, -v*qe*B+Fm}, {-v*dt+L, qe, dt, -E*qe+Fe}, {-v*dt+L, qe, dt, -v*qe*B+Fm}, {-v*dt+L, qe, -E*qe+Fe, -v*qe*B+Fm}, {-v*dt+L, -V*n+N, -dt*i+Q, dt}, {-v*dt+L, -V*n+N, -dt*i+Q, -E*qe+Fe}, {-v*dt+L, -V*n+N, -dt*i+Q, -v*qe*B+Fm}, {-v*dt+L, -V*n+N, dt, -E*qe+Fe}, {-v*dt+L, -V*n+N, dt, -v*qe*B+Fm}, {-v*dt+L, -V*n+N, -E*qe+Fe, -v*qe*B+Fm}, {-v*dt+L, -dt*i+Q, dt, -E*qe+Fe}, {-v*dt+L, -dt*i+Q, dt, -v*qe*B+Fm}, {-v*dt+L, -dt*i+Q, -E*qe+Fe, -v*qe*B+Fm}, {-v*dt+L, dt, -E*qe+Fe, -v*qe*B+Fm}, {qe, -V*n+N, -dt*i+Q, dt}, {qe, -V*n+N, -dt*i+Q, -E*qe+Fe}, {qe, -V*n+N, -dt*i+Q, -v*qe*B+Fm}, {qe, -V*n+N, dt, -E*qe+Fe}, {qe, -V*n+N, dt, -v*qe*B+Fm}, {qe, -V*n+N, -E*qe+Fe, -v*qe*B+Fm}, {qe, -dt*i+Q, dt, -E*qe+Fe}, {qe, -dt*i+Q, dt, -v*qe*B+Fm}, {qe, -dt*i+Q, -E*qe+Fe, -v*qe*B+Fm}, {qe, dt, -E*qe+Fe, -v*qe*B+Fm}, {-V*n+N, -dt*i+Q, dt, -E*qe+Fe}, {-V*n+N, -dt*i+Q, dt, -v*qe*B+Fm}, {-V*n+N, -dt*i+Q, -E*qe+Fe, -v*qe*B+Fm}, {-V*n+N, dt, -E*qe+Fe, -v*qe*B+Fm}, {-dt*i+Q, dt, -E*qe+Fe, -v*qe*B+Fm}, {-v*dt+L}, {qe}, {-V*n+N}, {-dt*i+Q}, {-E*qe+Fe}, {v}, {-v*qe*B+Fm}, {-v*dt+L, qe}, {-v*dt+L, -V*n+N}, {-v*dt+L, -dt*i+Q}, {-v*dt+L, -E*qe+Fe}, {-v*dt+L, v}, {-v*dt+L, -v*qe*B+Fm}, {qe, -V*n+N}, {qe, -dt*i+Q}, {qe, -E*qe+Fe}, {qe, v}, {qe, -v*qe*B+Fm}, {-V*n+N, -dt*i+Q}, {-V*n+N, -E*qe+Fe}, {-V*n+N, v}, {-V*n+N, -v*qe*B+Fm}, {-dt*i+Q, -E*qe+Fe}, {-dt*i+Q, v}, {-dt*i+Q, -v*qe*B+Fm}, {-E*qe+Fe, v}, {-E*qe+Fe, -v*qe*B+Fm}, {v, -v*qe*B+Fm}, {-v*dt+L, qe, -V*n+N}, {-v*dt+L, qe, -dt*i+Q}, {-v*dt+L, qe, -E*qe+Fe}, {-v*dt+L, qe, v}, {-v*dt+L, qe, -v*qe*B+Fm}, {-v*dt+L, -V*n+N, -dt*i+Q}, {-v*dt+L, -V*n+N, -E*qe+Fe}, {-v*dt+L, -V*n+N, v}, {-v*dt+L, -V*n+N, -v*qe*B+Fm}, {-v*dt+L, -dt*i+Q, -E*qe+Fe}, {-v*dt+L, -dt*i+Q, v}, {-v*dt+L, -dt*i+Q, -v*qe*B+Fm}, {-v*dt+L, -E*qe+Fe, v}, {-v*dt+L, -E*qe+Fe, -v*qe*B+Fm}, {-v*dt+L, v, -v*qe*B+Fm}, {qe, -V*n+N, -dt*i+Q}, {qe, -V*n+N, -E*qe+Fe}, {qe, -V*n+N, v}, {qe, -V*n+N, -v*qe*B+Fm}, {qe, -dt*i+Q, -E*qe+Fe}, {qe, -dt*i+Q, v}, {qe, -dt*i+Q, -v*qe*B+Fm}, {qe, -E*qe+Fe, v}, {qe, -E*qe+Fe, -v*qe*B+Fm}, {qe, v, -v*qe*B+Fm}, {-V*n+N, -dt*i+Q, -E*qe+Fe}, {-V*n+N, -dt*i+Q, v}, {-V*n+N, -dt*i+Q, -v*qe*B+Fm}, {-V*n+N, -E*qe+Fe, v}, {-V*n+N, -E*qe+Fe, -v*qe*B+Fm}, {-V*n+N, v, -v*qe*B+Fm}, {-dt*i+Q, -E*qe+Fe, v}, {-dt*i+Q, -E*qe+Fe, -v*qe*B+Fm}, {-dt*i+Q, v, -v*qe*B+Fm}, {-E*qe+Fe, v, -v*qe*B+Fm}, {-v*dt+L, qe, -V*n+N, -dt*i+Q}, {-v*dt+L, qe, -V*n+N, -E*qe+Fe}, {-v*dt+L, qe, -V*n+N, v}, {-v*dt+L, qe, -V*n+N, -v*qe*B+Fm}, {-v*dt+L, qe, -dt*i+Q, -E*qe+Fe}, {-v*dt+L, qe, -dt*i+Q, v}, {-v*dt+L, qe, -dt*i+Q, -v*qe*B+Fm}, {-v*dt+L, qe, -E*qe+Fe, v}, {-v*dt+L, qe, -E*qe+Fe, -v*qe*B+Fm}, {-v*dt+L, qe, v, -v*qe*B+Fm}, {-v*dt+L, -V*n+N, -dt*i+Q, -E*qe+Fe}, {-v*dt+L, -V*n+N, -dt*i+Q, v}, {-v*dt+L, -V*n+N, -dt*i+Q, -v*qe*B+Fm}, {-v*dt+L, -V*n+N, -E*qe+Fe, v}, {-v*dt+L, -V*n+N, -E*qe+Fe, -v*qe*B+Fm}, {-v*dt+L, -V*n+N, v, -v*qe*B+Fm}, {-v*dt+L, -dt*i+Q, -E*qe+Fe, v}, {-v*dt+L, -dt*i+Q, -E*qe+Fe, -v*qe*B+Fm}, {-v*dt+L, -dt*i+Q, v, -v*qe*B+Fm}, {-v*dt+L, -E*qe+Fe, v, -v*qe*B+Fm}, {qe, -V*n+N, -dt*i+Q, -E*qe+Fe}, {qe, -V*n+N, -dt*i+Q, v}, {qe, -V*n+N, -dt*i+Q, -v*qe*B+Fm}, {qe, -V*n+N, -E*qe+Fe, v}, {qe, -V*n+N, -E*qe+Fe, -v*qe*B+Fm}, {qe, -V*n+N, v, -v*qe*B+Fm}, {qe, -dt*i+Q, -E*qe+Fe, v}, {qe, -dt*i+Q, -E*qe+Fe, -v*qe*B+Fm}, {qe, -dt*i+Q, v, -v*qe*B+Fm}, {qe, -E*qe+Fe, v, -v*qe*B+Fm}, {-V*n+N, -dt*i+Q, -E*qe+Fe, v}, {-V*n+N, -dt*i+Q, -E*qe+Fe, -v*qe*B+Fm}, {-V*n+N, -dt*i+Q, v, -v*qe*B+Fm}, {-V*n+N, -E*qe+Fe, v, -v*qe*B+Fm}, {-dt*i+Q, -E*qe+Fe, v, -v*qe*B+Fm}};

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
f = openOut "results/hall/abduction/noiseless/3_axiom(s)_removed/combo_4_7_9/reasoning/reasoning_output.txt";
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

print("Reasoning complete. Output written to results/hall/abduction/noiseless/3_axiom(s)_removed/combo_4_7_9/reasoning/reasoning_output.txt");
