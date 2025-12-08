-- AI-Noether: Reasoning Template (Noiseless)
-- Tests if candidate axiom sets, when added to remaining axioms, prove targets

needsPackage("PrimaryDecomposition", Reload => true)

-- Ring definition
R = QQ[Fm, d, v, Fe, E, dt, Q, N, V, i, n, qe, B, h, L, UH, MonomialOrder => Lex];

-- Input data
remainingAxioms = toList([Fm - qe*v*B, Fe - qe*E, Fm - Fe, E*h - UH, v*dt - L, Q - N*qe, n*V - N]);
qList = toList([N*qe*UH - i*B*h*L]);
k = #qList;

-- Per-target variable partitions
measuredPerTarget = {{UH, h, L, i, B, N, qe}};
nonMeasuredPerTarget = {{Fm, d, v, Fe, E, dt, Q, V, n}};

-- Candidate axiom sets to test (list of lists)
candidateSets = {{}, {v*B-E}, {-E*h+UH}, {-v*dt+L}, {h}, {-V*n+N}, {-N*qe+Q}, {-E*qe+Fe}, {-v*qe*B+Fm}, {v*B-E, -E*h+UH}, {v*B-E, -v*dt+L}, {v*B-E, h}, {v*B-E, -V*n+N}, {v*B-E, -N*qe+Q}, {v*B-E, -E*qe+Fe}, {v*B-E, -v*qe*B+Fm}, {-E*h+UH, -v*dt+L}, {-E*h+UH, h}, {-E*h+UH, -V*n+N}, {-E*h+UH, -N*qe+Q}, {-E*h+UH, -E*qe+Fe}, {-E*h+UH, -v*qe*B+Fm}, {-v*dt+L, h}, {-v*dt+L, -V*n+N}, {-v*dt+L, -N*qe+Q}, {-v*dt+L, -E*qe+Fe}, {-v*dt+L, -v*qe*B+Fm}, {h, -V*n+N}, {h, -N*qe+Q}, {h, -E*qe+Fe}, {h, -v*qe*B+Fm}, {-V*n+N, -N*qe+Q}, {-V*n+N, -E*qe+Fe}, {-V*n+N, -v*qe*B+Fm}, {-N*qe+Q, -E*qe+Fe}, {-N*qe+Q, -v*qe*B+Fm}, {-E*qe+Fe, -v*qe*B+Fm}, {v*B-E, -E*h+UH, -v*dt+L}, {v*B-E, -E*h+UH, h}, {v*B-E, -E*h+UH, -V*n+N}, {v*B-E, -E*h+UH, -N*qe+Q}, {v*B-E, -E*h+UH, -E*qe+Fe}, {v*B-E, -E*h+UH, -v*qe*B+Fm}, {v*B-E, -v*dt+L, h}, {v*B-E, -v*dt+L, -V*n+N}, {v*B-E, -v*dt+L, -N*qe+Q}, {v*B-E, -v*dt+L, -E*qe+Fe}, {v*B-E, -v*dt+L, -v*qe*B+Fm}, {v*B-E, h, -V*n+N}, {v*B-E, h, -N*qe+Q}, {v*B-E, h, -E*qe+Fe}, {v*B-E, h, -v*qe*B+Fm}, {v*B-E, -V*n+N, -N*qe+Q}, {v*B-E, -V*n+N, -E*qe+Fe}, {v*B-E, -V*n+N, -v*qe*B+Fm}, {v*B-E, -N*qe+Q, -E*qe+Fe}, {v*B-E, -N*qe+Q, -v*qe*B+Fm}, {v*B-E, -E*qe+Fe, -v*qe*B+Fm}, {-E*h+UH, -v*dt+L, h}, {-E*h+UH, -v*dt+L, -V*n+N}, {-E*h+UH, -v*dt+L, -N*qe+Q}, {-E*h+UH, -v*dt+L, -E*qe+Fe}, {-E*h+UH, -v*dt+L, -v*qe*B+Fm}, {-E*h+UH, h, -V*n+N}, {-E*h+UH, h, -N*qe+Q}, {-E*h+UH, h, -E*qe+Fe}, {-E*h+UH, h, -v*qe*B+Fm}, {-E*h+UH, -V*n+N, -N*qe+Q}, {-E*h+UH, -V*n+N, -E*qe+Fe}, {-E*h+UH, -V*n+N, -v*qe*B+Fm}, {-E*h+UH, -N*qe+Q, -E*qe+Fe}, {-E*h+UH, -N*qe+Q, -v*qe*B+Fm}, {-E*h+UH, -E*qe+Fe, -v*qe*B+Fm}, {-v*dt+L, h, -V*n+N}, {-v*dt+L, h, -N*qe+Q}, {-v*dt+L, h, -E*qe+Fe}, {-v*dt+L, h, -v*qe*B+Fm}, {-v*dt+L, -V*n+N, -N*qe+Q}, {-v*dt+L, -V*n+N, -E*qe+Fe}, {-v*dt+L, -V*n+N, -v*qe*B+Fm}, {-v*dt+L, -N*qe+Q, -E*qe+Fe}, {-v*dt+L, -N*qe+Q, -v*qe*B+Fm}, {-v*dt+L, -E*qe+Fe, -v*qe*B+Fm}, {h, -V*n+N, -N*qe+Q}, {h, -V*n+N, -E*qe+Fe}, {h, -V*n+N, -v*qe*B+Fm}, {h, -N*qe+Q, -E*qe+Fe}, {h, -N*qe+Q, -v*qe*B+Fm}, {h, -E*qe+Fe, -v*qe*B+Fm}, {-V*n+N, -N*qe+Q, -E*qe+Fe}, {-V*n+N, -N*qe+Q, -v*qe*B+Fm}, {-V*n+N, -E*qe+Fe, -v*qe*B+Fm}, {-N*qe+Q, -E*qe+Fe, -v*qe*B+Fm}, {-V*n*qe+dt*i}, {v*B-E}, {-E*h+UH}, {-v*dt+L}, {-V*n+N}, {-N*qe+Q}, {-E*qe+Fe}, {-v*qe*B+Fm}, {-V*n*qe+dt*i, v*B-E}, {-V*n*qe+dt*i, -E*h+UH}, {-V*n*qe+dt*i, -v*dt+L}, {-V*n*qe+dt*i, -V*n+N}, {-V*n*qe+dt*i, -N*qe+Q}, {-V*n*qe+dt*i, -E*qe+Fe}, {-V*n*qe+dt*i, -v*qe*B+Fm}, {v*B-E, -E*h+UH}, {v*B-E, -v*dt+L}, {v*B-E, -V*n+N}, {v*B-E, -N*qe+Q}, {v*B-E, -E*qe+Fe}, {v*B-E, -v*qe*B+Fm}, {-E*h+UH, -v*dt+L}, {-E*h+UH, -V*n+N}, {-E*h+UH, -N*qe+Q}, {-E*h+UH, -E*qe+Fe}, {-E*h+UH, -v*qe*B+Fm}, {-v*dt+L, -V*n+N}, {-v*dt+L, -N*qe+Q}, {-v*dt+L, -E*qe+Fe}, {-v*dt+L, -v*qe*B+Fm}, {-V*n+N, -N*qe+Q}, {-V*n+N, -E*qe+Fe}, {-V*n+N, -v*qe*B+Fm}, {-N*qe+Q, -E*qe+Fe}, {-N*qe+Q, -v*qe*B+Fm}, {-E*qe+Fe, -v*qe*B+Fm}, {-V*n*qe+dt*i, v*B-E, -E*h+UH}, {-V*n*qe+dt*i, v*B-E, -v*dt+L}, {-V*n*qe+dt*i, v*B-E, -V*n+N}, {-V*n*qe+dt*i, v*B-E, -N*qe+Q}, {-V*n*qe+dt*i, v*B-E, -E*qe+Fe}, {-V*n*qe+dt*i, v*B-E, -v*qe*B+Fm}, {-V*n*qe+dt*i, -E*h+UH, -v*dt+L}, {-V*n*qe+dt*i, -E*h+UH, -V*n+N}, {-V*n*qe+dt*i, -E*h+UH, -N*qe+Q}, {-V*n*qe+dt*i, -E*h+UH, -E*qe+Fe}, {-V*n*qe+dt*i, -E*h+UH, -v*qe*B+Fm}, {-V*n*qe+dt*i, -v*dt+L, -V*n+N}, {-V*n*qe+dt*i, -v*dt+L, -N*qe+Q}, {-V*n*qe+dt*i, -v*dt+L, -E*qe+Fe}, {-V*n*qe+dt*i, -v*dt+L, -v*qe*B+Fm}, {-V*n*qe+dt*i, -V*n+N, -N*qe+Q}, {-V*n*qe+dt*i, -V*n+N, -E*qe+Fe}, {-V*n*qe+dt*i, -V*n+N, -v*qe*B+Fm}, {-V*n*qe+dt*i, -N*qe+Q, -E*qe+Fe}, {-V*n*qe+dt*i, -N*qe+Q, -v*qe*B+Fm}, {-V*n*qe+dt*i, -E*qe+Fe, -v*qe*B+Fm}, {v*B-E, -E*h+UH, -v*dt+L}, {v*B-E, -E*h+UH, -V*n+N}, {v*B-E, -E*h+UH, -N*qe+Q}, {v*B-E, -E*h+UH, -E*qe+Fe}, {v*B-E, -E*h+UH, -v*qe*B+Fm}, {v*B-E, -v*dt+L, -V*n+N}, {v*B-E, -v*dt+L, -N*qe+Q}, {v*B-E, -v*dt+L, -E*qe+Fe}, {v*B-E, -v*dt+L, -v*qe*B+Fm}, {v*B-E, -V*n+N, -N*qe+Q}, {v*B-E, -V*n+N, -E*qe+Fe}, {v*B-E, -V*n+N, -v*qe*B+Fm}, {v*B-E, -N*qe+Q, -E*qe+Fe}, {v*B-E, -N*qe+Q, -v*qe*B+Fm}, {v*B-E, -E*qe+Fe, -v*qe*B+Fm}, {-E*h+UH, -v*dt+L, -V*n+N}, {-E*h+UH, -v*dt+L, -N*qe+Q}, {-E*h+UH, -v*dt+L, -E*qe+Fe}, {-E*h+UH, -v*dt+L, -v*qe*B+Fm}, {-E*h+UH, -V*n+N, -N*qe+Q}, {-E*h+UH, -V*n+N, -E*qe+Fe}, {-E*h+UH, -V*n+N, -v*qe*B+Fm}, {-E*h+UH, -N*qe+Q, -E*qe+Fe}, {-E*h+UH, -N*qe+Q, -v*qe*B+Fm}, {-E*h+UH, -E*qe+Fe, -v*qe*B+Fm}, {-v*dt+L, -V*n+N, -N*qe+Q}, {-v*dt+L, -V*n+N, -E*qe+Fe}, {-v*dt+L, -V*n+N, -v*qe*B+Fm}, {-v*dt+L, -N*qe+Q, -E*qe+Fe}, {-v*dt+L, -N*qe+Q, -v*qe*B+Fm}, {-v*dt+L, -E*qe+Fe, -v*qe*B+Fm}, {-V*n+N, -N*qe+Q, -E*qe+Fe}, {-V*n+N, -N*qe+Q, -v*qe*B+Fm}, {-V*n+N, -E*qe+Fe, -v*qe*B+Fm}, {-N*qe+Q, -E*qe+Fe, -v*qe*B+Fm}, {-E*h+UH}, {-v*dt+L}, {B}, {-V*n+N}, {-N*qe+Q}, {E}, {-E*qe+Fe}, {-v*qe*B+Fm}, {-E*h+UH, -v*dt+L}, {-E*h+UH, B}, {-E*h+UH, -V*n+N}, {-E*h+UH, -N*qe+Q}, {-E*h+UH, E}, {-E*h+UH, -E*qe+Fe}, {-E*h+UH, -v*qe*B+Fm}, {-v*dt+L, B}, {-v*dt+L, -V*n+N}, {-v*dt+L, -N*qe+Q}, {-v*dt+L, E}, {-v*dt+L, -E*qe+Fe}, {-v*dt+L, -v*qe*B+Fm}, {B, -V*n+N}, {B, -N*qe+Q}, {B, E}, {B, -E*qe+Fe}, {B, -v*qe*B+Fm}, {-V*n+N, -N*qe+Q}, {-V*n+N, E}, {-V*n+N, -E*qe+Fe}, {-V*n+N, -v*qe*B+Fm}, {-N*qe+Q, E}, {-N*qe+Q, -E*qe+Fe}, {-N*qe+Q, -v*qe*B+Fm}, {E, -E*qe+Fe}, {E, -v*qe*B+Fm}, {-E*qe+Fe, -v*qe*B+Fm}, {-E*h+UH, -v*dt+L, B}, {-E*h+UH, -v*dt+L, -V*n+N}, {-E*h+UH, -v*dt+L, -N*qe+Q}, {-E*h+UH, -v*dt+L, E}, {-E*h+UH, -v*dt+L, -E*qe+Fe}, {-E*h+UH, -v*dt+L, -v*qe*B+Fm}, {-E*h+UH, B, -V*n+N}, {-E*h+UH, B, -N*qe+Q}, {-E*h+UH, B, E}, {-E*h+UH, B, -E*qe+Fe}, {-E*h+UH, B, -v*qe*B+Fm}, {-E*h+UH, -V*n+N, -N*qe+Q}, {-E*h+UH, -V*n+N, E}, {-E*h+UH, -V*n+N, -E*qe+Fe}, {-E*h+UH, -V*n+N, -v*qe*B+Fm}, {-E*h+UH, -N*qe+Q, E}, {-E*h+UH, -N*qe+Q, -E*qe+Fe}, {-E*h+UH, -N*qe+Q, -v*qe*B+Fm}, {-E*h+UH, E, -E*qe+Fe}, {-E*h+UH, E, -v*qe*B+Fm}, {-E*h+UH, -E*qe+Fe, -v*qe*B+Fm}, {-v*dt+L, B, -V*n+N}, {-v*dt+L, B, -N*qe+Q}, {-v*dt+L, B, E}, {-v*dt+L, B, -E*qe+Fe}, {-v*dt+L, B, -v*qe*B+Fm}, {-v*dt+L, -V*n+N, -N*qe+Q}, {-v*dt+L, -V*n+N, E}, {-v*dt+L, -V*n+N, -E*qe+Fe}, {-v*dt+L, -V*n+N, -v*qe*B+Fm}, {-v*dt+L, -N*qe+Q, E}, {-v*dt+L, -N*qe+Q, -E*qe+Fe}, {-v*dt+L, -N*qe+Q, -v*qe*B+Fm}, {-v*dt+L, E, -E*qe+Fe}, {-v*dt+L, E, -v*qe*B+Fm}, {-v*dt+L, -E*qe+Fe, -v*qe*B+Fm}, {B, -V*n+N, -N*qe+Q}, {B, -V*n+N, E}, {B, -V*n+N, -E*qe+Fe}, {B, -V*n+N, -v*qe*B+Fm}, {B, -N*qe+Q, E}, {B, -N*qe+Q, -E*qe+Fe}, {B, -N*qe+Q, -v*qe*B+Fm}, {B, E, -E*qe+Fe}, {B, E, -v*qe*B+Fm}, {B, -E*qe+Fe, -v*qe*B+Fm}, {-V*n+N, -N*qe+Q, E}, {-V*n+N, -N*qe+Q, -E*qe+Fe}, {-V*n+N, -N*qe+Q, -v*qe*B+Fm}, {-V*n+N, E, -E*qe+Fe}, {-V*n+N, E, -v*qe*B+Fm}, {-V*n+N, -E*qe+Fe, -v*qe*B+Fm}, {-N*qe+Q, E, -E*qe+Fe}, {-N*qe+Q, E, -v*qe*B+Fm}, {-N*qe+Q, -E*qe+Fe, -v*qe*B+Fm}, {E, -E*qe+Fe, -v*qe*B+Fm}, {-E*h+UH}, {-v*dt+L}, {-V*n+N}, {-N*qe+Q}, {E}, {-E*qe+Fe}, {v}, {-v*qe*B+Fm}, {-E*h+UH, -v*dt+L}, {-E*h+UH, -V*n+N}, {-E*h+UH, -N*qe+Q}, {-E*h+UH, E}, {-E*h+UH, -E*qe+Fe}, {-E*h+UH, v}, {-E*h+UH, -v*qe*B+Fm}, {-v*dt+L, -V*n+N}, {-v*dt+L, -N*qe+Q}, {-v*dt+L, E}, {-v*dt+L, -E*qe+Fe}, {-v*dt+L, v}, {-v*dt+L, -v*qe*B+Fm}, {-V*n+N, -N*qe+Q}, {-V*n+N, E}, {-V*n+N, -E*qe+Fe}, {-V*n+N, v}, {-V*n+N, -v*qe*B+Fm}, {-N*qe+Q, E}, {-N*qe+Q, -E*qe+Fe}, {-N*qe+Q, v}, {-N*qe+Q, -v*qe*B+Fm}, {E, -E*qe+Fe}, {E, v}, {E, -v*qe*B+Fm}, {-E*qe+Fe, v}, {-E*qe+Fe, -v*qe*B+Fm}, {v, -v*qe*B+Fm}, {-E*h+UH, -v*dt+L, -V*n+N}, {-E*h+UH, -v*dt+L, -N*qe+Q}, {-E*h+UH, -v*dt+L, E}, {-E*h+UH, -v*dt+L, -E*qe+Fe}, {-E*h+UH, -v*dt+L, v}, {-E*h+UH, -v*dt+L, -v*qe*B+Fm}, {-E*h+UH, -V*n+N, -N*qe+Q}, {-E*h+UH, -V*n+N, E}, {-E*h+UH, -V*n+N, -E*qe+Fe}, {-E*h+UH, -V*n+N, v}, {-E*h+UH, -V*n+N, -v*qe*B+Fm}, {-E*h+UH, -N*qe+Q, E}, {-E*h+UH, -N*qe+Q, -E*qe+Fe}, {-E*h+UH, -N*qe+Q, v}, {-E*h+UH, -N*qe+Q, -v*qe*B+Fm}, {-E*h+UH, E, -E*qe+Fe}, {-E*h+UH, E, v}, {-E*h+UH, E, -v*qe*B+Fm}, {-E*h+UH, -E*qe+Fe, v}, {-E*h+UH, -E*qe+Fe, -v*qe*B+Fm}, {-E*h+UH, v, -v*qe*B+Fm}, {-v*dt+L, -V*n+N, -N*qe+Q}, {-v*dt+L, -V*n+N, E}, {-v*dt+L, -V*n+N, -E*qe+Fe}, {-v*dt+L, -V*n+N, v}, {-v*dt+L, -V*n+N, -v*qe*B+Fm}, {-v*dt+L, -N*qe+Q, E}, {-v*dt+L, -N*qe+Q, -E*qe+Fe}, {-v*dt+L, -N*qe+Q, v}, {-v*dt+L, -N*qe+Q, -v*qe*B+Fm}, {-v*dt+L, E, -E*qe+Fe}, {-v*dt+L, E, v}, {-v*dt+L, E, -v*qe*B+Fm}, {-v*dt+L, -E*qe+Fe, v}, {-v*dt+L, -E*qe+Fe, -v*qe*B+Fm}, {-v*dt+L, v, -v*qe*B+Fm}, {-V*n+N, -N*qe+Q, E}, {-V*n+N, -N*qe+Q, -E*qe+Fe}, {-V*n+N, -N*qe+Q, v}, {-V*n+N, -N*qe+Q, -v*qe*B+Fm}, {-V*n+N, E, -E*qe+Fe}, {-V*n+N, E, v}, {-V*n+N, E, -v*qe*B+Fm}, {-V*n+N, -E*qe+Fe, v}, {-V*n+N, -E*qe+Fe, -v*qe*B+Fm}, {-V*n+N, v, -v*qe*B+Fm}, {-N*qe+Q, E, -E*qe+Fe}, {-N*qe+Q, E, v}, {-N*qe+Q, E, -v*qe*B+Fm}, {-N*qe+Q, -E*qe+Fe, v}, {-N*qe+Q, -E*qe+Fe, -v*qe*B+Fm}, {-N*qe+Q, v, -v*qe*B+Fm}, {E, -E*qe+Fe, v}, {E, -E*qe+Fe, -v*qe*B+Fm}, {E, v, -v*qe*B+Fm}, {-E*qe+Fe, v, -v*qe*B+Fm}, {-E*h+UH}, {-v*dt+L}, {h}, {qe}, {-V*n+N}, {-N*qe+Q}, {-E*qe+Fe}, {-v*qe*B+Fm}, {-E*h+UH, -v*dt+L}, {-E*h+UH, h}, {-E*h+UH, qe}, {-E*h+UH, -V*n+N}, {-E*h+UH, -N*qe+Q}, {-E*h+UH, -E*qe+Fe}, {-E*h+UH, -v*qe*B+Fm}, {-v*dt+L, h}, {-v*dt+L, qe}, {-v*dt+L, -V*n+N}, {-v*dt+L, -N*qe+Q}, {-v*dt+L, -E*qe+Fe}, {-v*dt+L, -v*qe*B+Fm}, {h, qe}, {h, -V*n+N}, {h, -N*qe+Q}, {h, -E*qe+Fe}, {h, -v*qe*B+Fm}, {qe, -V*n+N}, {qe, -N*qe+Q}, {qe, -E*qe+Fe}, {qe, -v*qe*B+Fm}, {-V*n+N, -N*qe+Q}, {-V*n+N, -E*qe+Fe}, {-V*n+N, -v*qe*B+Fm}, {-N*qe+Q, -E*qe+Fe}, {-N*qe+Q, -v*qe*B+Fm}, {-E*qe+Fe, -v*qe*B+Fm}, {-E*h+UH, -v*dt+L, h}, {-E*h+UH, -v*dt+L, qe}, {-E*h+UH, -v*dt+L, -V*n+N}, {-E*h+UH, -v*dt+L, -N*qe+Q}, {-E*h+UH, -v*dt+L, -E*qe+Fe}, {-E*h+UH, -v*dt+L, -v*qe*B+Fm}, {-E*h+UH, h, qe}, {-E*h+UH, h, -V*n+N}, {-E*h+UH, h, -N*qe+Q}, {-E*h+UH, h, -E*qe+Fe}, {-E*h+UH, h, -v*qe*B+Fm}, {-E*h+UH, qe, -V*n+N}, {-E*h+UH, qe, -N*qe+Q}, {-E*h+UH, qe, -E*qe+Fe}, {-E*h+UH, qe, -v*qe*B+Fm}, {-E*h+UH, -V*n+N, -N*qe+Q}, {-E*h+UH, -V*n+N, -E*qe+Fe}, {-E*h+UH, -V*n+N, -v*qe*B+Fm}, {-E*h+UH, -N*qe+Q, -E*qe+Fe}, {-E*h+UH, -N*qe+Q, -v*qe*B+Fm}, {-E*h+UH, -E*qe+Fe, -v*qe*B+Fm}, {-v*dt+L, h, qe}, {-v*dt+L, h, -V*n+N}, {-v*dt+L, h, -N*qe+Q}, {-v*dt+L, h, -E*qe+Fe}, {-v*dt+L, h, -v*qe*B+Fm}, {-v*dt+L, qe, -V*n+N}, {-v*dt+L, qe, -N*qe+Q}, {-v*dt+L, qe, -E*qe+Fe}, {-v*dt+L, qe, -v*qe*B+Fm}, {-v*dt+L, -V*n+N, -N*qe+Q}, {-v*dt+L, -V*n+N, -E*qe+Fe}, {-v*dt+L, -V*n+N, -v*qe*B+Fm}, {-v*dt+L, -N*qe+Q, -E*qe+Fe}, {-v*dt+L, -N*qe+Q, -v*qe*B+Fm}, {-v*dt+L, -E*qe+Fe, -v*qe*B+Fm}, {h, qe, -V*n+N}, {h, qe, -N*qe+Q}, {h, qe, -E*qe+Fe}, {h, qe, -v*qe*B+Fm}, {h, -V*n+N, -N*qe+Q}, {h, -V*n+N, -E*qe+Fe}, {h, -V*n+N, -v*qe*B+Fm}, {h, -N*qe+Q, -E*qe+Fe}, {h, -N*qe+Q, -v*qe*B+Fm}, {h, -E*qe+Fe, -v*qe*B+Fm}, {qe, -V*n+N, -N*qe+Q}, {qe, -V*n+N, -E*qe+Fe}, {qe, -V*n+N, -v*qe*B+Fm}, {qe, -N*qe+Q, -E*qe+Fe}, {qe, -N*qe+Q, -v*qe*B+Fm}, {qe, -E*qe+Fe, -v*qe*B+Fm}, {-V*n+N, -N*qe+Q, -E*qe+Fe}, {-V*n+N, -N*qe+Q, -v*qe*B+Fm}, {-V*n+N, -E*qe+Fe, -v*qe*B+Fm}, {-N*qe+Q, -E*qe+Fe, -v*qe*B+Fm}, {-E*h+UH}, {-v*dt+L}, {B}, {qe}, {-V*n+N}, {-N*qe+Q}, {-E*qe+Fe}, {-v*qe*B+Fm}, {-E*h+UH, -v*dt+L}, {-E*h+UH, B}, {-E*h+UH, qe}, {-E*h+UH, -V*n+N}, {-E*h+UH, -N*qe+Q}, {-E*h+UH, -E*qe+Fe}, {-E*h+UH, -v*qe*B+Fm}, {-v*dt+L, B}, {-v*dt+L, qe}, {-v*dt+L, -V*n+N}, {-v*dt+L, -N*qe+Q}, {-v*dt+L, -E*qe+Fe}, {-v*dt+L, -v*qe*B+Fm}, {B, qe}, {B, -V*n+N}, {B, -N*qe+Q}, {B, -E*qe+Fe}, {B, -v*qe*B+Fm}, {qe, -V*n+N}, {qe, -N*qe+Q}, {qe, -E*qe+Fe}, {qe, -v*qe*B+Fm}, {-V*n+N, -N*qe+Q}, {-V*n+N, -E*qe+Fe}, {-V*n+N, -v*qe*B+Fm}, {-N*qe+Q, -E*qe+Fe}, {-N*qe+Q, -v*qe*B+Fm}, {-E*qe+Fe, -v*qe*B+Fm}, {-E*h+UH, -v*dt+L, B}, {-E*h+UH, -v*dt+L, qe}, {-E*h+UH, -v*dt+L, -V*n+N}, {-E*h+UH, -v*dt+L, -N*qe+Q}, {-E*h+UH, -v*dt+L, -E*qe+Fe}, {-E*h+UH, -v*dt+L, -v*qe*B+Fm}, {-E*h+UH, B, qe}, {-E*h+UH, B, -V*n+N}, {-E*h+UH, B, -N*qe+Q}, {-E*h+UH, B, -E*qe+Fe}, {-E*h+UH, B, -v*qe*B+Fm}, {-E*h+UH, qe, -V*n+N}, {-E*h+UH, qe, -N*qe+Q}, {-E*h+UH, qe, -E*qe+Fe}, {-E*h+UH, qe, -v*qe*B+Fm}, {-E*h+UH, -V*n+N, -N*qe+Q}, {-E*h+UH, -V*n+N, -E*qe+Fe}, {-E*h+UH, -V*n+N, -v*qe*B+Fm}, {-E*h+UH, -N*qe+Q, -E*qe+Fe}, {-E*h+UH, -N*qe+Q, -v*qe*B+Fm}, {-E*h+UH, -E*qe+Fe, -v*qe*B+Fm}, {-v*dt+L, B, qe}, {-v*dt+L, B, -V*n+N}, {-v*dt+L, B, -N*qe+Q}, {-v*dt+L, B, -E*qe+Fe}, {-v*dt+L, B, -v*qe*B+Fm}, {-v*dt+L, qe, -V*n+N}, {-v*dt+L, qe, -N*qe+Q}, {-v*dt+L, qe, -E*qe+Fe}, {-v*dt+L, qe, -v*qe*B+Fm}, {-v*dt+L, -V*n+N, -N*qe+Q}, {-v*dt+L, -V*n+N, -E*qe+Fe}, {-v*dt+L, -V*n+N, -v*qe*B+Fm}, {-v*dt+L, -N*qe+Q, -E*qe+Fe}, {-v*dt+L, -N*qe+Q, -v*qe*B+Fm}, {-v*dt+L, -E*qe+Fe, -v*qe*B+Fm}, {B, qe, -V*n+N}, {B, qe, -N*qe+Q}, {B, qe, -E*qe+Fe}, {B, qe, -v*qe*B+Fm}, {B, -V*n+N, -N*qe+Q}, {B, -V*n+N, -E*qe+Fe}, {B, -V*n+N, -v*qe*B+Fm}, {B, -N*qe+Q, -E*qe+Fe}, {B, -N*qe+Q, -v*qe*B+Fm}, {B, -E*qe+Fe, -v*qe*B+Fm}, {qe, -V*n+N, -N*qe+Q}, {qe, -V*n+N, -E*qe+Fe}, {qe, -V*n+N, -v*qe*B+Fm}, {qe, -N*qe+Q, -E*qe+Fe}, {qe, -N*qe+Q, -v*qe*B+Fm}, {qe, -E*qe+Fe, -v*qe*B+Fm}, {-V*n+N, -N*qe+Q, -E*qe+Fe}, {-V*n+N, -N*qe+Q, -v*qe*B+Fm}, {-V*n+N, -E*qe+Fe, -v*qe*B+Fm}, {-N*qe+Q, -E*qe+Fe, -v*qe*B+Fm}, {-E*h+UH}, {-v*dt+L}, {qe}, {i}, {-V*n+N}, {-N*qe+Q}, {-E*qe+Fe}, {-v*qe*B+Fm}, {-E*h+UH, -v*dt+L}, {-E*h+UH, qe}, {-E*h+UH, i}, {-E*h+UH, -V*n+N}, {-E*h+UH, -N*qe+Q}, {-E*h+UH, -E*qe+Fe}, {-E*h+UH, -v*qe*B+Fm}, {-v*dt+L, qe}, {-v*dt+L, i}, {-v*dt+L, -V*n+N}, {-v*dt+L, -N*qe+Q}, {-v*dt+L, -E*qe+Fe}, {-v*dt+L, -v*qe*B+Fm}, {qe, i}, {qe, -V*n+N}, {qe, -N*qe+Q}, {qe, -E*qe+Fe}, {qe, -v*qe*B+Fm}, {i, -V*n+N}, {i, -N*qe+Q}, {i, -E*qe+Fe}, {i, -v*qe*B+Fm}, {-V*n+N, -N*qe+Q}, {-V*n+N, -E*qe+Fe}, {-V*n+N, -v*qe*B+Fm}, {-N*qe+Q, -E*qe+Fe}, {-N*qe+Q, -v*qe*B+Fm}, {-E*qe+Fe, -v*qe*B+Fm}, {-E*h+UH, -v*dt+L, qe}, {-E*h+UH, -v*dt+L, i}, {-E*h+UH, -v*dt+L, -V*n+N}, {-E*h+UH, -v*dt+L, -N*qe+Q}, {-E*h+UH, -v*dt+L, -E*qe+Fe}, {-E*h+UH, -v*dt+L, -v*qe*B+Fm}, {-E*h+UH, qe, i}, {-E*h+UH, qe, -V*n+N}, {-E*h+UH, qe, -N*qe+Q}, {-E*h+UH, qe, -E*qe+Fe}, {-E*h+UH, qe, -v*qe*B+Fm}, {-E*h+UH, i, -V*n+N}, {-E*h+UH, i, -N*qe+Q}, {-E*h+UH, i, -E*qe+Fe}, {-E*h+UH, i, -v*qe*B+Fm}, {-E*h+UH, -V*n+N, -N*qe+Q}, {-E*h+UH, -V*n+N, -E*qe+Fe}, {-E*h+UH, -V*n+N, -v*qe*B+Fm}, {-E*h+UH, -N*qe+Q, -E*qe+Fe}, {-E*h+UH, -N*qe+Q, -v*qe*B+Fm}, {-E*h+UH, -E*qe+Fe, -v*qe*B+Fm}, {-v*dt+L, qe, i}, {-v*dt+L, qe, -V*n+N}, {-v*dt+L, qe, -N*qe+Q}, {-v*dt+L, qe, -E*qe+Fe}, {-v*dt+L, qe, -v*qe*B+Fm}, {-v*dt+L, i, -V*n+N}, {-v*dt+L, i, -N*qe+Q}, {-v*dt+L, i, -E*qe+Fe}, {-v*dt+L, i, -v*qe*B+Fm}, {-v*dt+L, -V*n+N, -N*qe+Q}, {-v*dt+L, -V*n+N, -E*qe+Fe}, {-v*dt+L, -V*n+N, -v*qe*B+Fm}, {-v*dt+L, -N*qe+Q, -E*qe+Fe}, {-v*dt+L, -N*qe+Q, -v*qe*B+Fm}, {-v*dt+L, -E*qe+Fe, -v*qe*B+Fm}, {qe, i, -V*n+N}, {qe, i, -N*qe+Q}, {qe, i, -E*qe+Fe}, {qe, i, -v*qe*B+Fm}, {qe, -V*n+N, -N*qe+Q}, {qe, -V*n+N, -E*qe+Fe}, {qe, -V*n+N, -v*qe*B+Fm}, {qe, -N*qe+Q, -E*qe+Fe}, {qe, -N*qe+Q, -v*qe*B+Fm}, {qe, -E*qe+Fe, -v*qe*B+Fm}, {i, -V*n+N, -N*qe+Q}, {i, -V*n+N, -E*qe+Fe}, {i, -V*n+N, -v*qe*B+Fm}, {i, -N*qe+Q, -E*qe+Fe}, {i, -N*qe+Q, -v*qe*B+Fm}, {i, -E*qe+Fe, -v*qe*B+Fm}, {-V*n+N, -N*qe+Q, -E*qe+Fe}, {-V*n+N, -N*qe+Q, -v*qe*B+Fm}, {-V*n+N, -E*qe+Fe, -v*qe*B+Fm}, {-N*qe+Q, -E*qe+Fe, -v*qe*B+Fm}, {-E*h+UH}, {-v*dt+L}, {qe}, {-V*n+N}, {-N*qe+Q}, {dt}, {-E*qe+Fe}, {-v*qe*B+Fm}, {-E*h+UH, -v*dt+L}, {-E*h+UH, qe}, {-E*h+UH, -V*n+N}, {-E*h+UH, -N*qe+Q}, {-E*h+UH, dt}, {-E*h+UH, -E*qe+Fe}, {-E*h+UH, -v*qe*B+Fm}, {-v*dt+L, qe}, {-v*dt+L, -V*n+N}, {-v*dt+L, -N*qe+Q}, {-v*dt+L, dt}, {-v*dt+L, -E*qe+Fe}, {-v*dt+L, -v*qe*B+Fm}, {qe, -V*n+N}, {qe, -N*qe+Q}, {qe, dt}, {qe, -E*qe+Fe}, {qe, -v*qe*B+Fm}, {-V*n+N, -N*qe+Q}, {-V*n+N, dt}, {-V*n+N, -E*qe+Fe}, {-V*n+N, -v*qe*B+Fm}, {-N*qe+Q, dt}, {-N*qe+Q, -E*qe+Fe}, {-N*qe+Q, -v*qe*B+Fm}, {dt, -E*qe+Fe}, {dt, -v*qe*B+Fm}, {-E*qe+Fe, -v*qe*B+Fm}, {-E*h+UH, -v*dt+L, qe}, {-E*h+UH, -v*dt+L, -V*n+N}, {-E*h+UH, -v*dt+L, -N*qe+Q}, {-E*h+UH, -v*dt+L, dt}, {-E*h+UH, -v*dt+L, -E*qe+Fe}, {-E*h+UH, -v*dt+L, -v*qe*B+Fm}, {-E*h+UH, qe, -V*n+N}, {-E*h+UH, qe, -N*qe+Q}, {-E*h+UH, qe, dt}, {-E*h+UH, qe, -E*qe+Fe}, {-E*h+UH, qe, -v*qe*B+Fm}, {-E*h+UH, -V*n+N, -N*qe+Q}, {-E*h+UH, -V*n+N, dt}, {-E*h+UH, -V*n+N, -E*qe+Fe}, {-E*h+UH, -V*n+N, -v*qe*B+Fm}, {-E*h+UH, -N*qe+Q, dt}, {-E*h+UH, -N*qe+Q, -E*qe+Fe}, {-E*h+UH, -N*qe+Q, -v*qe*B+Fm}, {-E*h+UH, dt, -E*qe+Fe}, {-E*h+UH, dt, -v*qe*B+Fm}, {-E*h+UH, -E*qe+Fe, -v*qe*B+Fm}, {-v*dt+L, qe, -V*n+N}, {-v*dt+L, qe, -N*qe+Q}, {-v*dt+L, qe, dt}, {-v*dt+L, qe, -E*qe+Fe}, {-v*dt+L, qe, -v*qe*B+Fm}, {-v*dt+L, -V*n+N, -N*qe+Q}, {-v*dt+L, -V*n+N, dt}, {-v*dt+L, -V*n+N, -E*qe+Fe}, {-v*dt+L, -V*n+N, -v*qe*B+Fm}, {-v*dt+L, -N*qe+Q, dt}, {-v*dt+L, -N*qe+Q, -E*qe+Fe}, {-v*dt+L, -N*qe+Q, -v*qe*B+Fm}, {-v*dt+L, dt, -E*qe+Fe}, {-v*dt+L, dt, -v*qe*B+Fm}, {-v*dt+L, -E*qe+Fe, -v*qe*B+Fm}, {qe, -V*n+N, -N*qe+Q}, {qe, -V*n+N, dt}, {qe, -V*n+N, -E*qe+Fe}, {qe, -V*n+N, -v*qe*B+Fm}, {qe, -N*qe+Q, dt}, {qe, -N*qe+Q, -E*qe+Fe}, {qe, -N*qe+Q, -v*qe*B+Fm}, {qe, dt, -E*qe+Fe}, {qe, dt, -v*qe*B+Fm}, {qe, -E*qe+Fe, -v*qe*B+Fm}, {-V*n+N, -N*qe+Q, dt}, {-V*n+N, -N*qe+Q, -E*qe+Fe}, {-V*n+N, -N*qe+Q, -v*qe*B+Fm}, {-V*n+N, dt, -E*qe+Fe}, {-V*n+N, dt, -v*qe*B+Fm}, {-V*n+N, -E*qe+Fe, -v*qe*B+Fm}, {-N*qe+Q, dt, -E*qe+Fe}, {-N*qe+Q, dt, -v*qe*B+Fm}, {-N*qe+Q, -E*qe+Fe, -v*qe*B+Fm}, {dt, -E*qe+Fe, -v*qe*B+Fm}, {-E*h+UH}, {-v*dt+L}, {qe}, {-V*n+N}, {-N*qe+Q}, {-E*qe+Fe}, {v}, {-v*qe*B+Fm}, {-E*h+UH, -v*dt+L}, {-E*h+UH, qe}, {-E*h+UH, -V*n+N}, {-E*h+UH, -N*qe+Q}, {-E*h+UH, -E*qe+Fe}, {-E*h+UH, v}, {-E*h+UH, -v*qe*B+Fm}, {-v*dt+L, qe}, {-v*dt+L, -V*n+N}, {-v*dt+L, -N*qe+Q}, {-v*dt+L, -E*qe+Fe}, {-v*dt+L, v}, {-v*dt+L, -v*qe*B+Fm}, {qe, -V*n+N}, {qe, -N*qe+Q}, {qe, -E*qe+Fe}, {qe, v}, {qe, -v*qe*B+Fm}, {-V*n+N, -N*qe+Q}, {-V*n+N, -E*qe+Fe}, {-V*n+N, v}, {-V*n+N, -v*qe*B+Fm}, {-N*qe+Q, -E*qe+Fe}, {-N*qe+Q, v}, {-N*qe+Q, -v*qe*B+Fm}, {-E*qe+Fe, v}, {-E*qe+Fe, -v*qe*B+Fm}, {v, -v*qe*B+Fm}, {-E*h+UH, -v*dt+L, qe}, {-E*h+UH, -v*dt+L, -V*n+N}, {-E*h+UH, -v*dt+L, -N*qe+Q}, {-E*h+UH, -v*dt+L, -E*qe+Fe}, {-E*h+UH, -v*dt+L, v}, {-E*h+UH, -v*dt+L, -v*qe*B+Fm}, {-E*h+UH, qe, -V*n+N}, {-E*h+UH, qe, -N*qe+Q}, {-E*h+UH, qe, -E*qe+Fe}, {-E*h+UH, qe, v}, {-E*h+UH, qe, -v*qe*B+Fm}, {-E*h+UH, -V*n+N, -N*qe+Q}, {-E*h+UH, -V*n+N, -E*qe+Fe}, {-E*h+UH, -V*n+N, v}, {-E*h+UH, -V*n+N, -v*qe*B+Fm}, {-E*h+UH, -N*qe+Q, -E*qe+Fe}, {-E*h+UH, -N*qe+Q, v}, {-E*h+UH, -N*qe+Q, -v*qe*B+Fm}, {-E*h+UH, -E*qe+Fe, v}, {-E*h+UH, -E*qe+Fe, -v*qe*B+Fm}, {-E*h+UH, v, -v*qe*B+Fm}, {-v*dt+L, qe, -V*n+N}, {-v*dt+L, qe, -N*qe+Q}, {-v*dt+L, qe, -E*qe+Fe}, {-v*dt+L, qe, v}, {-v*dt+L, qe, -v*qe*B+Fm}, {-v*dt+L, -V*n+N, -N*qe+Q}, {-v*dt+L, -V*n+N, -E*qe+Fe}, {-v*dt+L, -V*n+N, v}, {-v*dt+L, -V*n+N, -v*qe*B+Fm}, {-v*dt+L, -N*qe+Q, -E*qe+Fe}, {-v*dt+L, -N*qe+Q, v}, {-v*dt+L, -N*qe+Q, -v*qe*B+Fm}, {-v*dt+L, -E*qe+Fe, v}, {-v*dt+L, -E*qe+Fe, -v*qe*B+Fm}, {-v*dt+L, v, -v*qe*B+Fm}, {qe, -V*n+N, -N*qe+Q}, {qe, -V*n+N, -E*qe+Fe}, {qe, -V*n+N, v}, {qe, -V*n+N, -v*qe*B+Fm}, {qe, -N*qe+Q, -E*qe+Fe}, {qe, -N*qe+Q, v}, {qe, -N*qe+Q, -v*qe*B+Fm}, {qe, -E*qe+Fe, v}, {qe, -E*qe+Fe, -v*qe*B+Fm}, {qe, v, -v*qe*B+Fm}, {-V*n+N, -N*qe+Q, -E*qe+Fe}, {-V*n+N, -N*qe+Q, v}, {-V*n+N, -N*qe+Q, -v*qe*B+Fm}, {-V*n+N, -E*qe+Fe, v}, {-V*n+N, -E*qe+Fe, -v*qe*B+Fm}, {-V*n+N, v, -v*qe*B+Fm}, {-N*qe+Q, -E*qe+Fe, v}, {-N*qe+Q, -E*qe+Fe, -v*qe*B+Fm}, {-N*qe+Q, v, -v*qe*B+Fm}, {-E*qe+Fe, v, -v*qe*B+Fm}};

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
f = openOut "results/hall/abduction/noiseless/2_axiom(s)_removed/combo_6_9/reasoning/reasoning_output.txt";
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

print("Reasoning complete. Output written to results/hall/abduction/noiseless/2_axiom(s)_removed/combo_6_9/reasoning/reasoning_output.txt");
