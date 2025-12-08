-- AI-Noether: Reasoning Template (Noiseless)
-- Tests if candidate axiom sets, when added to remaining axioms, prove targets

needsPackage("PrimaryDecomposition", Reload => true)

-- Ring definition
R = QQ[Fm, d, v, Fe, E, dt, Q, N, V, i, n, qe, B, h, L, UH, MonomialOrder => Lex];

-- Input data
remainingAxioms = toList([Fm - qe*v*B, Fe - qe*E, Fm - Fe, E*h - UH, i*dt - Q, Q - N*qe, n*V - N]);
qList = toList([N*qe*UH - i*B*h*L]);
k = #qList;

-- Per-target variable partitions
measuredPerTarget = {{UH, h, L, i, B, N, qe}};
nonMeasuredPerTarget = {{Fm, d, v, Fe, E, dt, Q, V, n}};

-- Candidate axiom sets to test (list of lists)
candidateSets = {{}, {-V*n*qe+dt*i}, {E*V*n*qe-i*B*L}, {E*dt-B*L}, {v*B-E}, {v*V*n*qe-i*L}, {v*dt-L}, {-E*h+UH}, {-V*n+N}, {-dt*i+Q}, {-E*qe+Fe}, {-v*qe*B+Fm}, {-V*n*qe+dt*i, E*V*n*qe-i*B*L}, {-V*n*qe+dt*i, E*dt-B*L}, {-V*n*qe+dt*i, v*B-E}, {-V*n*qe+dt*i, v*V*n*qe-i*L}, {-V*n*qe+dt*i, v*dt-L}, {-V*n*qe+dt*i, -E*h+UH}, {-V*n*qe+dt*i, -V*n+N}, {-V*n*qe+dt*i, -dt*i+Q}, {-V*n*qe+dt*i, -E*qe+Fe}, {-V*n*qe+dt*i, -v*qe*B+Fm}, {E*V*n*qe-i*B*L, E*dt-B*L}, {E*V*n*qe-i*B*L, v*B-E}, {E*V*n*qe-i*B*L, v*V*n*qe-i*L}, {E*V*n*qe-i*B*L, v*dt-L}, {E*V*n*qe-i*B*L, -E*h+UH}, {E*V*n*qe-i*B*L, -V*n+N}, {E*V*n*qe-i*B*L, -dt*i+Q}, {E*V*n*qe-i*B*L, -E*qe+Fe}, {E*V*n*qe-i*B*L, -v*qe*B+Fm}, {E*dt-B*L, v*B-E}, {E*dt-B*L, v*V*n*qe-i*L}, {E*dt-B*L, v*dt-L}, {E*dt-B*L, -E*h+UH}, {E*dt-B*L, -V*n+N}, {E*dt-B*L, -dt*i+Q}, {E*dt-B*L, -E*qe+Fe}, {E*dt-B*L, -v*qe*B+Fm}, {v*B-E, v*V*n*qe-i*L}, {v*B-E, v*dt-L}, {v*B-E, -E*h+UH}, {v*B-E, -V*n+N}, {v*B-E, -dt*i+Q}, {v*B-E, -E*qe+Fe}, {v*B-E, -v*qe*B+Fm}, {v*V*n*qe-i*L, v*dt-L}, {v*V*n*qe-i*L, -E*h+UH}, {v*V*n*qe-i*L, -V*n+N}, {v*V*n*qe-i*L, -dt*i+Q}, {v*V*n*qe-i*L, -E*qe+Fe}, {v*V*n*qe-i*L, -v*qe*B+Fm}, {v*dt-L, -E*h+UH}, {v*dt-L, -V*n+N}, {v*dt-L, -dt*i+Q}, {v*dt-L, -E*qe+Fe}, {v*dt-L, -v*qe*B+Fm}, {-E*h+UH, -V*n+N}, {-E*h+UH, -dt*i+Q}, {-E*h+UH, -E*qe+Fe}, {-E*h+UH, -v*qe*B+Fm}, {-V*n+N, -dt*i+Q}, {-V*n+N, -E*qe+Fe}, {-V*n+N, -v*qe*B+Fm}, {-dt*i+Q, -E*qe+Fe}, {-dt*i+Q, -v*qe*B+Fm}, {-E*qe+Fe, -v*qe*B+Fm}, {-V*n*qe+dt*i, E*V*n*qe-i*B*L, E*dt-B*L}, {-V*n*qe+dt*i, E*V*n*qe-i*B*L, v*B-E}, {-V*n*qe+dt*i, E*V*n*qe-i*B*L, v*V*n*qe-i*L}, {-V*n*qe+dt*i, E*V*n*qe-i*B*L, v*dt-L}, {-V*n*qe+dt*i, E*V*n*qe-i*B*L, -E*h+UH}, {-V*n*qe+dt*i, E*V*n*qe-i*B*L, -V*n+N}, {-V*n*qe+dt*i, E*V*n*qe-i*B*L, -dt*i+Q}, {-V*n*qe+dt*i, E*V*n*qe-i*B*L, -E*qe+Fe}, {-V*n*qe+dt*i, E*V*n*qe-i*B*L, -v*qe*B+Fm}, {-V*n*qe+dt*i, E*dt-B*L, v*B-E}, {-V*n*qe+dt*i, E*dt-B*L, v*V*n*qe-i*L}, {-V*n*qe+dt*i, E*dt-B*L, v*dt-L}, {-V*n*qe+dt*i, E*dt-B*L, -E*h+UH}, {-V*n*qe+dt*i, E*dt-B*L, -V*n+N}, {-V*n*qe+dt*i, E*dt-B*L, -dt*i+Q}, {-V*n*qe+dt*i, E*dt-B*L, -E*qe+Fe}, {-V*n*qe+dt*i, E*dt-B*L, -v*qe*B+Fm}, {-V*n*qe+dt*i, v*B-E, v*V*n*qe-i*L}, {-V*n*qe+dt*i, v*B-E, v*dt-L}, {-V*n*qe+dt*i, v*B-E, -E*h+UH}, {-V*n*qe+dt*i, v*B-E, -V*n+N}, {-V*n*qe+dt*i, v*B-E, -dt*i+Q}, {-V*n*qe+dt*i, v*B-E, -E*qe+Fe}, {-V*n*qe+dt*i, v*B-E, -v*qe*B+Fm}, {-V*n*qe+dt*i, v*V*n*qe-i*L, v*dt-L}, {-V*n*qe+dt*i, v*V*n*qe-i*L, -E*h+UH}, {-V*n*qe+dt*i, v*V*n*qe-i*L, -V*n+N}, {-V*n*qe+dt*i, v*V*n*qe-i*L, -dt*i+Q}, {-V*n*qe+dt*i, v*V*n*qe-i*L, -E*qe+Fe}, {-V*n*qe+dt*i, v*V*n*qe-i*L, -v*qe*B+Fm}, {-V*n*qe+dt*i, v*dt-L, -E*h+UH}, {-V*n*qe+dt*i, v*dt-L, -V*n+N}, {-V*n*qe+dt*i, v*dt-L, -dt*i+Q}, {-V*n*qe+dt*i, v*dt-L, -E*qe+Fe}, {-V*n*qe+dt*i, v*dt-L, -v*qe*B+Fm}, {-V*n*qe+dt*i, -E*h+UH, -V*n+N}, {-V*n*qe+dt*i, -E*h+UH, -dt*i+Q}, {-V*n*qe+dt*i, -E*h+UH, -E*qe+Fe}, {-V*n*qe+dt*i, -E*h+UH, -v*qe*B+Fm}, {-V*n*qe+dt*i, -V*n+N, -dt*i+Q}, {-V*n*qe+dt*i, -V*n+N, -E*qe+Fe}, {-V*n*qe+dt*i, -V*n+N, -v*qe*B+Fm}, {-V*n*qe+dt*i, -dt*i+Q, -E*qe+Fe}, {-V*n*qe+dt*i, -dt*i+Q, -v*qe*B+Fm}, {-V*n*qe+dt*i, -E*qe+Fe, -v*qe*B+Fm}, {E*V*n*qe-i*B*L, E*dt-B*L, v*B-E}, {E*V*n*qe-i*B*L, E*dt-B*L, v*V*n*qe-i*L}, {E*V*n*qe-i*B*L, E*dt-B*L, v*dt-L}, {E*V*n*qe-i*B*L, E*dt-B*L, -E*h+UH}, {E*V*n*qe-i*B*L, E*dt-B*L, -V*n+N}, {E*V*n*qe-i*B*L, E*dt-B*L, -dt*i+Q}, {E*V*n*qe-i*B*L, E*dt-B*L, -E*qe+Fe}, {E*V*n*qe-i*B*L, E*dt-B*L, -v*qe*B+Fm}, {E*V*n*qe-i*B*L, v*B-E, v*V*n*qe-i*L}, {E*V*n*qe-i*B*L, v*B-E, v*dt-L}, {E*V*n*qe-i*B*L, v*B-E, -E*h+UH}, {E*V*n*qe-i*B*L, v*B-E, -V*n+N}, {E*V*n*qe-i*B*L, v*B-E, -dt*i+Q}, {E*V*n*qe-i*B*L, v*B-E, -E*qe+Fe}, {E*V*n*qe-i*B*L, v*B-E, -v*qe*B+Fm}, {E*V*n*qe-i*B*L, v*V*n*qe-i*L, v*dt-L}, {E*V*n*qe-i*B*L, v*V*n*qe-i*L, -E*h+UH}, {E*V*n*qe-i*B*L, v*V*n*qe-i*L, -V*n+N}, {E*V*n*qe-i*B*L, v*V*n*qe-i*L, -dt*i+Q}, {E*V*n*qe-i*B*L, v*V*n*qe-i*L, -E*qe+Fe}, {E*V*n*qe-i*B*L, v*V*n*qe-i*L, -v*qe*B+Fm}, {E*V*n*qe-i*B*L, v*dt-L, -E*h+UH}, {E*V*n*qe-i*B*L, v*dt-L, -V*n+N}, {E*V*n*qe-i*B*L, v*dt-L, -dt*i+Q}, {E*V*n*qe-i*B*L, v*dt-L, -E*qe+Fe}, {E*V*n*qe-i*B*L, v*dt-L, -v*qe*B+Fm}, {E*V*n*qe-i*B*L, -E*h+UH, -V*n+N}, {E*V*n*qe-i*B*L, -E*h+UH, -dt*i+Q}, {E*V*n*qe-i*B*L, -E*h+UH, -E*qe+Fe}, {E*V*n*qe-i*B*L, -E*h+UH, -v*qe*B+Fm}, {E*V*n*qe-i*B*L, -V*n+N, -dt*i+Q}, {E*V*n*qe-i*B*L, -V*n+N, -E*qe+Fe}, {E*V*n*qe-i*B*L, -V*n+N, -v*qe*B+Fm}, {E*V*n*qe-i*B*L, -dt*i+Q, -E*qe+Fe}, {E*V*n*qe-i*B*L, -dt*i+Q, -v*qe*B+Fm}, {E*V*n*qe-i*B*L, -E*qe+Fe, -v*qe*B+Fm}, {E*dt-B*L, v*B-E, v*V*n*qe-i*L}, {E*dt-B*L, v*B-E, v*dt-L}, {E*dt-B*L, v*B-E, -E*h+UH}, {E*dt-B*L, v*B-E, -V*n+N}, {E*dt-B*L, v*B-E, -dt*i+Q}, {E*dt-B*L, v*B-E, -E*qe+Fe}, {E*dt-B*L, v*B-E, -v*qe*B+Fm}, {E*dt-B*L, v*V*n*qe-i*L, v*dt-L}, {E*dt-B*L, v*V*n*qe-i*L, -E*h+UH}, {E*dt-B*L, v*V*n*qe-i*L, -V*n+N}, {E*dt-B*L, v*V*n*qe-i*L, -dt*i+Q}, {E*dt-B*L, v*V*n*qe-i*L, -E*qe+Fe}, {E*dt-B*L, v*V*n*qe-i*L, -v*qe*B+Fm}, {E*dt-B*L, v*dt-L, -E*h+UH}, {E*dt-B*L, v*dt-L, -V*n+N}, {E*dt-B*L, v*dt-L, -dt*i+Q}, {E*dt-B*L, v*dt-L, -E*qe+Fe}, {E*dt-B*L, v*dt-L, -v*qe*B+Fm}, {E*dt-B*L, -E*h+UH, -V*n+N}, {E*dt-B*L, -E*h+UH, -dt*i+Q}, {E*dt-B*L, -E*h+UH, -E*qe+Fe}, {E*dt-B*L, -E*h+UH, -v*qe*B+Fm}, {E*dt-B*L, -V*n+N, -dt*i+Q}, {E*dt-B*L, -V*n+N, -E*qe+Fe}, {E*dt-B*L, -V*n+N, -v*qe*B+Fm}, {E*dt-B*L, -dt*i+Q, -E*qe+Fe}, {E*dt-B*L, -dt*i+Q, -v*qe*B+Fm}, {E*dt-B*L, -E*qe+Fe, -v*qe*B+Fm}, {v*B-E, v*V*n*qe-i*L, v*dt-L}, {v*B-E, v*V*n*qe-i*L, -E*h+UH}, {v*B-E, v*V*n*qe-i*L, -V*n+N}, {v*B-E, v*V*n*qe-i*L, -dt*i+Q}, {v*B-E, v*V*n*qe-i*L, -E*qe+Fe}, {v*B-E, v*V*n*qe-i*L, -v*qe*B+Fm}, {v*B-E, v*dt-L, -E*h+UH}, {v*B-E, v*dt-L, -V*n+N}, {v*B-E, v*dt-L, -dt*i+Q}, {v*B-E, v*dt-L, -E*qe+Fe}, {v*B-E, v*dt-L, -v*qe*B+Fm}, {v*B-E, -E*h+UH, -V*n+N}, {v*B-E, -E*h+UH, -dt*i+Q}, {v*B-E, -E*h+UH, -E*qe+Fe}, {v*B-E, -E*h+UH, -v*qe*B+Fm}, {v*B-E, -V*n+N, -dt*i+Q}, {v*B-E, -V*n+N, -E*qe+Fe}, {v*B-E, -V*n+N, -v*qe*B+Fm}, {v*B-E, -dt*i+Q, -E*qe+Fe}, {v*B-E, -dt*i+Q, -v*qe*B+Fm}, {v*B-E, -E*qe+Fe, -v*qe*B+Fm}, {v*V*n*qe-i*L, v*dt-L, -E*h+UH}, {v*V*n*qe-i*L, v*dt-L, -V*n+N}, {v*V*n*qe-i*L, v*dt-L, -dt*i+Q}, {v*V*n*qe-i*L, v*dt-L, -E*qe+Fe}, {v*V*n*qe-i*L, v*dt-L, -v*qe*B+Fm}, {v*V*n*qe-i*L, -E*h+UH, -V*n+N}, {v*V*n*qe-i*L, -E*h+UH, -dt*i+Q}, {v*V*n*qe-i*L, -E*h+UH, -E*qe+Fe}, {v*V*n*qe-i*L, -E*h+UH, -v*qe*B+Fm}, {v*V*n*qe-i*L, -V*n+N, -dt*i+Q}, {v*V*n*qe-i*L, -V*n+N, -E*qe+Fe}, {v*V*n*qe-i*L, -V*n+N, -v*qe*B+Fm}, {v*V*n*qe-i*L, -dt*i+Q, -E*qe+Fe}, {v*V*n*qe-i*L, -dt*i+Q, -v*qe*B+Fm}, {v*V*n*qe-i*L, -E*qe+Fe, -v*qe*B+Fm}, {v*dt-L, -E*h+UH, -V*n+N}, {v*dt-L, -E*h+UH, -dt*i+Q}, {v*dt-L, -E*h+UH, -E*qe+Fe}, {v*dt-L, -E*h+UH, -v*qe*B+Fm}, {v*dt-L, -V*n+N, -dt*i+Q}, {v*dt-L, -V*n+N, -E*qe+Fe}, {v*dt-L, -V*n+N, -v*qe*B+Fm}, {v*dt-L, -dt*i+Q, -E*qe+Fe}, {v*dt-L, -dt*i+Q, -v*qe*B+Fm}, {v*dt-L, -E*qe+Fe, -v*qe*B+Fm}, {-E*h+UH, -V*n+N, -dt*i+Q}, {-E*h+UH, -V*n+N, -E*qe+Fe}, {-E*h+UH, -V*n+N, -v*qe*B+Fm}, {-E*h+UH, -dt*i+Q, -E*qe+Fe}, {-E*h+UH, -dt*i+Q, -v*qe*B+Fm}, {-E*h+UH, -E*qe+Fe, -v*qe*B+Fm}, {-V*n+N, -dt*i+Q, -E*qe+Fe}, {-V*n+N, -dt*i+Q, -v*qe*B+Fm}, {-V*n+N, -E*qe+Fe, -v*qe*B+Fm}, {-dt*i+Q, -E*qe+Fe, -v*qe*B+Fm}, {-V*n*qe+dt*i}, {-E*h+UH}, {B}, {-V*n+N}, {-dt*i+Q}, {E}, {-E*qe+Fe}, {-v*qe*B+Fm}, {-V*n*qe+dt*i, -E*h+UH}, {-V*n*qe+dt*i, B}, {-V*n*qe+dt*i, -V*n+N}, {-V*n*qe+dt*i, -dt*i+Q}, {-V*n*qe+dt*i, E}, {-V*n*qe+dt*i, -E*qe+Fe}, {-V*n*qe+dt*i, -v*qe*B+Fm}, {-E*h+UH, B}, {-E*h+UH, -V*n+N}, {-E*h+UH, -dt*i+Q}, {-E*h+UH, E}, {-E*h+UH, -E*qe+Fe}, {-E*h+UH, -v*qe*B+Fm}, {B, -V*n+N}, {B, -dt*i+Q}, {B, E}, {B, -E*qe+Fe}, {B, -v*qe*B+Fm}, {-V*n+N, -dt*i+Q}, {-V*n+N, E}, {-V*n+N, -E*qe+Fe}, {-V*n+N, -v*qe*B+Fm}, {-dt*i+Q, E}, {-dt*i+Q, -E*qe+Fe}, {-dt*i+Q, -v*qe*B+Fm}, {E, -E*qe+Fe}, {E, -v*qe*B+Fm}, {-E*qe+Fe, -v*qe*B+Fm}, {-V*n*qe+dt*i, -E*h+UH, B}, {-V*n*qe+dt*i, -E*h+UH, -V*n+N}, {-V*n*qe+dt*i, -E*h+UH, -dt*i+Q}, {-V*n*qe+dt*i, -E*h+UH, E}, {-V*n*qe+dt*i, -E*h+UH, -E*qe+Fe}, {-V*n*qe+dt*i, -E*h+UH, -v*qe*B+Fm}, {-V*n*qe+dt*i, B, -V*n+N}, {-V*n*qe+dt*i, B, -dt*i+Q}, {-V*n*qe+dt*i, B, E}, {-V*n*qe+dt*i, B, -E*qe+Fe}, {-V*n*qe+dt*i, B, -v*qe*B+Fm}, {-V*n*qe+dt*i, -V*n+N, -dt*i+Q}, {-V*n*qe+dt*i, -V*n+N, E}, {-V*n*qe+dt*i, -V*n+N, -E*qe+Fe}, {-V*n*qe+dt*i, -V*n+N, -v*qe*B+Fm}, {-V*n*qe+dt*i, -dt*i+Q, E}, {-V*n*qe+dt*i, -dt*i+Q, -E*qe+Fe}, {-V*n*qe+dt*i, -dt*i+Q, -v*qe*B+Fm}, {-V*n*qe+dt*i, E, -E*qe+Fe}, {-V*n*qe+dt*i, E, -v*qe*B+Fm}, {-V*n*qe+dt*i, -E*qe+Fe, -v*qe*B+Fm}, {-E*h+UH, B, -V*n+N}, {-E*h+UH, B, -dt*i+Q}, {-E*h+UH, B, E}, {-E*h+UH, B, -E*qe+Fe}, {-E*h+UH, B, -v*qe*B+Fm}, {-E*h+UH, -V*n+N, -dt*i+Q}, {-E*h+UH, -V*n+N, E}, {-E*h+UH, -V*n+N, -E*qe+Fe}, {-E*h+UH, -V*n+N, -v*qe*B+Fm}, {-E*h+UH, -dt*i+Q, E}, {-E*h+UH, -dt*i+Q, -E*qe+Fe}, {-E*h+UH, -dt*i+Q, -v*qe*B+Fm}, {-E*h+UH, E, -E*qe+Fe}, {-E*h+UH, E, -v*qe*B+Fm}, {-E*h+UH, -E*qe+Fe, -v*qe*B+Fm}, {B, -V*n+N, -dt*i+Q}, {B, -V*n+N, E}, {B, -V*n+N, -E*qe+Fe}, {B, -V*n+N, -v*qe*B+Fm}, {B, -dt*i+Q, E}, {B, -dt*i+Q, -E*qe+Fe}, {B, -dt*i+Q, -v*qe*B+Fm}, {B, E, -E*qe+Fe}, {B, E, -v*qe*B+Fm}, {B, -E*qe+Fe, -v*qe*B+Fm}, {-V*n+N, -dt*i+Q, E}, {-V*n+N, -dt*i+Q, -E*qe+Fe}, {-V*n+N, -dt*i+Q, -v*qe*B+Fm}, {-V*n+N, E, -E*qe+Fe}, {-V*n+N, E, -v*qe*B+Fm}, {-V*n+N, -E*qe+Fe, -v*qe*B+Fm}, {-dt*i+Q, E, -E*qe+Fe}, {-dt*i+Q, E, -v*qe*B+Fm}, {-dt*i+Q, -E*qe+Fe, -v*qe*B+Fm}, {E, -E*qe+Fe, -v*qe*B+Fm}, {-V*n*qe+dt*i}, {v*B-E}, {-E*h+UH}, {h}, {-V*n+N}, {-dt*i+Q}, {-E*qe+Fe}, {-v*qe*B+Fm}, {-V*n*qe+dt*i, v*B-E}, {-V*n*qe+dt*i, -E*h+UH}, {-V*n*qe+dt*i, h}, {-V*n*qe+dt*i, -V*n+N}, {-V*n*qe+dt*i, -dt*i+Q}, {-V*n*qe+dt*i, -E*qe+Fe}, {-V*n*qe+dt*i, -v*qe*B+Fm}, {v*B-E, -E*h+UH}, {v*B-E, h}, {v*B-E, -V*n+N}, {v*B-E, -dt*i+Q}, {v*B-E, -E*qe+Fe}, {v*B-E, -v*qe*B+Fm}, {-E*h+UH, h}, {-E*h+UH, -V*n+N}, {-E*h+UH, -dt*i+Q}, {-E*h+UH, -E*qe+Fe}, {-E*h+UH, -v*qe*B+Fm}, {h, -V*n+N}, {h, -dt*i+Q}, {h, -E*qe+Fe}, {h, -v*qe*B+Fm}, {-V*n+N, -dt*i+Q}, {-V*n+N, -E*qe+Fe}, {-V*n+N, -v*qe*B+Fm}, {-dt*i+Q, -E*qe+Fe}, {-dt*i+Q, -v*qe*B+Fm}, {-E*qe+Fe, -v*qe*B+Fm}, {-V*n*qe+dt*i, v*B-E, -E*h+UH}, {-V*n*qe+dt*i, v*B-E, h}, {-V*n*qe+dt*i, v*B-E, -V*n+N}, {-V*n*qe+dt*i, v*B-E, -dt*i+Q}, {-V*n*qe+dt*i, v*B-E, -E*qe+Fe}, {-V*n*qe+dt*i, v*B-E, -v*qe*B+Fm}, {-V*n*qe+dt*i, -E*h+UH, h}, {-V*n*qe+dt*i, -E*h+UH, -V*n+N}, {-V*n*qe+dt*i, -E*h+UH, -dt*i+Q}, {-V*n*qe+dt*i, -E*h+UH, -E*qe+Fe}, {-V*n*qe+dt*i, -E*h+UH, -v*qe*B+Fm}, {-V*n*qe+dt*i, h, -V*n+N}, {-V*n*qe+dt*i, h, -dt*i+Q}, {-V*n*qe+dt*i, h, -E*qe+Fe}, {-V*n*qe+dt*i, h, -v*qe*B+Fm}, {-V*n*qe+dt*i, -V*n+N, -dt*i+Q}, {-V*n*qe+dt*i, -V*n+N, -E*qe+Fe}, {-V*n*qe+dt*i, -V*n+N, -v*qe*B+Fm}, {-V*n*qe+dt*i, -dt*i+Q, -E*qe+Fe}, {-V*n*qe+dt*i, -dt*i+Q, -v*qe*B+Fm}, {-V*n*qe+dt*i, -E*qe+Fe, -v*qe*B+Fm}, {v*B-E, -E*h+UH, h}, {v*B-E, -E*h+UH, -V*n+N}, {v*B-E, -E*h+UH, -dt*i+Q}, {v*B-E, -E*h+UH, -E*qe+Fe}, {v*B-E, -E*h+UH, -v*qe*B+Fm}, {v*B-E, h, -V*n+N}, {v*B-E, h, -dt*i+Q}, {v*B-E, h, -E*qe+Fe}, {v*B-E, h, -v*qe*B+Fm}, {v*B-E, -V*n+N, -dt*i+Q}, {v*B-E, -V*n+N, -E*qe+Fe}, {v*B-E, -V*n+N, -v*qe*B+Fm}, {v*B-E, -dt*i+Q, -E*qe+Fe}, {v*B-E, -dt*i+Q, -v*qe*B+Fm}, {v*B-E, -E*qe+Fe, -v*qe*B+Fm}, {-E*h+UH, h, -V*n+N}, {-E*h+UH, h, -dt*i+Q}, {-E*h+UH, h, -E*qe+Fe}, {-E*h+UH, h, -v*qe*B+Fm}, {-E*h+UH, -V*n+N, -dt*i+Q}, {-E*h+UH, -V*n+N, -E*qe+Fe}, {-E*h+UH, -V*n+N, -v*qe*B+Fm}, {-E*h+UH, -dt*i+Q, -E*qe+Fe}, {-E*h+UH, -dt*i+Q, -v*qe*B+Fm}, {-E*h+UH, -E*qe+Fe, -v*qe*B+Fm}, {h, -V*n+N, -dt*i+Q}, {h, -V*n+N, -E*qe+Fe}, {h, -V*n+N, -v*qe*B+Fm}, {h, -dt*i+Q, -E*qe+Fe}, {h, -dt*i+Q, -v*qe*B+Fm}, {h, -E*qe+Fe, -v*qe*B+Fm}, {-V*n+N, -dt*i+Q, -E*qe+Fe}, {-V*n+N, -dt*i+Q, -v*qe*B+Fm}, {-V*n+N, -E*qe+Fe, -v*qe*B+Fm}, {-dt*i+Q, -E*qe+Fe, -v*qe*B+Fm}, {v*B-E}, {-E*h+UH}, {n}, {i}, {-V*n+N}, {-dt*i+Q}, {-E*qe+Fe}, {-v*qe*B+Fm}, {v*B-E, -E*h+UH}, {v*B-E, n}, {v*B-E, i}, {v*B-E, -V*n+N}, {v*B-E, -dt*i+Q}, {v*B-E, -E*qe+Fe}, {v*B-E, -v*qe*B+Fm}, {-E*h+UH, n}, {-E*h+UH, i}, {-E*h+UH, -V*n+N}, {-E*h+UH, -dt*i+Q}, {-E*h+UH, -E*qe+Fe}, {-E*h+UH, -v*qe*B+Fm}, {n, i}, {n, -V*n+N}, {n, -dt*i+Q}, {n, -E*qe+Fe}, {n, -v*qe*B+Fm}, {i, -V*n+N}, {i, -dt*i+Q}, {i, -E*qe+Fe}, {i, -v*qe*B+Fm}, {-V*n+N, -dt*i+Q}, {-V*n+N, -E*qe+Fe}, {-V*n+N, -v*qe*B+Fm}, {-dt*i+Q, -E*qe+Fe}, {-dt*i+Q, -v*qe*B+Fm}, {-E*qe+Fe, -v*qe*B+Fm}, {v*B-E, -E*h+UH, n}, {v*B-E, -E*h+UH, i}, {v*B-E, -E*h+UH, -V*n+N}, {v*B-E, -E*h+UH, -dt*i+Q}, {v*B-E, -E*h+UH, -E*qe+Fe}, {v*B-E, -E*h+UH, -v*qe*B+Fm}, {v*B-E, n, i}, {v*B-E, n, -V*n+N}, {v*B-E, n, -dt*i+Q}, {v*B-E, n, -E*qe+Fe}, {v*B-E, n, -v*qe*B+Fm}, {v*B-E, i, -V*n+N}, {v*B-E, i, -dt*i+Q}, {v*B-E, i, -E*qe+Fe}, {v*B-E, i, -v*qe*B+Fm}, {v*B-E, -V*n+N, -dt*i+Q}, {v*B-E, -V*n+N, -E*qe+Fe}, {v*B-E, -V*n+N, -v*qe*B+Fm}, {v*B-E, -dt*i+Q, -E*qe+Fe}, {v*B-E, -dt*i+Q, -v*qe*B+Fm}, {v*B-E, -E*qe+Fe, -v*qe*B+Fm}, {-E*h+UH, n, i}, {-E*h+UH, n, -V*n+N}, {-E*h+UH, n, -dt*i+Q}, {-E*h+UH, n, -E*qe+Fe}, {-E*h+UH, n, -v*qe*B+Fm}, {-E*h+UH, i, -V*n+N}, {-E*h+UH, i, -dt*i+Q}, {-E*h+UH, i, -E*qe+Fe}, {-E*h+UH, i, -v*qe*B+Fm}, {-E*h+UH, -V*n+N, -dt*i+Q}, {-E*h+UH, -V*n+N, -E*qe+Fe}, {-E*h+UH, -V*n+N, -v*qe*B+Fm}, {-E*h+UH, -dt*i+Q, -E*qe+Fe}, {-E*h+UH, -dt*i+Q, -v*qe*B+Fm}, {-E*h+UH, -E*qe+Fe, -v*qe*B+Fm}, {n, i, -V*n+N}, {n, i, -dt*i+Q}, {n, i, -E*qe+Fe}, {n, i, -v*qe*B+Fm}, {n, -V*n+N, -dt*i+Q}, {n, -V*n+N, -E*qe+Fe}, {n, -V*n+N, -v*qe*B+Fm}, {n, -dt*i+Q, -E*qe+Fe}, {n, -dt*i+Q, -v*qe*B+Fm}, {n, -E*qe+Fe, -v*qe*B+Fm}, {i, -V*n+N, -dt*i+Q}, {i, -V*n+N, -E*qe+Fe}, {i, -V*n+N, -v*qe*B+Fm}, {i, -dt*i+Q, -E*qe+Fe}, {i, -dt*i+Q, -v*qe*B+Fm}, {i, -E*qe+Fe, -v*qe*B+Fm}, {-V*n+N, -dt*i+Q, -E*qe+Fe}, {-V*n+N, -dt*i+Q, -v*qe*B+Fm}, {-V*n+N, -E*qe+Fe, -v*qe*B+Fm}, {-dt*i+Q, -E*qe+Fe, -v*qe*B+Fm}, {v*B-E}, {-E*h+UH}, {i}, {V}, {-V*n+N}, {-dt*i+Q}, {-E*qe+Fe}, {-v*qe*B+Fm}, {v*B-E, -E*h+UH}, {v*B-E, i}, {v*B-E, V}, {v*B-E, -V*n+N}, {v*B-E, -dt*i+Q}, {v*B-E, -E*qe+Fe}, {v*B-E, -v*qe*B+Fm}, {-E*h+UH, i}, {-E*h+UH, V}, {-E*h+UH, -V*n+N}, {-E*h+UH, -dt*i+Q}, {-E*h+UH, -E*qe+Fe}, {-E*h+UH, -v*qe*B+Fm}, {i, V}, {i, -V*n+N}, {i, -dt*i+Q}, {i, -E*qe+Fe}, {i, -v*qe*B+Fm}, {V, -V*n+N}, {V, -dt*i+Q}, {V, -E*qe+Fe}, {V, -v*qe*B+Fm}, {-V*n+N, -dt*i+Q}, {-V*n+N, -E*qe+Fe}, {-V*n+N, -v*qe*B+Fm}, {-dt*i+Q, -E*qe+Fe}, {-dt*i+Q, -v*qe*B+Fm}, {-E*qe+Fe, -v*qe*B+Fm}, {v*B-E, -E*h+UH, i}, {v*B-E, -E*h+UH, V}, {v*B-E, -E*h+UH, -V*n+N}, {v*B-E, -E*h+UH, -dt*i+Q}, {v*B-E, -E*h+UH, -E*qe+Fe}, {v*B-E, -E*h+UH, -v*qe*B+Fm}, {v*B-E, i, V}, {v*B-E, i, -V*n+N}, {v*B-E, i, -dt*i+Q}, {v*B-E, i, -E*qe+Fe}, {v*B-E, i, -v*qe*B+Fm}, {v*B-E, V, -V*n+N}, {v*B-E, V, -dt*i+Q}, {v*B-E, V, -E*qe+Fe}, {v*B-E, V, -v*qe*B+Fm}, {v*B-E, -V*n+N, -dt*i+Q}, {v*B-E, -V*n+N, -E*qe+Fe}, {v*B-E, -V*n+N, -v*qe*B+Fm}, {v*B-E, -dt*i+Q, -E*qe+Fe}, {v*B-E, -dt*i+Q, -v*qe*B+Fm}, {v*B-E, -E*qe+Fe, -v*qe*B+Fm}, {-E*h+UH, i, V}, {-E*h+UH, i, -V*n+N}, {-E*h+UH, i, -dt*i+Q}, {-E*h+UH, i, -E*qe+Fe}, {-E*h+UH, i, -v*qe*B+Fm}, {-E*h+UH, V, -V*n+N}, {-E*h+UH, V, -dt*i+Q}, {-E*h+UH, V, -E*qe+Fe}, {-E*h+UH, V, -v*qe*B+Fm}, {-E*h+UH, -V*n+N, -dt*i+Q}, {-E*h+UH, -V*n+N, -E*qe+Fe}, {-E*h+UH, -V*n+N, -v*qe*B+Fm}, {-E*h+UH, -dt*i+Q, -E*qe+Fe}, {-E*h+UH, -dt*i+Q, -v*qe*B+Fm}, {-E*h+UH, -E*qe+Fe, -v*qe*B+Fm}, {i, V, -V*n+N}, {i, V, -dt*i+Q}, {i, V, -E*qe+Fe}, {i, V, -v*qe*B+Fm}, {i, -V*n+N, -dt*i+Q}, {i, -V*n+N, -E*qe+Fe}, {i, -V*n+N, -v*qe*B+Fm}, {i, -dt*i+Q, -E*qe+Fe}, {i, -dt*i+Q, -v*qe*B+Fm}, {i, -E*qe+Fe, -v*qe*B+Fm}, {V, -V*n+N, -dt*i+Q}, {V, -V*n+N, -E*qe+Fe}, {V, -V*n+N, -v*qe*B+Fm}, {V, -dt*i+Q, -E*qe+Fe}, {V, -dt*i+Q, -v*qe*B+Fm}, {V, -E*qe+Fe, -v*qe*B+Fm}, {-V*n+N, -dt*i+Q, -E*qe+Fe}, {-V*n+N, -dt*i+Q, -v*qe*B+Fm}, {-V*n+N, -E*qe+Fe, -v*qe*B+Fm}, {-dt*i+Q, -E*qe+Fe, -v*qe*B+Fm}, {-E*h+UH}, {qe}, {i}, {-V*n+N}, {-dt*i+Q}, {-E*qe+Fe}, {-v*qe*B+Fm}, {-E*h+UH, qe}, {-E*h+UH, i}, {-E*h+UH, -V*n+N}, {-E*h+UH, -dt*i+Q}, {-E*h+UH, -E*qe+Fe}, {-E*h+UH, -v*qe*B+Fm}, {qe, i}, {qe, -V*n+N}, {qe, -dt*i+Q}, {qe, -E*qe+Fe}, {qe, -v*qe*B+Fm}, {i, -V*n+N}, {i, -dt*i+Q}, {i, -E*qe+Fe}, {i, -v*qe*B+Fm}, {-V*n+N, -dt*i+Q}, {-V*n+N, -E*qe+Fe}, {-V*n+N, -v*qe*B+Fm}, {-dt*i+Q, -E*qe+Fe}, {-dt*i+Q, -v*qe*B+Fm}, {-E*qe+Fe, -v*qe*B+Fm}, {-E*h+UH, qe, i}, {-E*h+UH, qe, -V*n+N}, {-E*h+UH, qe, -dt*i+Q}, {-E*h+UH, qe, -E*qe+Fe}, {-E*h+UH, qe, -v*qe*B+Fm}, {-E*h+UH, i, -V*n+N}, {-E*h+UH, i, -dt*i+Q}, {-E*h+UH, i, -E*qe+Fe}, {-E*h+UH, i, -v*qe*B+Fm}, {-E*h+UH, -V*n+N, -dt*i+Q}, {-E*h+UH, -V*n+N, -E*qe+Fe}, {-E*h+UH, -V*n+N, -v*qe*B+Fm}, {-E*h+UH, -dt*i+Q, -E*qe+Fe}, {-E*h+UH, -dt*i+Q, -v*qe*B+Fm}, {-E*h+UH, -E*qe+Fe, -v*qe*B+Fm}, {qe, i, -V*n+N}, {qe, i, -dt*i+Q}, {qe, i, -E*qe+Fe}, {qe, i, -v*qe*B+Fm}, {qe, -V*n+N, -dt*i+Q}, {qe, -V*n+N, -E*qe+Fe}, {qe, -V*n+N, -v*qe*B+Fm}, {qe, -dt*i+Q, -E*qe+Fe}, {qe, -dt*i+Q, -v*qe*B+Fm}, {qe, -E*qe+Fe, -v*qe*B+Fm}, {i, -V*n+N, -dt*i+Q}, {i, -V*n+N, -E*qe+Fe}, {i, -V*n+N, -v*qe*B+Fm}, {i, -dt*i+Q, -E*qe+Fe}, {i, -dt*i+Q, -v*qe*B+Fm}, {i, -E*qe+Fe, -v*qe*B+Fm}, {-V*n+N, -dt*i+Q, -E*qe+Fe}, {-V*n+N, -dt*i+Q, -v*qe*B+Fm}, {-V*n+N, -E*qe+Fe, -v*qe*B+Fm}, {-dt*i+Q, -E*qe+Fe, -v*qe*B+Fm}, {-E*h+UH}, {L}, {qe}, {-V*n+N}, {-dt*i+Q}, {dt}, {-E*qe+Fe}, {-v*qe*B+Fm}, {-E*h+UH, L}, {-E*h+UH, qe}, {-E*h+UH, -V*n+N}, {-E*h+UH, -dt*i+Q}, {-E*h+UH, dt}, {-E*h+UH, -E*qe+Fe}, {-E*h+UH, -v*qe*B+Fm}, {L, qe}, {L, -V*n+N}, {L, -dt*i+Q}, {L, dt}, {L, -E*qe+Fe}, {L, -v*qe*B+Fm}, {qe, -V*n+N}, {qe, -dt*i+Q}, {qe, dt}, {qe, -E*qe+Fe}, {qe, -v*qe*B+Fm}, {-V*n+N, -dt*i+Q}, {-V*n+N, dt}, {-V*n+N, -E*qe+Fe}, {-V*n+N, -v*qe*B+Fm}, {-dt*i+Q, dt}, {-dt*i+Q, -E*qe+Fe}, {-dt*i+Q, -v*qe*B+Fm}, {dt, -E*qe+Fe}, {dt, -v*qe*B+Fm}, {-E*qe+Fe, -v*qe*B+Fm}, {-E*h+UH, L, qe}, {-E*h+UH, L, -V*n+N}, {-E*h+UH, L, -dt*i+Q}, {-E*h+UH, L, dt}, {-E*h+UH, L, -E*qe+Fe}, {-E*h+UH, L, -v*qe*B+Fm}, {-E*h+UH, qe, -V*n+N}, {-E*h+UH, qe, -dt*i+Q}, {-E*h+UH, qe, dt}, {-E*h+UH, qe, -E*qe+Fe}, {-E*h+UH, qe, -v*qe*B+Fm}, {-E*h+UH, -V*n+N, -dt*i+Q}, {-E*h+UH, -V*n+N, dt}, {-E*h+UH, -V*n+N, -E*qe+Fe}, {-E*h+UH, -V*n+N, -v*qe*B+Fm}, {-E*h+UH, -dt*i+Q, dt}, {-E*h+UH, -dt*i+Q, -E*qe+Fe}, {-E*h+UH, -dt*i+Q, -v*qe*B+Fm}, {-E*h+UH, dt, -E*qe+Fe}, {-E*h+UH, dt, -v*qe*B+Fm}, {-E*h+UH, -E*qe+Fe, -v*qe*B+Fm}, {L, qe, -V*n+N}, {L, qe, -dt*i+Q}, {L, qe, dt}, {L, qe, -E*qe+Fe}, {L, qe, -v*qe*B+Fm}, {L, -V*n+N, -dt*i+Q}, {L, -V*n+N, dt}, {L, -V*n+N, -E*qe+Fe}, {L, -V*n+N, -v*qe*B+Fm}, {L, -dt*i+Q, dt}, {L, -dt*i+Q, -E*qe+Fe}, {L, -dt*i+Q, -v*qe*B+Fm}, {L, dt, -E*qe+Fe}, {L, dt, -v*qe*B+Fm}, {L, -E*qe+Fe, -v*qe*B+Fm}, {qe, -V*n+N, -dt*i+Q}, {qe, -V*n+N, dt}, {qe, -V*n+N, -E*qe+Fe}, {qe, -V*n+N, -v*qe*B+Fm}, {qe, -dt*i+Q, dt}, {qe, -dt*i+Q, -E*qe+Fe}, {qe, -dt*i+Q, -v*qe*B+Fm}, {qe, dt, -E*qe+Fe}, {qe, dt, -v*qe*B+Fm}, {qe, -E*qe+Fe, -v*qe*B+Fm}, {-V*n+N, -dt*i+Q, dt}, {-V*n+N, -dt*i+Q, -E*qe+Fe}, {-V*n+N, -dt*i+Q, -v*qe*B+Fm}, {-V*n+N, dt, -E*qe+Fe}, {-V*n+N, dt, -v*qe*B+Fm}, {-V*n+N, -E*qe+Fe, -v*qe*B+Fm}, {-dt*i+Q, dt, -E*qe+Fe}, {-dt*i+Q, dt, -v*qe*B+Fm}, {-dt*i+Q, -E*qe+Fe, -v*qe*B+Fm}, {dt, -E*qe+Fe, -v*qe*B+Fm}, {-E*h+UH}, {h}, {qe}, {-V*n+N}, {-dt*i+Q}, {dt}, {-E*qe+Fe}, {-v*qe*B+Fm}, {-E*h+UH, h}, {-E*h+UH, qe}, {-E*h+UH, -V*n+N}, {-E*h+UH, -dt*i+Q}, {-E*h+UH, dt}, {-E*h+UH, -E*qe+Fe}, {-E*h+UH, -v*qe*B+Fm}, {h, qe}, {h, -V*n+N}, {h, -dt*i+Q}, {h, dt}, {h, -E*qe+Fe}, {h, -v*qe*B+Fm}, {qe, -V*n+N}, {qe, -dt*i+Q}, {qe, dt}, {qe, -E*qe+Fe}, {qe, -v*qe*B+Fm}, {-V*n+N, -dt*i+Q}, {-V*n+N, dt}, {-V*n+N, -E*qe+Fe}, {-V*n+N, -v*qe*B+Fm}, {-dt*i+Q, dt}, {-dt*i+Q, -E*qe+Fe}, {-dt*i+Q, -v*qe*B+Fm}, {dt, -E*qe+Fe}, {dt, -v*qe*B+Fm}, {-E*qe+Fe, -v*qe*B+Fm}, {-E*h+UH, h, qe}, {-E*h+UH, h, -V*n+N}, {-E*h+UH, h, -dt*i+Q}, {-E*h+UH, h, dt}, {-E*h+UH, h, -E*qe+Fe}, {-E*h+UH, h, -v*qe*B+Fm}, {-E*h+UH, qe, -V*n+N}, {-E*h+UH, qe, -dt*i+Q}, {-E*h+UH, qe, dt}, {-E*h+UH, qe, -E*qe+Fe}, {-E*h+UH, qe, -v*qe*B+Fm}, {-E*h+UH, -V*n+N, -dt*i+Q}, {-E*h+UH, -V*n+N, dt}, {-E*h+UH, -V*n+N, -E*qe+Fe}, {-E*h+UH, -V*n+N, -v*qe*B+Fm}, {-E*h+UH, -dt*i+Q, dt}, {-E*h+UH, -dt*i+Q, -E*qe+Fe}, {-E*h+UH, -dt*i+Q, -v*qe*B+Fm}, {-E*h+UH, dt, -E*qe+Fe}, {-E*h+UH, dt, -v*qe*B+Fm}, {-E*h+UH, -E*qe+Fe, -v*qe*B+Fm}, {h, qe, -V*n+N}, {h, qe, -dt*i+Q}, {h, qe, dt}, {h, qe, -E*qe+Fe}, {h, qe, -v*qe*B+Fm}, {h, -V*n+N, -dt*i+Q}, {h, -V*n+N, dt}, {h, -V*n+N, -E*qe+Fe}, {h, -V*n+N, -v*qe*B+Fm}, {h, -dt*i+Q, dt}, {h, -dt*i+Q, -E*qe+Fe}, {h, -dt*i+Q, -v*qe*B+Fm}, {h, dt, -E*qe+Fe}, {h, dt, -v*qe*B+Fm}, {h, -E*qe+Fe, -v*qe*B+Fm}, {qe, -V*n+N, -dt*i+Q}, {qe, -V*n+N, dt}, {qe, -V*n+N, -E*qe+Fe}, {qe, -V*n+N, -v*qe*B+Fm}, {qe, -dt*i+Q, dt}, {qe, -dt*i+Q, -E*qe+Fe}, {qe, -dt*i+Q, -v*qe*B+Fm}, {qe, dt, -E*qe+Fe}, {qe, dt, -v*qe*B+Fm}, {qe, -E*qe+Fe, -v*qe*B+Fm}, {-V*n+N, -dt*i+Q, dt}, {-V*n+N, -dt*i+Q, -E*qe+Fe}, {-V*n+N, -dt*i+Q, -v*qe*B+Fm}, {-V*n+N, dt, -E*qe+Fe}, {-V*n+N, dt, -v*qe*B+Fm}, {-V*n+N, -E*qe+Fe, -v*qe*B+Fm}, {-dt*i+Q, dt, -E*qe+Fe}, {-dt*i+Q, dt, -v*qe*B+Fm}, {-dt*i+Q, -E*qe+Fe, -v*qe*B+Fm}, {dt, -E*qe+Fe, -v*qe*B+Fm}, {-E*h+UH}, {B}, {qe}, {-V*n+N}, {-dt*i+Q}, {dt}, {-E*qe+Fe}, {-v*qe*B+Fm}, {-E*h+UH, B}, {-E*h+UH, qe}, {-E*h+UH, -V*n+N}, {-E*h+UH, -dt*i+Q}, {-E*h+UH, dt}, {-E*h+UH, -E*qe+Fe}, {-E*h+UH, -v*qe*B+Fm}, {B, qe}, {B, -V*n+N}, {B, -dt*i+Q}, {B, dt}, {B, -E*qe+Fe}, {B, -v*qe*B+Fm}, {qe, -V*n+N}, {qe, -dt*i+Q}, {qe, dt}, {qe, -E*qe+Fe}, {qe, -v*qe*B+Fm}, {-V*n+N, -dt*i+Q}, {-V*n+N, dt}, {-V*n+N, -E*qe+Fe}, {-V*n+N, -v*qe*B+Fm}, {-dt*i+Q, dt}, {-dt*i+Q, -E*qe+Fe}, {-dt*i+Q, -v*qe*B+Fm}, {dt, -E*qe+Fe}, {dt, -v*qe*B+Fm}, {-E*qe+Fe, -v*qe*B+Fm}, {-E*h+UH, B, qe}, {-E*h+UH, B, -V*n+N}, {-E*h+UH, B, -dt*i+Q}, {-E*h+UH, B, dt}, {-E*h+UH, B, -E*qe+Fe}, {-E*h+UH, B, -v*qe*B+Fm}, {-E*h+UH, qe, -V*n+N}, {-E*h+UH, qe, -dt*i+Q}, {-E*h+UH, qe, dt}, {-E*h+UH, qe, -E*qe+Fe}, {-E*h+UH, qe, -v*qe*B+Fm}, {-E*h+UH, -V*n+N, -dt*i+Q}, {-E*h+UH, -V*n+N, dt}, {-E*h+UH, -V*n+N, -E*qe+Fe}, {-E*h+UH, -V*n+N, -v*qe*B+Fm}, {-E*h+UH, -dt*i+Q, dt}, {-E*h+UH, -dt*i+Q, -E*qe+Fe}, {-E*h+UH, -dt*i+Q, -v*qe*B+Fm}, {-E*h+UH, dt, -E*qe+Fe}, {-E*h+UH, dt, -v*qe*B+Fm}, {-E*h+UH, -E*qe+Fe, -v*qe*B+Fm}, {B, qe, -V*n+N}, {B, qe, -dt*i+Q}, {B, qe, dt}, {B, qe, -E*qe+Fe}, {B, qe, -v*qe*B+Fm}, {B, -V*n+N, -dt*i+Q}, {B, -V*n+N, dt}, {B, -V*n+N, -E*qe+Fe}, {B, -V*n+N, -v*qe*B+Fm}, {B, -dt*i+Q, dt}, {B, -dt*i+Q, -E*qe+Fe}, {B, -dt*i+Q, -v*qe*B+Fm}, {B, dt, -E*qe+Fe}, {B, dt, -v*qe*B+Fm}, {B, -E*qe+Fe, -v*qe*B+Fm}, {qe, -V*n+N, -dt*i+Q}, {qe, -V*n+N, dt}, {qe, -V*n+N, -E*qe+Fe}, {qe, -V*n+N, -v*qe*B+Fm}, {qe, -dt*i+Q, dt}, {qe, -dt*i+Q, -E*qe+Fe}, {qe, -dt*i+Q, -v*qe*B+Fm}, {qe, dt, -E*qe+Fe}, {qe, dt, -v*qe*B+Fm}, {qe, -E*qe+Fe, -v*qe*B+Fm}, {-V*n+N, -dt*i+Q, dt}, {-V*n+N, -dt*i+Q, -E*qe+Fe}, {-V*n+N, -dt*i+Q, -v*qe*B+Fm}, {-V*n+N, dt, -E*qe+Fe}, {-V*n+N, dt, -v*qe*B+Fm}, {-V*n+N, -E*qe+Fe, -v*qe*B+Fm}, {-dt*i+Q, dt, -E*qe+Fe}, {-dt*i+Q, dt, -v*qe*B+Fm}, {-dt*i+Q, -E*qe+Fe, -v*qe*B+Fm}, {dt, -E*qe+Fe, -v*qe*B+Fm}};

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
f = openOut "results/hall/abduction/noiseless/2_axiom(s)_removed/combo_5_9/reasoning/reasoning_output.txt";
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

print("Reasoning complete. Output written to results/hall/abduction/noiseless/2_axiom(s)_removed/combo_5_9/reasoning/reasoning_output.txt");
