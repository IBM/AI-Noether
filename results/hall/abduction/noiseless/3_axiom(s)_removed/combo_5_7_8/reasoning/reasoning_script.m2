-- AI-Noether: Reasoning Template (Noiseless)
-- Tests if candidate axiom sets, when added to remaining axioms, prove targets

needsPackage("PrimaryDecomposition", Reload => true)

-- Ring definition
R = QQ[Fm, d, v, Fe, E, dt, Q, N, V, i, n, qe, B, h, L, UH, MonomialOrder => Lex];

-- Input data
remainingAxioms = toList([Fm - qe*v*B, Fe - qe*E, Fm - Fe, E*h - UH, i*dt - Q, V - L*h*d]);
qList = toList([N*qe*UH - i*B*h*L]);
k = #qList;

-- Per-target variable partitions
measuredPerTarget = {{UH, h, L, i, B, N, qe}};
nonMeasuredPerTarget = {{Fm, d, v, Fe, E, dt, Q, V, n}};

-- Candidate axiom sets to test (list of lists)
candidateSets = {{}, {E*N*qe-i*B*L}, {v*B-E}, {v*N*qe-i*L}, {-E*h+UH}, {-d*h*L+V}, {-dt*i+Q}, {-E*qe+Fe}, {-v*qe*B+Fm}, {E*N*qe-i*B*L, v*B-E}, {E*N*qe-i*B*L, v*N*qe-i*L}, {E*N*qe-i*B*L, -E*h+UH}, {E*N*qe-i*B*L, -d*h*L+V}, {E*N*qe-i*B*L, -dt*i+Q}, {E*N*qe-i*B*L, -E*qe+Fe}, {E*N*qe-i*B*L, -v*qe*B+Fm}, {v*B-E, v*N*qe-i*L}, {v*B-E, -E*h+UH}, {v*B-E, -d*h*L+V}, {v*B-E, -dt*i+Q}, {v*B-E, -E*qe+Fe}, {v*B-E, -v*qe*B+Fm}, {v*N*qe-i*L, -E*h+UH}, {v*N*qe-i*L, -d*h*L+V}, {v*N*qe-i*L, -dt*i+Q}, {v*N*qe-i*L, -E*qe+Fe}, {v*N*qe-i*L, -v*qe*B+Fm}, {-E*h+UH, -d*h*L+V}, {-E*h+UH, -dt*i+Q}, {-E*h+UH, -E*qe+Fe}, {-E*h+UH, -v*qe*B+Fm}, {-d*h*L+V, -dt*i+Q}, {-d*h*L+V, -E*qe+Fe}, {-d*h*L+V, -v*qe*B+Fm}, {-dt*i+Q, -E*qe+Fe}, {-dt*i+Q, -v*qe*B+Fm}, {-E*qe+Fe, -v*qe*B+Fm}, {E*N*qe-i*B*L, v*B-E, v*N*qe-i*L}, {E*N*qe-i*B*L, v*B-E, -E*h+UH}, {E*N*qe-i*B*L, v*B-E, -d*h*L+V}, {E*N*qe-i*B*L, v*B-E, -dt*i+Q}, {E*N*qe-i*B*L, v*B-E, -E*qe+Fe}, {E*N*qe-i*B*L, v*B-E, -v*qe*B+Fm}, {E*N*qe-i*B*L, v*N*qe-i*L, -E*h+UH}, {E*N*qe-i*B*L, v*N*qe-i*L, -d*h*L+V}, {E*N*qe-i*B*L, v*N*qe-i*L, -dt*i+Q}, {E*N*qe-i*B*L, v*N*qe-i*L, -E*qe+Fe}, {E*N*qe-i*B*L, v*N*qe-i*L, -v*qe*B+Fm}, {E*N*qe-i*B*L, -E*h+UH, -d*h*L+V}, {E*N*qe-i*B*L, -E*h+UH, -dt*i+Q}, {E*N*qe-i*B*L, -E*h+UH, -E*qe+Fe}, {E*N*qe-i*B*L, -E*h+UH, -v*qe*B+Fm}, {E*N*qe-i*B*L, -d*h*L+V, -dt*i+Q}, {E*N*qe-i*B*L, -d*h*L+V, -E*qe+Fe}, {E*N*qe-i*B*L, -d*h*L+V, -v*qe*B+Fm}, {E*N*qe-i*B*L, -dt*i+Q, -E*qe+Fe}, {E*N*qe-i*B*L, -dt*i+Q, -v*qe*B+Fm}, {E*N*qe-i*B*L, -E*qe+Fe, -v*qe*B+Fm}, {v*B-E, v*N*qe-i*L, -E*h+UH}, {v*B-E, v*N*qe-i*L, -d*h*L+V}, {v*B-E, v*N*qe-i*L, -dt*i+Q}, {v*B-E, v*N*qe-i*L, -E*qe+Fe}, {v*B-E, v*N*qe-i*L, -v*qe*B+Fm}, {v*B-E, -E*h+UH, -d*h*L+V}, {v*B-E, -E*h+UH, -dt*i+Q}, {v*B-E, -E*h+UH, -E*qe+Fe}, {v*B-E, -E*h+UH, -v*qe*B+Fm}, {v*B-E, -d*h*L+V, -dt*i+Q}, {v*B-E, -d*h*L+V, -E*qe+Fe}, {v*B-E, -d*h*L+V, -v*qe*B+Fm}, {v*B-E, -dt*i+Q, -E*qe+Fe}, {v*B-E, -dt*i+Q, -v*qe*B+Fm}, {v*B-E, -E*qe+Fe, -v*qe*B+Fm}, {v*N*qe-i*L, -E*h+UH, -d*h*L+V}, {v*N*qe-i*L, -E*h+UH, -dt*i+Q}, {v*N*qe-i*L, -E*h+UH, -E*qe+Fe}, {v*N*qe-i*L, -E*h+UH, -v*qe*B+Fm}, {v*N*qe-i*L, -d*h*L+V, -dt*i+Q}, {v*N*qe-i*L, -d*h*L+V, -E*qe+Fe}, {v*N*qe-i*L, -d*h*L+V, -v*qe*B+Fm}, {v*N*qe-i*L, -dt*i+Q, -E*qe+Fe}, {v*N*qe-i*L, -dt*i+Q, -v*qe*B+Fm}, {v*N*qe-i*L, -E*qe+Fe, -v*qe*B+Fm}, {-E*h+UH, -d*h*L+V, -dt*i+Q}, {-E*h+UH, -d*h*L+V, -E*qe+Fe}, {-E*h+UH, -d*h*L+V, -v*qe*B+Fm}, {-E*h+UH, -dt*i+Q, -E*qe+Fe}, {-E*h+UH, -dt*i+Q, -v*qe*B+Fm}, {-E*h+UH, -E*qe+Fe, -v*qe*B+Fm}, {-d*h*L+V, -dt*i+Q, -E*qe+Fe}, {-d*h*L+V, -dt*i+Q, -v*qe*B+Fm}, {-d*h*L+V, -E*qe+Fe, -v*qe*B+Fm}, {-dt*i+Q, -E*qe+Fe, -v*qe*B+Fm}, {E*N*qe-i*B*L, v*B-E, v*N*qe-i*L, -E*h+UH}, {E*N*qe-i*B*L, v*B-E, v*N*qe-i*L, -d*h*L+V}, {E*N*qe-i*B*L, v*B-E, v*N*qe-i*L, -dt*i+Q}, {E*N*qe-i*B*L, v*B-E, v*N*qe-i*L, -E*qe+Fe}, {E*N*qe-i*B*L, v*B-E, v*N*qe-i*L, -v*qe*B+Fm}, {E*N*qe-i*B*L, v*B-E, -E*h+UH, -d*h*L+V}, {E*N*qe-i*B*L, v*B-E, -E*h+UH, -dt*i+Q}, {E*N*qe-i*B*L, v*B-E, -E*h+UH, -E*qe+Fe}, {E*N*qe-i*B*L, v*B-E, -E*h+UH, -v*qe*B+Fm}, {E*N*qe-i*B*L, v*B-E, -d*h*L+V, -dt*i+Q}, {E*N*qe-i*B*L, v*B-E, -d*h*L+V, -E*qe+Fe}, {E*N*qe-i*B*L, v*B-E, -d*h*L+V, -v*qe*B+Fm}, {E*N*qe-i*B*L, v*B-E, -dt*i+Q, -E*qe+Fe}, {E*N*qe-i*B*L, v*B-E, -dt*i+Q, -v*qe*B+Fm}, {E*N*qe-i*B*L, v*B-E, -E*qe+Fe, -v*qe*B+Fm}, {E*N*qe-i*B*L, v*N*qe-i*L, -E*h+UH, -d*h*L+V}, {E*N*qe-i*B*L, v*N*qe-i*L, -E*h+UH, -dt*i+Q}, {E*N*qe-i*B*L, v*N*qe-i*L, -E*h+UH, -E*qe+Fe}, {E*N*qe-i*B*L, v*N*qe-i*L, -E*h+UH, -v*qe*B+Fm}, {E*N*qe-i*B*L, v*N*qe-i*L, -d*h*L+V, -dt*i+Q}, {E*N*qe-i*B*L, v*N*qe-i*L, -d*h*L+V, -E*qe+Fe}, {E*N*qe-i*B*L, v*N*qe-i*L, -d*h*L+V, -v*qe*B+Fm}, {E*N*qe-i*B*L, v*N*qe-i*L, -dt*i+Q, -E*qe+Fe}, {E*N*qe-i*B*L, v*N*qe-i*L, -dt*i+Q, -v*qe*B+Fm}, {E*N*qe-i*B*L, v*N*qe-i*L, -E*qe+Fe, -v*qe*B+Fm}, {E*N*qe-i*B*L, -E*h+UH, -d*h*L+V, -dt*i+Q}, {E*N*qe-i*B*L, -E*h+UH, -d*h*L+V, -E*qe+Fe}, {E*N*qe-i*B*L, -E*h+UH, -d*h*L+V, -v*qe*B+Fm}, {E*N*qe-i*B*L, -E*h+UH, -dt*i+Q, -E*qe+Fe}, {E*N*qe-i*B*L, -E*h+UH, -dt*i+Q, -v*qe*B+Fm}, {E*N*qe-i*B*L, -E*h+UH, -E*qe+Fe, -v*qe*B+Fm}, {E*N*qe-i*B*L, -d*h*L+V, -dt*i+Q, -E*qe+Fe}, {E*N*qe-i*B*L, -d*h*L+V, -dt*i+Q, -v*qe*B+Fm}, {E*N*qe-i*B*L, -d*h*L+V, -E*qe+Fe, -v*qe*B+Fm}, {E*N*qe-i*B*L, -dt*i+Q, -E*qe+Fe, -v*qe*B+Fm}, {v*B-E, v*N*qe-i*L, -E*h+UH, -d*h*L+V}, {v*B-E, v*N*qe-i*L, -E*h+UH, -dt*i+Q}, {v*B-E, v*N*qe-i*L, -E*h+UH, -E*qe+Fe}, {v*B-E, v*N*qe-i*L, -E*h+UH, -v*qe*B+Fm}, {v*B-E, v*N*qe-i*L, -d*h*L+V, -dt*i+Q}, {v*B-E, v*N*qe-i*L, -d*h*L+V, -E*qe+Fe}, {v*B-E, v*N*qe-i*L, -d*h*L+V, -v*qe*B+Fm}, {v*B-E, v*N*qe-i*L, -dt*i+Q, -E*qe+Fe}, {v*B-E, v*N*qe-i*L, -dt*i+Q, -v*qe*B+Fm}, {v*B-E, v*N*qe-i*L, -E*qe+Fe, -v*qe*B+Fm}, {v*B-E, -E*h+UH, -d*h*L+V, -dt*i+Q}, {v*B-E, -E*h+UH, -d*h*L+V, -E*qe+Fe}, {v*B-E, -E*h+UH, -d*h*L+V, -v*qe*B+Fm}, {v*B-E, -E*h+UH, -dt*i+Q, -E*qe+Fe}, {v*B-E, -E*h+UH, -dt*i+Q, -v*qe*B+Fm}, {v*B-E, -E*h+UH, -E*qe+Fe, -v*qe*B+Fm}, {v*B-E, -d*h*L+V, -dt*i+Q, -E*qe+Fe}, {v*B-E, -d*h*L+V, -dt*i+Q, -v*qe*B+Fm}, {v*B-E, -d*h*L+V, -E*qe+Fe, -v*qe*B+Fm}, {v*B-E, -dt*i+Q, -E*qe+Fe, -v*qe*B+Fm}, {v*N*qe-i*L, -E*h+UH, -d*h*L+V, -dt*i+Q}, {v*N*qe-i*L, -E*h+UH, -d*h*L+V, -E*qe+Fe}, {v*N*qe-i*L, -E*h+UH, -d*h*L+V, -v*qe*B+Fm}, {v*N*qe-i*L, -E*h+UH, -dt*i+Q, -E*qe+Fe}, {v*N*qe-i*L, -E*h+UH, -dt*i+Q, -v*qe*B+Fm}, {v*N*qe-i*L, -E*h+UH, -E*qe+Fe, -v*qe*B+Fm}, {v*N*qe-i*L, -d*h*L+V, -dt*i+Q, -E*qe+Fe}, {v*N*qe-i*L, -d*h*L+V, -dt*i+Q, -v*qe*B+Fm}, {v*N*qe-i*L, -d*h*L+V, -E*qe+Fe, -v*qe*B+Fm}, {v*N*qe-i*L, -dt*i+Q, -E*qe+Fe, -v*qe*B+Fm}, {-E*h+UH, -d*h*L+V, -dt*i+Q, -E*qe+Fe}, {-E*h+UH, -d*h*L+V, -dt*i+Q, -v*qe*B+Fm}, {-E*h+UH, -d*h*L+V, -E*qe+Fe, -v*qe*B+Fm}, {-E*h+UH, -dt*i+Q, -E*qe+Fe, -v*qe*B+Fm}, {-d*h*L+V, -dt*i+Q, -E*qe+Fe, -v*qe*B+Fm}, {-E*h+UH}, {B}, {-d*h*L+V}, {-dt*i+Q}, {E}, {-E*qe+Fe}, {-v*qe*B+Fm}, {-E*h+UH, B}, {-E*h+UH, -d*h*L+V}, {-E*h+UH, -dt*i+Q}, {-E*h+UH, E}, {-E*h+UH, -E*qe+Fe}, {-E*h+UH, -v*qe*B+Fm}, {B, -d*h*L+V}, {B, -dt*i+Q}, {B, E}, {B, -E*qe+Fe}, {B, -v*qe*B+Fm}, {-d*h*L+V, -dt*i+Q}, {-d*h*L+V, E}, {-d*h*L+V, -E*qe+Fe}, {-d*h*L+V, -v*qe*B+Fm}, {-dt*i+Q, E}, {-dt*i+Q, -E*qe+Fe}, {-dt*i+Q, -v*qe*B+Fm}, {E, -E*qe+Fe}, {E, -v*qe*B+Fm}, {-E*qe+Fe, -v*qe*B+Fm}, {-E*h+UH, B, -d*h*L+V}, {-E*h+UH, B, -dt*i+Q}, {-E*h+UH, B, E}, {-E*h+UH, B, -E*qe+Fe}, {-E*h+UH, B, -v*qe*B+Fm}, {-E*h+UH, -d*h*L+V, -dt*i+Q}, {-E*h+UH, -d*h*L+V, E}, {-E*h+UH, -d*h*L+V, -E*qe+Fe}, {-E*h+UH, -d*h*L+V, -v*qe*B+Fm}, {-E*h+UH, -dt*i+Q, E}, {-E*h+UH, -dt*i+Q, -E*qe+Fe}, {-E*h+UH, -dt*i+Q, -v*qe*B+Fm}, {-E*h+UH, E, -E*qe+Fe}, {-E*h+UH, E, -v*qe*B+Fm}, {-E*h+UH, -E*qe+Fe, -v*qe*B+Fm}, {B, -d*h*L+V, -dt*i+Q}, {B, -d*h*L+V, E}, {B, -d*h*L+V, -E*qe+Fe}, {B, -d*h*L+V, -v*qe*B+Fm}, {B, -dt*i+Q, E}, {B, -dt*i+Q, -E*qe+Fe}, {B, -dt*i+Q, -v*qe*B+Fm}, {B, E, -E*qe+Fe}, {B, E, -v*qe*B+Fm}, {B, -E*qe+Fe, -v*qe*B+Fm}, {-d*h*L+V, -dt*i+Q, E}, {-d*h*L+V, -dt*i+Q, -E*qe+Fe}, {-d*h*L+V, -dt*i+Q, -v*qe*B+Fm}, {-d*h*L+V, E, -E*qe+Fe}, {-d*h*L+V, E, -v*qe*B+Fm}, {-d*h*L+V, -E*qe+Fe, -v*qe*B+Fm}, {-dt*i+Q, E, -E*qe+Fe}, {-dt*i+Q, E, -v*qe*B+Fm}, {-dt*i+Q, -E*qe+Fe, -v*qe*B+Fm}, {E, -E*qe+Fe, -v*qe*B+Fm}, {-E*h+UH, B, -d*h*L+V, -dt*i+Q}, {-E*h+UH, B, -d*h*L+V, E}, {-E*h+UH, B, -d*h*L+V, -E*qe+Fe}, {-E*h+UH, B, -d*h*L+V, -v*qe*B+Fm}, {-E*h+UH, B, -dt*i+Q, E}, {-E*h+UH, B, -dt*i+Q, -E*qe+Fe}, {-E*h+UH, B, -dt*i+Q, -v*qe*B+Fm}, {-E*h+UH, B, E, -E*qe+Fe}, {-E*h+UH, B, E, -v*qe*B+Fm}, {-E*h+UH, B, -E*qe+Fe, -v*qe*B+Fm}, {-E*h+UH, -d*h*L+V, -dt*i+Q, E}, {-E*h+UH, -d*h*L+V, -dt*i+Q, -E*qe+Fe}, {-E*h+UH, -d*h*L+V, -dt*i+Q, -v*qe*B+Fm}, {-E*h+UH, -d*h*L+V, E, -E*qe+Fe}, {-E*h+UH, -d*h*L+V, E, -v*qe*B+Fm}, {-E*h+UH, -d*h*L+V, -E*qe+Fe, -v*qe*B+Fm}, {-E*h+UH, -dt*i+Q, E, -E*qe+Fe}, {-E*h+UH, -dt*i+Q, E, -v*qe*B+Fm}, {-E*h+UH, -dt*i+Q, -E*qe+Fe, -v*qe*B+Fm}, {-E*h+UH, E, -E*qe+Fe, -v*qe*B+Fm}, {B, -d*h*L+V, -dt*i+Q, E}, {B, -d*h*L+V, -dt*i+Q, -E*qe+Fe}, {B, -d*h*L+V, -dt*i+Q, -v*qe*B+Fm}, {B, -d*h*L+V, E, -E*qe+Fe}, {B, -d*h*L+V, E, -v*qe*B+Fm}, {B, -d*h*L+V, -E*qe+Fe, -v*qe*B+Fm}, {B, -dt*i+Q, E, -E*qe+Fe}, {B, -dt*i+Q, E, -v*qe*B+Fm}, {B, -dt*i+Q, -E*qe+Fe, -v*qe*B+Fm}, {B, E, -E*qe+Fe, -v*qe*B+Fm}, {-d*h*L+V, -dt*i+Q, E, -E*qe+Fe}, {-d*h*L+V, -dt*i+Q, E, -v*qe*B+Fm}, {-d*h*L+V, -dt*i+Q, -E*qe+Fe, -v*qe*B+Fm}, {-d*h*L+V, E, -E*qe+Fe, -v*qe*B+Fm}, {-dt*i+Q, E, -E*qe+Fe, -v*qe*B+Fm}, {v*B-E}, {-E*h+UH}, {h}, {-d*h*L+V}, {-dt*i+Q}, {-E*qe+Fe}, {-v*qe*B+Fm}, {v*B-E, -E*h+UH}, {v*B-E, h}, {v*B-E, -d*h*L+V}, {v*B-E, -dt*i+Q}, {v*B-E, -E*qe+Fe}, {v*B-E, -v*qe*B+Fm}, {-E*h+UH, h}, {-E*h+UH, -d*h*L+V}, {-E*h+UH, -dt*i+Q}, {-E*h+UH, -E*qe+Fe}, {-E*h+UH, -v*qe*B+Fm}, {h, -d*h*L+V}, {h, -dt*i+Q}, {h, -E*qe+Fe}, {h, -v*qe*B+Fm}, {-d*h*L+V, -dt*i+Q}, {-d*h*L+V, -E*qe+Fe}, {-d*h*L+V, -v*qe*B+Fm}, {-dt*i+Q, -E*qe+Fe}, {-dt*i+Q, -v*qe*B+Fm}, {-E*qe+Fe, -v*qe*B+Fm}, {v*B-E, -E*h+UH, h}, {v*B-E, -E*h+UH, -d*h*L+V}, {v*B-E, -E*h+UH, -dt*i+Q}, {v*B-E, -E*h+UH, -E*qe+Fe}, {v*B-E, -E*h+UH, -v*qe*B+Fm}, {v*B-E, h, -d*h*L+V}, {v*B-E, h, -dt*i+Q}, {v*B-E, h, -E*qe+Fe}, {v*B-E, h, -v*qe*B+Fm}, {v*B-E, -d*h*L+V, -dt*i+Q}, {v*B-E, -d*h*L+V, -E*qe+Fe}, {v*B-E, -d*h*L+V, -v*qe*B+Fm}, {v*B-E, -dt*i+Q, -E*qe+Fe}, {v*B-E, -dt*i+Q, -v*qe*B+Fm}, {v*B-E, -E*qe+Fe, -v*qe*B+Fm}, {-E*h+UH, h, -d*h*L+V}, {-E*h+UH, h, -dt*i+Q}, {-E*h+UH, h, -E*qe+Fe}, {-E*h+UH, h, -v*qe*B+Fm}, {-E*h+UH, -d*h*L+V, -dt*i+Q}, {-E*h+UH, -d*h*L+V, -E*qe+Fe}, {-E*h+UH, -d*h*L+V, -v*qe*B+Fm}, {-E*h+UH, -dt*i+Q, -E*qe+Fe}, {-E*h+UH, -dt*i+Q, -v*qe*B+Fm}, {-E*h+UH, -E*qe+Fe, -v*qe*B+Fm}, {h, -d*h*L+V, -dt*i+Q}, {h, -d*h*L+V, -E*qe+Fe}, {h, -d*h*L+V, -v*qe*B+Fm}, {h, -dt*i+Q, -E*qe+Fe}, {h, -dt*i+Q, -v*qe*B+Fm}, {h, -E*qe+Fe, -v*qe*B+Fm}, {-d*h*L+V, -dt*i+Q, -E*qe+Fe}, {-d*h*L+V, -dt*i+Q, -v*qe*B+Fm}, {-d*h*L+V, -E*qe+Fe, -v*qe*B+Fm}, {-dt*i+Q, -E*qe+Fe, -v*qe*B+Fm}, {v*B-E, -E*h+UH, h, -d*h*L+V}, {v*B-E, -E*h+UH, h, -dt*i+Q}, {v*B-E, -E*h+UH, h, -E*qe+Fe}, {v*B-E, -E*h+UH, h, -v*qe*B+Fm}, {v*B-E, -E*h+UH, -d*h*L+V, -dt*i+Q}, {v*B-E, -E*h+UH, -d*h*L+V, -E*qe+Fe}, {v*B-E, -E*h+UH, -d*h*L+V, -v*qe*B+Fm}, {v*B-E, -E*h+UH, -dt*i+Q, -E*qe+Fe}, {v*B-E, -E*h+UH, -dt*i+Q, -v*qe*B+Fm}, {v*B-E, -E*h+UH, -E*qe+Fe, -v*qe*B+Fm}, {v*B-E, h, -d*h*L+V, -dt*i+Q}, {v*B-E, h, -d*h*L+V, -E*qe+Fe}, {v*B-E, h, -d*h*L+V, -v*qe*B+Fm}, {v*B-E, h, -dt*i+Q, -E*qe+Fe}, {v*B-E, h, -dt*i+Q, -v*qe*B+Fm}, {v*B-E, h, -E*qe+Fe, -v*qe*B+Fm}, {v*B-E, -d*h*L+V, -dt*i+Q, -E*qe+Fe}, {v*B-E, -d*h*L+V, -dt*i+Q, -v*qe*B+Fm}, {v*B-E, -d*h*L+V, -E*qe+Fe, -v*qe*B+Fm}, {v*B-E, -dt*i+Q, -E*qe+Fe, -v*qe*B+Fm}, {-E*h+UH, h, -d*h*L+V, -dt*i+Q}, {-E*h+UH, h, -d*h*L+V, -E*qe+Fe}, {-E*h+UH, h, -d*h*L+V, -v*qe*B+Fm}, {-E*h+UH, h, -dt*i+Q, -E*qe+Fe}, {-E*h+UH, h, -dt*i+Q, -v*qe*B+Fm}, {-E*h+UH, h, -E*qe+Fe, -v*qe*B+Fm}, {-E*h+UH, -d*h*L+V, -dt*i+Q, -E*qe+Fe}, {-E*h+UH, -d*h*L+V, -dt*i+Q, -v*qe*B+Fm}, {-E*h+UH, -d*h*L+V, -E*qe+Fe, -v*qe*B+Fm}, {-E*h+UH, -dt*i+Q, -E*qe+Fe, -v*qe*B+Fm}, {h, -d*h*L+V, -dt*i+Q, -E*qe+Fe}, {h, -d*h*L+V, -dt*i+Q, -v*qe*B+Fm}, {h, -d*h*L+V, -E*qe+Fe, -v*qe*B+Fm}, {h, -dt*i+Q, -E*qe+Fe, -v*qe*B+Fm}, {-d*h*L+V, -dt*i+Q, -E*qe+Fe, -v*qe*B+Fm}, {-E*h+UH}, {L}, {qe}, {-d*h*L+V}, {-dt*i+Q}, {-E*qe+Fe}, {-v*qe*B+Fm}, {-E*h+UH, L}, {-E*h+UH, qe}, {-E*h+UH, -d*h*L+V}, {-E*h+UH, -dt*i+Q}, {-E*h+UH, -E*qe+Fe}, {-E*h+UH, -v*qe*B+Fm}, {L, qe}, {L, -d*h*L+V}, {L, -dt*i+Q}, {L, -E*qe+Fe}, {L, -v*qe*B+Fm}, {qe, -d*h*L+V}, {qe, -dt*i+Q}, {qe, -E*qe+Fe}, {qe, -v*qe*B+Fm}, {-d*h*L+V, -dt*i+Q}, {-d*h*L+V, -E*qe+Fe}, {-d*h*L+V, -v*qe*B+Fm}, {-dt*i+Q, -E*qe+Fe}, {-dt*i+Q, -v*qe*B+Fm}, {-E*qe+Fe, -v*qe*B+Fm}, {-E*h+UH, L, qe}, {-E*h+UH, L, -d*h*L+V}, {-E*h+UH, L, -dt*i+Q}, {-E*h+UH, L, -E*qe+Fe}, {-E*h+UH, L, -v*qe*B+Fm}, {-E*h+UH, qe, -d*h*L+V}, {-E*h+UH, qe, -dt*i+Q}, {-E*h+UH, qe, -E*qe+Fe}, {-E*h+UH, qe, -v*qe*B+Fm}, {-E*h+UH, -d*h*L+V, -dt*i+Q}, {-E*h+UH, -d*h*L+V, -E*qe+Fe}, {-E*h+UH, -d*h*L+V, -v*qe*B+Fm}, {-E*h+UH, -dt*i+Q, -E*qe+Fe}, {-E*h+UH, -dt*i+Q, -v*qe*B+Fm}, {-E*h+UH, -E*qe+Fe, -v*qe*B+Fm}, {L, qe, -d*h*L+V}, {L, qe, -dt*i+Q}, {L, qe, -E*qe+Fe}, {L, qe, -v*qe*B+Fm}, {L, -d*h*L+V, -dt*i+Q}, {L, -d*h*L+V, -E*qe+Fe}, {L, -d*h*L+V, -v*qe*B+Fm}, {L, -dt*i+Q, -E*qe+Fe}, {L, -dt*i+Q, -v*qe*B+Fm}, {L, -E*qe+Fe, -v*qe*B+Fm}, {qe, -d*h*L+V, -dt*i+Q}, {qe, -d*h*L+V, -E*qe+Fe}, {qe, -d*h*L+V, -v*qe*B+Fm}, {qe, -dt*i+Q, -E*qe+Fe}, {qe, -dt*i+Q, -v*qe*B+Fm}, {qe, -E*qe+Fe, -v*qe*B+Fm}, {-d*h*L+V, -dt*i+Q, -E*qe+Fe}, {-d*h*L+V, -dt*i+Q, -v*qe*B+Fm}, {-d*h*L+V, -E*qe+Fe, -v*qe*B+Fm}, {-dt*i+Q, -E*qe+Fe, -v*qe*B+Fm}, {-E*h+UH, L, qe, -d*h*L+V}, {-E*h+UH, L, qe, -dt*i+Q}, {-E*h+UH, L, qe, -E*qe+Fe}, {-E*h+UH, L, qe, -v*qe*B+Fm}, {-E*h+UH, L, -d*h*L+V, -dt*i+Q}, {-E*h+UH, L, -d*h*L+V, -E*qe+Fe}, {-E*h+UH, L, -d*h*L+V, -v*qe*B+Fm}, {-E*h+UH, L, -dt*i+Q, -E*qe+Fe}, {-E*h+UH, L, -dt*i+Q, -v*qe*B+Fm}, {-E*h+UH, L, -E*qe+Fe, -v*qe*B+Fm}, {-E*h+UH, qe, -d*h*L+V, -dt*i+Q}, {-E*h+UH, qe, -d*h*L+V, -E*qe+Fe}, {-E*h+UH, qe, -d*h*L+V, -v*qe*B+Fm}, {-E*h+UH, qe, -dt*i+Q, -E*qe+Fe}, {-E*h+UH, qe, -dt*i+Q, -v*qe*B+Fm}, {-E*h+UH, qe, -E*qe+Fe, -v*qe*B+Fm}, {-E*h+UH, -d*h*L+V, -dt*i+Q, -E*qe+Fe}, {-E*h+UH, -d*h*L+V, -dt*i+Q, -v*qe*B+Fm}, {-E*h+UH, -d*h*L+V, -E*qe+Fe, -v*qe*B+Fm}, {-E*h+UH, -dt*i+Q, -E*qe+Fe, -v*qe*B+Fm}, {L, qe, -d*h*L+V, -dt*i+Q}, {L, qe, -d*h*L+V, -E*qe+Fe}, {L, qe, -d*h*L+V, -v*qe*B+Fm}, {L, qe, -dt*i+Q, -E*qe+Fe}, {L, qe, -dt*i+Q, -v*qe*B+Fm}, {L, qe, -E*qe+Fe, -v*qe*B+Fm}, {L, -d*h*L+V, -dt*i+Q, -E*qe+Fe}, {L, -d*h*L+V, -dt*i+Q, -v*qe*B+Fm}, {L, -d*h*L+V, -E*qe+Fe, -v*qe*B+Fm}, {L, -dt*i+Q, -E*qe+Fe, -v*qe*B+Fm}, {qe, -d*h*L+V, -dt*i+Q, -E*qe+Fe}, {qe, -d*h*L+V, -dt*i+Q, -v*qe*B+Fm}, {qe, -d*h*L+V, -E*qe+Fe, -v*qe*B+Fm}, {qe, -dt*i+Q, -E*qe+Fe, -v*qe*B+Fm}, {-d*h*L+V, -dt*i+Q, -E*qe+Fe, -v*qe*B+Fm}, {-E*h+UH}, {h}, {qe}, {-d*h*L+V}, {-dt*i+Q}, {-E*qe+Fe}, {-v*qe*B+Fm}, {-E*h+UH, h}, {-E*h+UH, qe}, {-E*h+UH, -d*h*L+V}, {-E*h+UH, -dt*i+Q}, {-E*h+UH, -E*qe+Fe}, {-E*h+UH, -v*qe*B+Fm}, {h, qe}, {h, -d*h*L+V}, {h, -dt*i+Q}, {h, -E*qe+Fe}, {h, -v*qe*B+Fm}, {qe, -d*h*L+V}, {qe, -dt*i+Q}, {qe, -E*qe+Fe}, {qe, -v*qe*B+Fm}, {-d*h*L+V, -dt*i+Q}, {-d*h*L+V, -E*qe+Fe}, {-d*h*L+V, -v*qe*B+Fm}, {-dt*i+Q, -E*qe+Fe}, {-dt*i+Q, -v*qe*B+Fm}, {-E*qe+Fe, -v*qe*B+Fm}, {-E*h+UH, h, qe}, {-E*h+UH, h, -d*h*L+V}, {-E*h+UH, h, -dt*i+Q}, {-E*h+UH, h, -E*qe+Fe}, {-E*h+UH, h, -v*qe*B+Fm}, {-E*h+UH, qe, -d*h*L+V}, {-E*h+UH, qe, -dt*i+Q}, {-E*h+UH, qe, -E*qe+Fe}, {-E*h+UH, qe, -v*qe*B+Fm}, {-E*h+UH, -d*h*L+V, -dt*i+Q}, {-E*h+UH, -d*h*L+V, -E*qe+Fe}, {-E*h+UH, -d*h*L+V, -v*qe*B+Fm}, {-E*h+UH, -dt*i+Q, -E*qe+Fe}, {-E*h+UH, -dt*i+Q, -v*qe*B+Fm}, {-E*h+UH, -E*qe+Fe, -v*qe*B+Fm}, {h, qe, -d*h*L+V}, {h, qe, -dt*i+Q}, {h, qe, -E*qe+Fe}, {h, qe, -v*qe*B+Fm}, {h, -d*h*L+V, -dt*i+Q}, {h, -d*h*L+V, -E*qe+Fe}, {h, -d*h*L+V, -v*qe*B+Fm}, {h, -dt*i+Q, -E*qe+Fe}, {h, -dt*i+Q, -v*qe*B+Fm}, {h, -E*qe+Fe, -v*qe*B+Fm}, {qe, -d*h*L+V, -dt*i+Q}, {qe, -d*h*L+V, -E*qe+Fe}, {qe, -d*h*L+V, -v*qe*B+Fm}, {qe, -dt*i+Q, -E*qe+Fe}, {qe, -dt*i+Q, -v*qe*B+Fm}, {qe, -E*qe+Fe, -v*qe*B+Fm}, {-d*h*L+V, -dt*i+Q, -E*qe+Fe}, {-d*h*L+V, -dt*i+Q, -v*qe*B+Fm}, {-d*h*L+V, -E*qe+Fe, -v*qe*B+Fm}, {-dt*i+Q, -E*qe+Fe, -v*qe*B+Fm}, {-E*h+UH, h, qe, -d*h*L+V}, {-E*h+UH, h, qe, -dt*i+Q}, {-E*h+UH, h, qe, -E*qe+Fe}, {-E*h+UH, h, qe, -v*qe*B+Fm}, {-E*h+UH, h, -d*h*L+V, -dt*i+Q}, {-E*h+UH, h, -d*h*L+V, -E*qe+Fe}, {-E*h+UH, h, -d*h*L+V, -v*qe*B+Fm}, {-E*h+UH, h, -dt*i+Q, -E*qe+Fe}, {-E*h+UH, h, -dt*i+Q, -v*qe*B+Fm}, {-E*h+UH, h, -E*qe+Fe, -v*qe*B+Fm}, {-E*h+UH, qe, -d*h*L+V, -dt*i+Q}, {-E*h+UH, qe, -d*h*L+V, -E*qe+Fe}, {-E*h+UH, qe, -d*h*L+V, -v*qe*B+Fm}, {-E*h+UH, qe, -dt*i+Q, -E*qe+Fe}, {-E*h+UH, qe, -dt*i+Q, -v*qe*B+Fm}, {-E*h+UH, qe, -E*qe+Fe, -v*qe*B+Fm}, {-E*h+UH, -d*h*L+V, -dt*i+Q, -E*qe+Fe}, {-E*h+UH, -d*h*L+V, -dt*i+Q, -v*qe*B+Fm}, {-E*h+UH, -d*h*L+V, -E*qe+Fe, -v*qe*B+Fm}, {-E*h+UH, -dt*i+Q, -E*qe+Fe, -v*qe*B+Fm}, {h, qe, -d*h*L+V, -dt*i+Q}, {h, qe, -d*h*L+V, -E*qe+Fe}, {h, qe, -d*h*L+V, -v*qe*B+Fm}, {h, qe, -dt*i+Q, -E*qe+Fe}, {h, qe, -dt*i+Q, -v*qe*B+Fm}, {h, qe, -E*qe+Fe, -v*qe*B+Fm}, {h, -d*h*L+V, -dt*i+Q, -E*qe+Fe}, {h, -d*h*L+V, -dt*i+Q, -v*qe*B+Fm}, {h, -d*h*L+V, -E*qe+Fe, -v*qe*B+Fm}, {h, -dt*i+Q, -E*qe+Fe, -v*qe*B+Fm}, {qe, -d*h*L+V, -dt*i+Q, -E*qe+Fe}, {qe, -d*h*L+V, -dt*i+Q, -v*qe*B+Fm}, {qe, -d*h*L+V, -E*qe+Fe, -v*qe*B+Fm}, {qe, -dt*i+Q, -E*qe+Fe, -v*qe*B+Fm}, {-d*h*L+V, -dt*i+Q, -E*qe+Fe, -v*qe*B+Fm}, {-E*h+UH}, {B}, {qe}, {-d*h*L+V}, {-dt*i+Q}, {-E*qe+Fe}, {-v*qe*B+Fm}, {-E*h+UH, B}, {-E*h+UH, qe}, {-E*h+UH, -d*h*L+V}, {-E*h+UH, -dt*i+Q}, {-E*h+UH, -E*qe+Fe}, {-E*h+UH, -v*qe*B+Fm}, {B, qe}, {B, -d*h*L+V}, {B, -dt*i+Q}, {B, -E*qe+Fe}, {B, -v*qe*B+Fm}, {qe, -d*h*L+V}, {qe, -dt*i+Q}, {qe, -E*qe+Fe}, {qe, -v*qe*B+Fm}, {-d*h*L+V, -dt*i+Q}, {-d*h*L+V, -E*qe+Fe}, {-d*h*L+V, -v*qe*B+Fm}, {-dt*i+Q, -E*qe+Fe}, {-dt*i+Q, -v*qe*B+Fm}, {-E*qe+Fe, -v*qe*B+Fm}, {-E*h+UH, B, qe}, {-E*h+UH, B, -d*h*L+V}, {-E*h+UH, B, -dt*i+Q}, {-E*h+UH, B, -E*qe+Fe}, {-E*h+UH, B, -v*qe*B+Fm}, {-E*h+UH, qe, -d*h*L+V}, {-E*h+UH, qe, -dt*i+Q}, {-E*h+UH, qe, -E*qe+Fe}, {-E*h+UH, qe, -v*qe*B+Fm}, {-E*h+UH, -d*h*L+V, -dt*i+Q}, {-E*h+UH, -d*h*L+V, -E*qe+Fe}, {-E*h+UH, -d*h*L+V, -v*qe*B+Fm}, {-E*h+UH, -dt*i+Q, -E*qe+Fe}, {-E*h+UH, -dt*i+Q, -v*qe*B+Fm}, {-E*h+UH, -E*qe+Fe, -v*qe*B+Fm}, {B, qe, -d*h*L+V}, {B, qe, -dt*i+Q}, {B, qe, -E*qe+Fe}, {B, qe, -v*qe*B+Fm}, {B, -d*h*L+V, -dt*i+Q}, {B, -d*h*L+V, -E*qe+Fe}, {B, -d*h*L+V, -v*qe*B+Fm}, {B, -dt*i+Q, -E*qe+Fe}, {B, -dt*i+Q, -v*qe*B+Fm}, {B, -E*qe+Fe, -v*qe*B+Fm}, {qe, -d*h*L+V, -dt*i+Q}, {qe, -d*h*L+V, -E*qe+Fe}, {qe, -d*h*L+V, -v*qe*B+Fm}, {qe, -dt*i+Q, -E*qe+Fe}, {qe, -dt*i+Q, -v*qe*B+Fm}, {qe, -E*qe+Fe, -v*qe*B+Fm}, {-d*h*L+V, -dt*i+Q, -E*qe+Fe}, {-d*h*L+V, -dt*i+Q, -v*qe*B+Fm}, {-d*h*L+V, -E*qe+Fe, -v*qe*B+Fm}, {-dt*i+Q, -E*qe+Fe, -v*qe*B+Fm}, {-E*h+UH, B, qe, -d*h*L+V}, {-E*h+UH, B, qe, -dt*i+Q}, {-E*h+UH, B, qe, -E*qe+Fe}, {-E*h+UH, B, qe, -v*qe*B+Fm}, {-E*h+UH, B, -d*h*L+V, -dt*i+Q}, {-E*h+UH, B, -d*h*L+V, -E*qe+Fe}, {-E*h+UH, B, -d*h*L+V, -v*qe*B+Fm}, {-E*h+UH, B, -dt*i+Q, -E*qe+Fe}, {-E*h+UH, B, -dt*i+Q, -v*qe*B+Fm}, {-E*h+UH, B, -E*qe+Fe, -v*qe*B+Fm}, {-E*h+UH, qe, -d*h*L+V, -dt*i+Q}, {-E*h+UH, qe, -d*h*L+V, -E*qe+Fe}, {-E*h+UH, qe, -d*h*L+V, -v*qe*B+Fm}, {-E*h+UH, qe, -dt*i+Q, -E*qe+Fe}, {-E*h+UH, qe, -dt*i+Q, -v*qe*B+Fm}, {-E*h+UH, qe, -E*qe+Fe, -v*qe*B+Fm}, {-E*h+UH, -d*h*L+V, -dt*i+Q, -E*qe+Fe}, {-E*h+UH, -d*h*L+V, -dt*i+Q, -v*qe*B+Fm}, {-E*h+UH, -d*h*L+V, -E*qe+Fe, -v*qe*B+Fm}, {-E*h+UH, -dt*i+Q, -E*qe+Fe, -v*qe*B+Fm}, {B, qe, -d*h*L+V, -dt*i+Q}, {B, qe, -d*h*L+V, -E*qe+Fe}, {B, qe, -d*h*L+V, -v*qe*B+Fm}, {B, qe, -dt*i+Q, -E*qe+Fe}, {B, qe, -dt*i+Q, -v*qe*B+Fm}, {B, qe, -E*qe+Fe, -v*qe*B+Fm}, {B, -d*h*L+V, -dt*i+Q, -E*qe+Fe}, {B, -d*h*L+V, -dt*i+Q, -v*qe*B+Fm}, {B, -d*h*L+V, -E*qe+Fe, -v*qe*B+Fm}, {B, -dt*i+Q, -E*qe+Fe, -v*qe*B+Fm}, {qe, -d*h*L+V, -dt*i+Q, -E*qe+Fe}, {qe, -d*h*L+V, -dt*i+Q, -v*qe*B+Fm}, {qe, -d*h*L+V, -E*qe+Fe, -v*qe*B+Fm}, {qe, -dt*i+Q, -E*qe+Fe, -v*qe*B+Fm}, {-d*h*L+V, -dt*i+Q, -E*qe+Fe, -v*qe*B+Fm}, {-E*h+UH}, {qe}, {i}, {-d*h*L+V}, {-dt*i+Q}, {-E*qe+Fe}, {-v*qe*B+Fm}, {-E*h+UH, qe}, {-E*h+UH, i}, {-E*h+UH, -d*h*L+V}, {-E*h+UH, -dt*i+Q}, {-E*h+UH, -E*qe+Fe}, {-E*h+UH, -v*qe*B+Fm}, {qe, i}, {qe, -d*h*L+V}, {qe, -dt*i+Q}, {qe, -E*qe+Fe}, {qe, -v*qe*B+Fm}, {i, -d*h*L+V}, {i, -dt*i+Q}, {i, -E*qe+Fe}, {i, -v*qe*B+Fm}, {-d*h*L+V, -dt*i+Q}, {-d*h*L+V, -E*qe+Fe}, {-d*h*L+V, -v*qe*B+Fm}, {-dt*i+Q, -E*qe+Fe}, {-dt*i+Q, -v*qe*B+Fm}, {-E*qe+Fe, -v*qe*B+Fm}, {-E*h+UH, qe, i}, {-E*h+UH, qe, -d*h*L+V}, {-E*h+UH, qe, -dt*i+Q}, {-E*h+UH, qe, -E*qe+Fe}, {-E*h+UH, qe, -v*qe*B+Fm}, {-E*h+UH, i, -d*h*L+V}, {-E*h+UH, i, -dt*i+Q}, {-E*h+UH, i, -E*qe+Fe}, {-E*h+UH, i, -v*qe*B+Fm}, {-E*h+UH, -d*h*L+V, -dt*i+Q}, {-E*h+UH, -d*h*L+V, -E*qe+Fe}, {-E*h+UH, -d*h*L+V, -v*qe*B+Fm}, {-E*h+UH, -dt*i+Q, -E*qe+Fe}, {-E*h+UH, -dt*i+Q, -v*qe*B+Fm}, {-E*h+UH, -E*qe+Fe, -v*qe*B+Fm}, {qe, i, -d*h*L+V}, {qe, i, -dt*i+Q}, {qe, i, -E*qe+Fe}, {qe, i, -v*qe*B+Fm}, {qe, -d*h*L+V, -dt*i+Q}, {qe, -d*h*L+V, -E*qe+Fe}, {qe, -d*h*L+V, -v*qe*B+Fm}, {qe, -dt*i+Q, -E*qe+Fe}, {qe, -dt*i+Q, -v*qe*B+Fm}, {qe, -E*qe+Fe, -v*qe*B+Fm}, {i, -d*h*L+V, -dt*i+Q}, {i, -d*h*L+V, -E*qe+Fe}, {i, -d*h*L+V, -v*qe*B+Fm}, {i, -dt*i+Q, -E*qe+Fe}, {i, -dt*i+Q, -v*qe*B+Fm}, {i, -E*qe+Fe, -v*qe*B+Fm}, {-d*h*L+V, -dt*i+Q, -E*qe+Fe}, {-d*h*L+V, -dt*i+Q, -v*qe*B+Fm}, {-d*h*L+V, -E*qe+Fe, -v*qe*B+Fm}, {-dt*i+Q, -E*qe+Fe, -v*qe*B+Fm}, {-E*h+UH, qe, i, -d*h*L+V}, {-E*h+UH, qe, i, -dt*i+Q}, {-E*h+UH, qe, i, -E*qe+Fe}, {-E*h+UH, qe, i, -v*qe*B+Fm}, {-E*h+UH, qe, -d*h*L+V, -dt*i+Q}, {-E*h+UH, qe, -d*h*L+V, -E*qe+Fe}, {-E*h+UH, qe, -d*h*L+V, -v*qe*B+Fm}, {-E*h+UH, qe, -dt*i+Q, -E*qe+Fe}, {-E*h+UH, qe, -dt*i+Q, -v*qe*B+Fm}, {-E*h+UH, qe, -E*qe+Fe, -v*qe*B+Fm}, {-E*h+UH, i, -d*h*L+V, -dt*i+Q}, {-E*h+UH, i, -d*h*L+V, -E*qe+Fe}, {-E*h+UH, i, -d*h*L+V, -v*qe*B+Fm}, {-E*h+UH, i, -dt*i+Q, -E*qe+Fe}, {-E*h+UH, i, -dt*i+Q, -v*qe*B+Fm}, {-E*h+UH, i, -E*qe+Fe, -v*qe*B+Fm}, {-E*h+UH, -d*h*L+V, -dt*i+Q, -E*qe+Fe}, {-E*h+UH, -d*h*L+V, -dt*i+Q, -v*qe*B+Fm}, {-E*h+UH, -d*h*L+V, -E*qe+Fe, -v*qe*B+Fm}, {-E*h+UH, -dt*i+Q, -E*qe+Fe, -v*qe*B+Fm}, {qe, i, -d*h*L+V, -dt*i+Q}, {qe, i, -d*h*L+V, -E*qe+Fe}, {qe, i, -d*h*L+V, -v*qe*B+Fm}, {qe, i, -dt*i+Q, -E*qe+Fe}, {qe, i, -dt*i+Q, -v*qe*B+Fm}, {qe, i, -E*qe+Fe, -v*qe*B+Fm}, {qe, -d*h*L+V, -dt*i+Q, -E*qe+Fe}, {qe, -d*h*L+V, -dt*i+Q, -v*qe*B+Fm}, {qe, -d*h*L+V, -E*qe+Fe, -v*qe*B+Fm}, {qe, -dt*i+Q, -E*qe+Fe, -v*qe*B+Fm}, {i, -d*h*L+V, -dt*i+Q, -E*qe+Fe}, {i, -d*h*L+V, -dt*i+Q, -v*qe*B+Fm}, {i, -d*h*L+V, -E*qe+Fe, -v*qe*B+Fm}, {i, -dt*i+Q, -E*qe+Fe, -v*qe*B+Fm}, {-d*h*L+V, -dt*i+Q, -E*qe+Fe, -v*qe*B+Fm}};

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
f = openOut "results/hall/abduction/noiseless/3_axiom(s)_removed/combo_5_7_8/reasoning/reasoning_output.txt";
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

print("Reasoning complete. Output written to results/hall/abduction/noiseless/3_axiom(s)_removed/combo_5_7_8/reasoning/reasoning_output.txt");
