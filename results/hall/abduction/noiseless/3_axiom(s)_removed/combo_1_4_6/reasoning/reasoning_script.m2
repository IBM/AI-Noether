-- AI-Noether: Reasoning Template (Noiseless)
-- Tests if candidate axiom sets, when added to remaining axioms, prove targets

needsPackage("PrimaryDecomposition", Reload => true)

-- Ring definition
R = QQ[Fm, d, v, Fe, E, dt, Q, N, V, i, n, qe, B, h, L, UH, MonomialOrder => Lex];

-- Input data
remainingAxioms = toList([Fe - qe*E, Fm - Fe, v*dt - L, Q - N*qe, n*V - N, V - L*h*d]);
qList = toList([N*qe*UH - i*B*h*L]);
k = #qList;

-- Per-target variable partitions
measuredPerTarget = {{UH, h, L, i, B, N, qe}};
nonMeasuredPerTarget = {{Fm, d, v, Fe, E, dt, Q, V, n}};

-- Candidate axiom sets to test (list of lists)
candidateSets = {{}, {d*n*qe*UH-i*B}, {-v*dt+L}, {-d*h*L+V}, {-V*n+N}, {-N*qe+Q}, {-E*qe+Fe}, {Fm-Fe}, {d*n*qe*UH-i*B, -v*dt+L}, {d*n*qe*UH-i*B, -d*h*L+V}, {d*n*qe*UH-i*B, -V*n+N}, {d*n*qe*UH-i*B, -N*qe+Q}, {d*n*qe*UH-i*B, -E*qe+Fe}, {d*n*qe*UH-i*B, Fm-Fe}, {-v*dt+L, -d*h*L+V}, {-v*dt+L, -V*n+N}, {-v*dt+L, -N*qe+Q}, {-v*dt+L, -E*qe+Fe}, {-v*dt+L, Fm-Fe}, {-d*h*L+V, -V*n+N}, {-d*h*L+V, -N*qe+Q}, {-d*h*L+V, -E*qe+Fe}, {-d*h*L+V, Fm-Fe}, {-V*n+N, -N*qe+Q}, {-V*n+N, -E*qe+Fe}, {-V*n+N, Fm-Fe}, {-N*qe+Q, -E*qe+Fe}, {-N*qe+Q, Fm-Fe}, {-E*qe+Fe, Fm-Fe}, {d*n*qe*UH-i*B, -v*dt+L, -d*h*L+V}, {d*n*qe*UH-i*B, -v*dt+L, -V*n+N}, {d*n*qe*UH-i*B, -v*dt+L, -N*qe+Q}, {d*n*qe*UH-i*B, -v*dt+L, -E*qe+Fe}, {d*n*qe*UH-i*B, -v*dt+L, Fm-Fe}, {d*n*qe*UH-i*B, -d*h*L+V, -V*n+N}, {d*n*qe*UH-i*B, -d*h*L+V, -N*qe+Q}, {d*n*qe*UH-i*B, -d*h*L+V, -E*qe+Fe}, {d*n*qe*UH-i*B, -d*h*L+V, Fm-Fe}, {d*n*qe*UH-i*B, -V*n+N, -N*qe+Q}, {d*n*qe*UH-i*B, -V*n+N, -E*qe+Fe}, {d*n*qe*UH-i*B, -V*n+N, Fm-Fe}, {d*n*qe*UH-i*B, -N*qe+Q, -E*qe+Fe}, {d*n*qe*UH-i*B, -N*qe+Q, Fm-Fe}, {d*n*qe*UH-i*B, -E*qe+Fe, Fm-Fe}, {-v*dt+L, -d*h*L+V, -V*n+N}, {-v*dt+L, -d*h*L+V, -N*qe+Q}, {-v*dt+L, -d*h*L+V, -E*qe+Fe}, {-v*dt+L, -d*h*L+V, Fm-Fe}, {-v*dt+L, -V*n+N, -N*qe+Q}, {-v*dt+L, -V*n+N, -E*qe+Fe}, {-v*dt+L, -V*n+N, Fm-Fe}, {-v*dt+L, -N*qe+Q, -E*qe+Fe}, {-v*dt+L, -N*qe+Q, Fm-Fe}, {-v*dt+L, -E*qe+Fe, Fm-Fe}, {-d*h*L+V, -V*n+N, -N*qe+Q}, {-d*h*L+V, -V*n+N, -E*qe+Fe}, {-d*h*L+V, -V*n+N, Fm-Fe}, {-d*h*L+V, -N*qe+Q, -E*qe+Fe}, {-d*h*L+V, -N*qe+Q, Fm-Fe}, {-d*h*L+V, -E*qe+Fe, Fm-Fe}, {-V*n+N, -N*qe+Q, -E*qe+Fe}, {-V*n+N, -N*qe+Q, Fm-Fe}, {-V*n+N, -E*qe+Fe, Fm-Fe}, {-N*qe+Q, -E*qe+Fe, Fm-Fe}, {d*n*qe*UH-i*B, -v*dt+L, -d*h*L+V, -V*n+N}, {d*n*qe*UH-i*B, -v*dt+L, -d*h*L+V, -N*qe+Q}, {d*n*qe*UH-i*B, -v*dt+L, -d*h*L+V, -E*qe+Fe}, {d*n*qe*UH-i*B, -v*dt+L, -d*h*L+V, Fm-Fe}, {d*n*qe*UH-i*B, -v*dt+L, -V*n+N, -N*qe+Q}, {d*n*qe*UH-i*B, -v*dt+L, -V*n+N, -E*qe+Fe}, {d*n*qe*UH-i*B, -v*dt+L, -V*n+N, Fm-Fe}, {d*n*qe*UH-i*B, -v*dt+L, -N*qe+Q, -E*qe+Fe}, {d*n*qe*UH-i*B, -v*dt+L, -N*qe+Q, Fm-Fe}, {d*n*qe*UH-i*B, -v*dt+L, -E*qe+Fe, Fm-Fe}, {d*n*qe*UH-i*B, -d*h*L+V, -V*n+N, -N*qe+Q}, {d*n*qe*UH-i*B, -d*h*L+V, -V*n+N, -E*qe+Fe}, {d*n*qe*UH-i*B, -d*h*L+V, -V*n+N, Fm-Fe}, {d*n*qe*UH-i*B, -d*h*L+V, -N*qe+Q, -E*qe+Fe}, {d*n*qe*UH-i*B, -d*h*L+V, -N*qe+Q, Fm-Fe}, {d*n*qe*UH-i*B, -d*h*L+V, -E*qe+Fe, Fm-Fe}, {d*n*qe*UH-i*B, -V*n+N, -N*qe+Q, -E*qe+Fe}, {d*n*qe*UH-i*B, -V*n+N, -N*qe+Q, Fm-Fe}, {d*n*qe*UH-i*B, -V*n+N, -E*qe+Fe, Fm-Fe}, {d*n*qe*UH-i*B, -N*qe+Q, -E*qe+Fe, Fm-Fe}, {-v*dt+L, -d*h*L+V, -V*n+N, -N*qe+Q}, {-v*dt+L, -d*h*L+V, -V*n+N, -E*qe+Fe}, {-v*dt+L, -d*h*L+V, -V*n+N, Fm-Fe}, {-v*dt+L, -d*h*L+V, -N*qe+Q, -E*qe+Fe}, {-v*dt+L, -d*h*L+V, -N*qe+Q, Fm-Fe}, {-v*dt+L, -d*h*L+V, -E*qe+Fe, Fm-Fe}, {-v*dt+L, -V*n+N, -N*qe+Q, -E*qe+Fe}, {-v*dt+L, -V*n+N, -N*qe+Q, Fm-Fe}, {-v*dt+L, -V*n+N, -E*qe+Fe, Fm-Fe}, {-v*dt+L, -N*qe+Q, -E*qe+Fe, Fm-Fe}, {-d*h*L+V, -V*n+N, -N*qe+Q, -E*qe+Fe}, {-d*h*L+V, -V*n+N, -N*qe+Q, Fm-Fe}, {-d*h*L+V, -V*n+N, -E*qe+Fe, Fm-Fe}, {-d*h*L+V, -N*qe+Q, -E*qe+Fe, Fm-Fe}, {-V*n+N, -N*qe+Q, -E*qe+Fe, Fm-Fe}, {-v*dt+L}, {h}, {-d*h*L+V}, {-V*n+N}, {-N*qe+Q}, {-E*qe+Fe}, {Fm-Fe}, {-v*dt+L, h}, {-v*dt+L, -d*h*L+V}, {-v*dt+L, -V*n+N}, {-v*dt+L, -N*qe+Q}, {-v*dt+L, -E*qe+Fe}, {-v*dt+L, Fm-Fe}, {h, -d*h*L+V}, {h, -V*n+N}, {h, -N*qe+Q}, {h, -E*qe+Fe}, {h, Fm-Fe}, {-d*h*L+V, -V*n+N}, {-d*h*L+V, -N*qe+Q}, {-d*h*L+V, -E*qe+Fe}, {-d*h*L+V, Fm-Fe}, {-V*n+N, -N*qe+Q}, {-V*n+N, -E*qe+Fe}, {-V*n+N, Fm-Fe}, {-N*qe+Q, -E*qe+Fe}, {-N*qe+Q, Fm-Fe}, {-E*qe+Fe, Fm-Fe}, {-v*dt+L, h, -d*h*L+V}, {-v*dt+L, h, -V*n+N}, {-v*dt+L, h, -N*qe+Q}, {-v*dt+L, h, -E*qe+Fe}, {-v*dt+L, h, Fm-Fe}, {-v*dt+L, -d*h*L+V, -V*n+N}, {-v*dt+L, -d*h*L+V, -N*qe+Q}, {-v*dt+L, -d*h*L+V, -E*qe+Fe}, {-v*dt+L, -d*h*L+V, Fm-Fe}, {-v*dt+L, -V*n+N, -N*qe+Q}, {-v*dt+L, -V*n+N, -E*qe+Fe}, {-v*dt+L, -V*n+N, Fm-Fe}, {-v*dt+L, -N*qe+Q, -E*qe+Fe}, {-v*dt+L, -N*qe+Q, Fm-Fe}, {-v*dt+L, -E*qe+Fe, Fm-Fe}, {h, -d*h*L+V, -V*n+N}, {h, -d*h*L+V, -N*qe+Q}, {h, -d*h*L+V, -E*qe+Fe}, {h, -d*h*L+V, Fm-Fe}, {h, -V*n+N, -N*qe+Q}, {h, -V*n+N, -E*qe+Fe}, {h, -V*n+N, Fm-Fe}, {h, -N*qe+Q, -E*qe+Fe}, {h, -N*qe+Q, Fm-Fe}, {h, -E*qe+Fe, Fm-Fe}, {-d*h*L+V, -V*n+N, -N*qe+Q}, {-d*h*L+V, -V*n+N, -E*qe+Fe}, {-d*h*L+V, -V*n+N, Fm-Fe}, {-d*h*L+V, -N*qe+Q, -E*qe+Fe}, {-d*h*L+V, -N*qe+Q, Fm-Fe}, {-d*h*L+V, -E*qe+Fe, Fm-Fe}, {-V*n+N, -N*qe+Q, -E*qe+Fe}, {-V*n+N, -N*qe+Q, Fm-Fe}, {-V*n+N, -E*qe+Fe, Fm-Fe}, {-N*qe+Q, -E*qe+Fe, Fm-Fe}, {-v*dt+L, h, -d*h*L+V, -V*n+N}, {-v*dt+L, h, -d*h*L+V, -N*qe+Q}, {-v*dt+L, h, -d*h*L+V, -E*qe+Fe}, {-v*dt+L, h, -d*h*L+V, Fm-Fe}, {-v*dt+L, h, -V*n+N, -N*qe+Q}, {-v*dt+L, h, -V*n+N, -E*qe+Fe}, {-v*dt+L, h, -V*n+N, Fm-Fe}, {-v*dt+L, h, -N*qe+Q, -E*qe+Fe}, {-v*dt+L, h, -N*qe+Q, Fm-Fe}, {-v*dt+L, h, -E*qe+Fe, Fm-Fe}, {-v*dt+L, -d*h*L+V, -V*n+N, -N*qe+Q}, {-v*dt+L, -d*h*L+V, -V*n+N, -E*qe+Fe}, {-v*dt+L, -d*h*L+V, -V*n+N, Fm-Fe}, {-v*dt+L, -d*h*L+V, -N*qe+Q, -E*qe+Fe}, {-v*dt+L, -d*h*L+V, -N*qe+Q, Fm-Fe}, {-v*dt+L, -d*h*L+V, -E*qe+Fe, Fm-Fe}, {-v*dt+L, -V*n+N, -N*qe+Q, -E*qe+Fe}, {-v*dt+L, -V*n+N, -N*qe+Q, Fm-Fe}, {-v*dt+L, -V*n+N, -E*qe+Fe, Fm-Fe}, {-v*dt+L, -N*qe+Q, -E*qe+Fe, Fm-Fe}, {h, -d*h*L+V, -V*n+N, -N*qe+Q}, {h, -d*h*L+V, -V*n+N, -E*qe+Fe}, {h, -d*h*L+V, -V*n+N, Fm-Fe}, {h, -d*h*L+V, -N*qe+Q, -E*qe+Fe}, {h, -d*h*L+V, -N*qe+Q, Fm-Fe}, {h, -d*h*L+V, -E*qe+Fe, Fm-Fe}, {h, -V*n+N, -N*qe+Q, -E*qe+Fe}, {h, -V*n+N, -N*qe+Q, Fm-Fe}, {h, -V*n+N, -E*qe+Fe, Fm-Fe}, {h, -N*qe+Q, -E*qe+Fe, Fm-Fe}, {-d*h*L+V, -V*n+N, -N*qe+Q, -E*qe+Fe}, {-d*h*L+V, -V*n+N, -N*qe+Q, Fm-Fe}, {-d*h*L+V, -V*n+N, -E*qe+Fe, Fm-Fe}, {-d*h*L+V, -N*qe+Q, -E*qe+Fe, Fm-Fe}, {-V*n+N, -N*qe+Q, -E*qe+Fe, Fm-Fe}, {-v*dt+L}, {-d*h*L+V}, {-V*n+N}, {-N*qe+Q}, {dt}, {-E*qe+Fe}, {Fm-Fe}, {-v*dt+L, -d*h*L+V}, {-v*dt+L, -V*n+N}, {-v*dt+L, -N*qe+Q}, {-v*dt+L, dt}, {-v*dt+L, -E*qe+Fe}, {-v*dt+L, Fm-Fe}, {-d*h*L+V, -V*n+N}, {-d*h*L+V, -N*qe+Q}, {-d*h*L+V, dt}, {-d*h*L+V, -E*qe+Fe}, {-d*h*L+V, Fm-Fe}, {-V*n+N, -N*qe+Q}, {-V*n+N, dt}, {-V*n+N, -E*qe+Fe}, {-V*n+N, Fm-Fe}, {-N*qe+Q, dt}, {-N*qe+Q, -E*qe+Fe}, {-N*qe+Q, Fm-Fe}, {dt, -E*qe+Fe}, {dt, Fm-Fe}, {-E*qe+Fe, Fm-Fe}, {-v*dt+L, -d*h*L+V, -V*n+N}, {-v*dt+L, -d*h*L+V, -N*qe+Q}, {-v*dt+L, -d*h*L+V, dt}, {-v*dt+L, -d*h*L+V, -E*qe+Fe}, {-v*dt+L, -d*h*L+V, Fm-Fe}, {-v*dt+L, -V*n+N, -N*qe+Q}, {-v*dt+L, -V*n+N, dt}, {-v*dt+L, -V*n+N, -E*qe+Fe}, {-v*dt+L, -V*n+N, Fm-Fe}, {-v*dt+L, -N*qe+Q, dt}, {-v*dt+L, -N*qe+Q, -E*qe+Fe}, {-v*dt+L, -N*qe+Q, Fm-Fe}, {-v*dt+L, dt, -E*qe+Fe}, {-v*dt+L, dt, Fm-Fe}, {-v*dt+L, -E*qe+Fe, Fm-Fe}, {-d*h*L+V, -V*n+N, -N*qe+Q}, {-d*h*L+V, -V*n+N, dt}, {-d*h*L+V, -V*n+N, -E*qe+Fe}, {-d*h*L+V, -V*n+N, Fm-Fe}, {-d*h*L+V, -N*qe+Q, dt}, {-d*h*L+V, -N*qe+Q, -E*qe+Fe}, {-d*h*L+V, -N*qe+Q, Fm-Fe}, {-d*h*L+V, dt, -E*qe+Fe}, {-d*h*L+V, dt, Fm-Fe}, {-d*h*L+V, -E*qe+Fe, Fm-Fe}, {-V*n+N, -N*qe+Q, dt}, {-V*n+N, -N*qe+Q, -E*qe+Fe}, {-V*n+N, -N*qe+Q, Fm-Fe}, {-V*n+N, dt, -E*qe+Fe}, {-V*n+N, dt, Fm-Fe}, {-V*n+N, -E*qe+Fe, Fm-Fe}, {-N*qe+Q, dt, -E*qe+Fe}, {-N*qe+Q, dt, Fm-Fe}, {-N*qe+Q, -E*qe+Fe, Fm-Fe}, {dt, -E*qe+Fe, Fm-Fe}, {-v*dt+L, -d*h*L+V, -V*n+N, -N*qe+Q}, {-v*dt+L, -d*h*L+V, -V*n+N, dt}, {-v*dt+L, -d*h*L+V, -V*n+N, -E*qe+Fe}, {-v*dt+L, -d*h*L+V, -V*n+N, Fm-Fe}, {-v*dt+L, -d*h*L+V, -N*qe+Q, dt}, {-v*dt+L, -d*h*L+V, -N*qe+Q, -E*qe+Fe}, {-v*dt+L, -d*h*L+V, -N*qe+Q, Fm-Fe}, {-v*dt+L, -d*h*L+V, dt, -E*qe+Fe}, {-v*dt+L, -d*h*L+V, dt, Fm-Fe}, {-v*dt+L, -d*h*L+V, -E*qe+Fe, Fm-Fe}, {-v*dt+L, -V*n+N, -N*qe+Q, dt}, {-v*dt+L, -V*n+N, -N*qe+Q, -E*qe+Fe}, {-v*dt+L, -V*n+N, -N*qe+Q, Fm-Fe}, {-v*dt+L, -V*n+N, dt, -E*qe+Fe}, {-v*dt+L, -V*n+N, dt, Fm-Fe}, {-v*dt+L, -V*n+N, -E*qe+Fe, Fm-Fe}, {-v*dt+L, -N*qe+Q, dt, -E*qe+Fe}, {-v*dt+L, -N*qe+Q, dt, Fm-Fe}, {-v*dt+L, -N*qe+Q, -E*qe+Fe, Fm-Fe}, {-v*dt+L, dt, -E*qe+Fe, Fm-Fe}, {-d*h*L+V, -V*n+N, -N*qe+Q, dt}, {-d*h*L+V, -V*n+N, -N*qe+Q, -E*qe+Fe}, {-d*h*L+V, -V*n+N, -N*qe+Q, Fm-Fe}, {-d*h*L+V, -V*n+N, dt, -E*qe+Fe}, {-d*h*L+V, -V*n+N, dt, Fm-Fe}, {-d*h*L+V, -V*n+N, -E*qe+Fe, Fm-Fe}, {-d*h*L+V, -N*qe+Q, dt, -E*qe+Fe}, {-d*h*L+V, -N*qe+Q, dt, Fm-Fe}, {-d*h*L+V, -N*qe+Q, -E*qe+Fe, Fm-Fe}, {-d*h*L+V, dt, -E*qe+Fe, Fm-Fe}, {-V*n+N, -N*qe+Q, dt, -E*qe+Fe}, {-V*n+N, -N*qe+Q, dt, Fm-Fe}, {-V*n+N, -N*qe+Q, -E*qe+Fe, Fm-Fe}, {-V*n+N, dt, -E*qe+Fe, Fm-Fe}, {-N*qe+Q, dt, -E*qe+Fe, Fm-Fe}, {-v*dt+L}, {-d*h*L+V}, {-V*n+N}, {-N*qe+Q}, {-E*qe+Fe}, {v}, {Fm-Fe}, {-v*dt+L, -d*h*L+V}, {-v*dt+L, -V*n+N}, {-v*dt+L, -N*qe+Q}, {-v*dt+L, -E*qe+Fe}, {-v*dt+L, v}, {-v*dt+L, Fm-Fe}, {-d*h*L+V, -V*n+N}, {-d*h*L+V, -N*qe+Q}, {-d*h*L+V, -E*qe+Fe}, {-d*h*L+V, v}, {-d*h*L+V, Fm-Fe}, {-V*n+N, -N*qe+Q}, {-V*n+N, -E*qe+Fe}, {-V*n+N, v}, {-V*n+N, Fm-Fe}, {-N*qe+Q, -E*qe+Fe}, {-N*qe+Q, v}, {-N*qe+Q, Fm-Fe}, {-E*qe+Fe, v}, {-E*qe+Fe, Fm-Fe}, {v, Fm-Fe}, {-v*dt+L, -d*h*L+V, -V*n+N}, {-v*dt+L, -d*h*L+V, -N*qe+Q}, {-v*dt+L, -d*h*L+V, -E*qe+Fe}, {-v*dt+L, -d*h*L+V, v}, {-v*dt+L, -d*h*L+V, Fm-Fe}, {-v*dt+L, -V*n+N, -N*qe+Q}, {-v*dt+L, -V*n+N, -E*qe+Fe}, {-v*dt+L, -V*n+N, v}, {-v*dt+L, -V*n+N, Fm-Fe}, {-v*dt+L, -N*qe+Q, -E*qe+Fe}, {-v*dt+L, -N*qe+Q, v}, {-v*dt+L, -N*qe+Q, Fm-Fe}, {-v*dt+L, -E*qe+Fe, v}, {-v*dt+L, -E*qe+Fe, Fm-Fe}, {-v*dt+L, v, Fm-Fe}, {-d*h*L+V, -V*n+N, -N*qe+Q}, {-d*h*L+V, -V*n+N, -E*qe+Fe}, {-d*h*L+V, -V*n+N, v}, {-d*h*L+V, -V*n+N, Fm-Fe}, {-d*h*L+V, -N*qe+Q, -E*qe+Fe}, {-d*h*L+V, -N*qe+Q, v}, {-d*h*L+V, -N*qe+Q, Fm-Fe}, {-d*h*L+V, -E*qe+Fe, v}, {-d*h*L+V, -E*qe+Fe, Fm-Fe}, {-d*h*L+V, v, Fm-Fe}, {-V*n+N, -N*qe+Q, -E*qe+Fe}, {-V*n+N, -N*qe+Q, v}, {-V*n+N, -N*qe+Q, Fm-Fe}, {-V*n+N, -E*qe+Fe, v}, {-V*n+N, -E*qe+Fe, Fm-Fe}, {-V*n+N, v, Fm-Fe}, {-N*qe+Q, -E*qe+Fe, v}, {-N*qe+Q, -E*qe+Fe, Fm-Fe}, {-N*qe+Q, v, Fm-Fe}, {-E*qe+Fe, v, Fm-Fe}, {-v*dt+L, -d*h*L+V, -V*n+N, -N*qe+Q}, {-v*dt+L, -d*h*L+V, -V*n+N, -E*qe+Fe}, {-v*dt+L, -d*h*L+V, -V*n+N, v}, {-v*dt+L, -d*h*L+V, -V*n+N, Fm-Fe}, {-v*dt+L, -d*h*L+V, -N*qe+Q, -E*qe+Fe}, {-v*dt+L, -d*h*L+V, -N*qe+Q, v}, {-v*dt+L, -d*h*L+V, -N*qe+Q, Fm-Fe}, {-v*dt+L, -d*h*L+V, -E*qe+Fe, v}, {-v*dt+L, -d*h*L+V, -E*qe+Fe, Fm-Fe}, {-v*dt+L, -d*h*L+V, v, Fm-Fe}, {-v*dt+L, -V*n+N, -N*qe+Q, -E*qe+Fe}, {-v*dt+L, -V*n+N, -N*qe+Q, v}, {-v*dt+L, -V*n+N, -N*qe+Q, Fm-Fe}, {-v*dt+L, -V*n+N, -E*qe+Fe, v}, {-v*dt+L, -V*n+N, -E*qe+Fe, Fm-Fe}, {-v*dt+L, -V*n+N, v, Fm-Fe}, {-v*dt+L, -N*qe+Q, -E*qe+Fe, v}, {-v*dt+L, -N*qe+Q, -E*qe+Fe, Fm-Fe}, {-v*dt+L, -N*qe+Q, v, Fm-Fe}, {-v*dt+L, -E*qe+Fe, v, Fm-Fe}, {-d*h*L+V, -V*n+N, -N*qe+Q, -E*qe+Fe}, {-d*h*L+V, -V*n+N, -N*qe+Q, v}, {-d*h*L+V, -V*n+N, -N*qe+Q, Fm-Fe}, {-d*h*L+V, -V*n+N, -E*qe+Fe, v}, {-d*h*L+V, -V*n+N, -E*qe+Fe, Fm-Fe}, {-d*h*L+V, -V*n+N, v, Fm-Fe}, {-d*h*L+V, -N*qe+Q, -E*qe+Fe, v}, {-d*h*L+V, -N*qe+Q, -E*qe+Fe, Fm-Fe}, {-d*h*L+V, -N*qe+Q, v, Fm-Fe}, {-d*h*L+V, -E*qe+Fe, v, Fm-Fe}, {-V*n+N, -N*qe+Q, -E*qe+Fe, v}, {-V*n+N, -N*qe+Q, -E*qe+Fe, Fm-Fe}, {-V*n+N, -N*qe+Q, v, Fm-Fe}, {-V*n+N, -E*qe+Fe, v, Fm-Fe}, {-N*qe+Q, -E*qe+Fe, v, Fm-Fe}};

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
f = openOut "results/hall/abduction/noiseless/3_axiom(s)_removed/combo_1_4_6/reasoning/reasoning_output.txt";
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

print("Reasoning complete. Output written to results/hall/abduction/noiseless/3_axiom(s)_removed/combo_1_4_6/reasoning/reasoning_output.txt");
