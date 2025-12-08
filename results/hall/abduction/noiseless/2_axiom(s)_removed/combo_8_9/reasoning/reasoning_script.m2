-- AI-Noether: Reasoning Template (Noiseless)
-- Tests if candidate axiom sets, when added to remaining axioms, prove targets

needsPackage("PrimaryDecomposition", Reload => true)

-- Ring definition
R = QQ[Fm, d, v, Fe, E, dt, Q, N, V, i, n, qe, B, h, L, UH, MonomialOrder => Lex];

-- Input data
remainingAxioms = toList([Fm - qe*v*B, Fe - qe*E, Fm - Fe, E*h - UH, v*dt - L, i*dt - Q, Q - N*qe]);
qList = toList([N*qe*UH - i*B*h*L]);
k = #qList;

-- Per-target variable partitions
measuredPerTarget = {{UH, h, L, i, B, N, qe}};
nonMeasuredPerTarget = {{Fm, d, v, Fe, E, dt, Q, V, n}};

-- Candidate axiom sets to test (list of lists)
candidateSets = {{}, {Fm-Fe}, {E*h-UH}, {Fe*h-qe*UH}, {v*B-E}, {N*qe-Q}, {E*qe-Fe}, {dt*i-Q}, {E*Q-Fe*N}, {v*Q-i*L}, {E*dt-B*L}, {v*dt-L}, {B*h*L-dt*UH}, {qe*B*L-Fe*dt}, {i*B*L-Fe*N}, {Fe*dt*N-Q*B*L}, {v*Fe*N-E*i*L}, {Fm-Fe, E*h-UH}, {Fm-Fe, Fe*h-qe*UH}, {Fm-Fe, v*B-E}, {Fm-Fe, N*qe-Q}, {Fm-Fe, E*qe-Fe}, {Fm-Fe, dt*i-Q}, {Fm-Fe, E*Q-Fe*N}, {Fm-Fe, v*Q-i*L}, {Fm-Fe, E*dt-B*L}, {Fm-Fe, v*dt-L}, {Fm-Fe, B*h*L-dt*UH}, {Fm-Fe, qe*B*L-Fe*dt}, {Fm-Fe, i*B*L-Fe*N}, {Fm-Fe, Fe*dt*N-Q*B*L}, {Fm-Fe, v*Fe*N-E*i*L}, {E*h-UH, Fe*h-qe*UH}, {E*h-UH, v*B-E}, {E*h-UH, N*qe-Q}, {E*h-UH, E*qe-Fe}, {E*h-UH, dt*i-Q}, {E*h-UH, E*Q-Fe*N}, {E*h-UH, v*Q-i*L}, {E*h-UH, E*dt-B*L}, {E*h-UH, v*dt-L}, {E*h-UH, B*h*L-dt*UH}, {E*h-UH, qe*B*L-Fe*dt}, {E*h-UH, i*B*L-Fe*N}, {E*h-UH, Fe*dt*N-Q*B*L}, {E*h-UH, v*Fe*N-E*i*L}, {Fe*h-qe*UH, v*B-E}, {Fe*h-qe*UH, N*qe-Q}, {Fe*h-qe*UH, E*qe-Fe}, {Fe*h-qe*UH, dt*i-Q}, {Fe*h-qe*UH, E*Q-Fe*N}, {Fe*h-qe*UH, v*Q-i*L}, {Fe*h-qe*UH, E*dt-B*L}, {Fe*h-qe*UH, v*dt-L}, {Fe*h-qe*UH, B*h*L-dt*UH}, {Fe*h-qe*UH, qe*B*L-Fe*dt}, {Fe*h-qe*UH, i*B*L-Fe*N}, {Fe*h-qe*UH, Fe*dt*N-Q*B*L}, {Fe*h-qe*UH, v*Fe*N-E*i*L}, {v*B-E, N*qe-Q}, {v*B-E, E*qe-Fe}, {v*B-E, dt*i-Q}, {v*B-E, E*Q-Fe*N}, {v*B-E, v*Q-i*L}, {v*B-E, E*dt-B*L}, {v*B-E, v*dt-L}, {v*B-E, B*h*L-dt*UH}, {v*B-E, qe*B*L-Fe*dt}, {v*B-E, i*B*L-Fe*N}, {v*B-E, Fe*dt*N-Q*B*L}, {v*B-E, v*Fe*N-E*i*L}, {N*qe-Q, E*qe-Fe}, {N*qe-Q, dt*i-Q}, {N*qe-Q, E*Q-Fe*N}, {N*qe-Q, v*Q-i*L}, {N*qe-Q, E*dt-B*L}, {N*qe-Q, v*dt-L}, {N*qe-Q, B*h*L-dt*UH}, {N*qe-Q, qe*B*L-Fe*dt}, {N*qe-Q, i*B*L-Fe*N}, {N*qe-Q, Fe*dt*N-Q*B*L}, {N*qe-Q, v*Fe*N-E*i*L}, {E*qe-Fe, dt*i-Q}, {E*qe-Fe, E*Q-Fe*N}, {E*qe-Fe, v*Q-i*L}, {E*qe-Fe, E*dt-B*L}, {E*qe-Fe, v*dt-L}, {E*qe-Fe, B*h*L-dt*UH}, {E*qe-Fe, qe*B*L-Fe*dt}, {E*qe-Fe, i*B*L-Fe*N}, {E*qe-Fe, Fe*dt*N-Q*B*L}, {E*qe-Fe, v*Fe*N-E*i*L}, {dt*i-Q, E*Q-Fe*N}, {dt*i-Q, v*Q-i*L}, {dt*i-Q, E*dt-B*L}, {dt*i-Q, v*dt-L}, {dt*i-Q, B*h*L-dt*UH}, {dt*i-Q, qe*B*L-Fe*dt}, {dt*i-Q, i*B*L-Fe*N}, {dt*i-Q, Fe*dt*N-Q*B*L}, {dt*i-Q, v*Fe*N-E*i*L}, {E*Q-Fe*N, v*Q-i*L}, {E*Q-Fe*N, E*dt-B*L}, {E*Q-Fe*N, v*dt-L}, {E*Q-Fe*N, B*h*L-dt*UH}, {E*Q-Fe*N, qe*B*L-Fe*dt}, {E*Q-Fe*N, i*B*L-Fe*N}, {E*Q-Fe*N, Fe*dt*N-Q*B*L}, {E*Q-Fe*N, v*Fe*N-E*i*L}, {v*Q-i*L, E*dt-B*L}, {v*Q-i*L, v*dt-L}, {v*Q-i*L, B*h*L-dt*UH}, {v*Q-i*L, qe*B*L-Fe*dt}, {v*Q-i*L, i*B*L-Fe*N}, {v*Q-i*L, Fe*dt*N-Q*B*L}, {v*Q-i*L, v*Fe*N-E*i*L}, {E*dt-B*L, v*dt-L}, {E*dt-B*L, B*h*L-dt*UH}, {E*dt-B*L, qe*B*L-Fe*dt}, {E*dt-B*L, i*B*L-Fe*N}, {E*dt-B*L, Fe*dt*N-Q*B*L}, {E*dt-B*L, v*Fe*N-E*i*L}, {v*dt-L, B*h*L-dt*UH}, {v*dt-L, qe*B*L-Fe*dt}, {v*dt-L, i*B*L-Fe*N}, {v*dt-L, Fe*dt*N-Q*B*L}, {v*dt-L, v*Fe*N-E*i*L}, {B*h*L-dt*UH, qe*B*L-Fe*dt}, {B*h*L-dt*UH, i*B*L-Fe*N}, {B*h*L-dt*UH, Fe*dt*N-Q*B*L}, {B*h*L-dt*UH, v*Fe*N-E*i*L}, {qe*B*L-Fe*dt, i*B*L-Fe*N}, {qe*B*L-Fe*dt, Fe*dt*N-Q*B*L}, {qe*B*L-Fe*dt, v*Fe*N-E*i*L}, {i*B*L-Fe*N, Fe*dt*N-Q*B*L}, {i*B*L-Fe*N, v*Fe*N-E*i*L}, {Fe*dt*N-Q*B*L, v*Fe*N-E*i*L}, {Fm-Fe, E*h-UH, Fe*h-qe*UH}, {Fm-Fe, E*h-UH, v*B-E}, {Fm-Fe, E*h-UH, N*qe-Q}, {Fm-Fe, E*h-UH, E*qe-Fe}, {Fm-Fe, E*h-UH, dt*i-Q}, {Fm-Fe, E*h-UH, E*Q-Fe*N}, {Fm-Fe, E*h-UH, v*Q-i*L}, {Fm-Fe, E*h-UH, E*dt-B*L}, {Fm-Fe, E*h-UH, v*dt-L}, {Fm-Fe, E*h-UH, B*h*L-dt*UH}, {Fm-Fe, E*h-UH, qe*B*L-Fe*dt}, {Fm-Fe, E*h-UH, i*B*L-Fe*N}, {Fm-Fe, E*h-UH, Fe*dt*N-Q*B*L}, {Fm-Fe, E*h-UH, v*Fe*N-E*i*L}, {Fm-Fe, Fe*h-qe*UH, v*B-E}, {Fm-Fe, Fe*h-qe*UH, N*qe-Q}, {Fm-Fe, Fe*h-qe*UH, E*qe-Fe}, {Fm-Fe, Fe*h-qe*UH, dt*i-Q}, {Fm-Fe, Fe*h-qe*UH, E*Q-Fe*N}, {Fm-Fe, Fe*h-qe*UH, v*Q-i*L}, {Fm-Fe, Fe*h-qe*UH, E*dt-B*L}, {Fm-Fe, Fe*h-qe*UH, v*dt-L}, {Fm-Fe, Fe*h-qe*UH, B*h*L-dt*UH}, {Fm-Fe, Fe*h-qe*UH, qe*B*L-Fe*dt}, {Fm-Fe, Fe*h-qe*UH, i*B*L-Fe*N}, {Fm-Fe, Fe*h-qe*UH, Fe*dt*N-Q*B*L}, {Fm-Fe, Fe*h-qe*UH, v*Fe*N-E*i*L}, {Fm-Fe, v*B-E, N*qe-Q}, {Fm-Fe, v*B-E, E*qe-Fe}, {Fm-Fe, v*B-E, dt*i-Q}, {Fm-Fe, v*B-E, E*Q-Fe*N}, {Fm-Fe, v*B-E, v*Q-i*L}, {Fm-Fe, v*B-E, E*dt-B*L}, {Fm-Fe, v*B-E, v*dt-L}, {Fm-Fe, v*B-E, B*h*L-dt*UH}, {Fm-Fe, v*B-E, qe*B*L-Fe*dt}, {Fm-Fe, v*B-E, i*B*L-Fe*N}, {Fm-Fe, v*B-E, Fe*dt*N-Q*B*L}, {Fm-Fe, v*B-E, v*Fe*N-E*i*L}, {Fm-Fe, N*qe-Q, E*qe-Fe}, {Fm-Fe, N*qe-Q, dt*i-Q}, {Fm-Fe, N*qe-Q, E*Q-Fe*N}, {Fm-Fe, N*qe-Q, v*Q-i*L}, {Fm-Fe, N*qe-Q, E*dt-B*L}, {Fm-Fe, N*qe-Q, v*dt-L}, {Fm-Fe, N*qe-Q, B*h*L-dt*UH}, {Fm-Fe, N*qe-Q, qe*B*L-Fe*dt}, {Fm-Fe, N*qe-Q, i*B*L-Fe*N}, {Fm-Fe, N*qe-Q, Fe*dt*N-Q*B*L}, {Fm-Fe, N*qe-Q, v*Fe*N-E*i*L}, {Fm-Fe, E*qe-Fe, dt*i-Q}, {Fm-Fe, E*qe-Fe, E*Q-Fe*N}, {Fm-Fe, E*qe-Fe, v*Q-i*L}, {Fm-Fe, E*qe-Fe, E*dt-B*L}, {Fm-Fe, E*qe-Fe, v*dt-L}, {Fm-Fe, E*qe-Fe, B*h*L-dt*UH}, {Fm-Fe, E*qe-Fe, qe*B*L-Fe*dt}, {Fm-Fe, E*qe-Fe, i*B*L-Fe*N}, {Fm-Fe, E*qe-Fe, Fe*dt*N-Q*B*L}, {Fm-Fe, E*qe-Fe, v*Fe*N-E*i*L}, {Fm-Fe, dt*i-Q, E*Q-Fe*N}, {Fm-Fe, dt*i-Q, v*Q-i*L}, {Fm-Fe, dt*i-Q, E*dt-B*L}, {Fm-Fe, dt*i-Q, v*dt-L}, {Fm-Fe, dt*i-Q, B*h*L-dt*UH}, {Fm-Fe, dt*i-Q, qe*B*L-Fe*dt}, {Fm-Fe, dt*i-Q, i*B*L-Fe*N}, {Fm-Fe, dt*i-Q, Fe*dt*N-Q*B*L}, {Fm-Fe, dt*i-Q, v*Fe*N-E*i*L}, {Fm-Fe, E*Q-Fe*N, v*Q-i*L}, {Fm-Fe, E*Q-Fe*N, E*dt-B*L}, {Fm-Fe, E*Q-Fe*N, v*dt-L}, {Fm-Fe, E*Q-Fe*N, B*h*L-dt*UH}, {Fm-Fe, E*Q-Fe*N, qe*B*L-Fe*dt}, {Fm-Fe, E*Q-Fe*N, i*B*L-Fe*N}, {Fm-Fe, E*Q-Fe*N, Fe*dt*N-Q*B*L}, {Fm-Fe, E*Q-Fe*N, v*Fe*N-E*i*L}, {Fm-Fe, v*Q-i*L, E*dt-B*L}, {Fm-Fe, v*Q-i*L, v*dt-L}, {Fm-Fe, v*Q-i*L, B*h*L-dt*UH}, {Fm-Fe, v*Q-i*L, qe*B*L-Fe*dt}, {Fm-Fe, v*Q-i*L, i*B*L-Fe*N}, {Fm-Fe, v*Q-i*L, Fe*dt*N-Q*B*L}, {Fm-Fe, v*Q-i*L, v*Fe*N-E*i*L}, {Fm-Fe, E*dt-B*L, v*dt-L}, {Fm-Fe, E*dt-B*L, B*h*L-dt*UH}, {Fm-Fe, E*dt-B*L, qe*B*L-Fe*dt}, {Fm-Fe, E*dt-B*L, i*B*L-Fe*N}, {Fm-Fe, E*dt-B*L, Fe*dt*N-Q*B*L}, {Fm-Fe, E*dt-B*L, v*Fe*N-E*i*L}, {Fm-Fe, v*dt-L, B*h*L-dt*UH}, {Fm-Fe, v*dt-L, qe*B*L-Fe*dt}, {Fm-Fe, v*dt-L, i*B*L-Fe*N}, {Fm-Fe, v*dt-L, Fe*dt*N-Q*B*L}, {Fm-Fe, v*dt-L, v*Fe*N-E*i*L}, {Fm-Fe, B*h*L-dt*UH, qe*B*L-Fe*dt}, {Fm-Fe, B*h*L-dt*UH, i*B*L-Fe*N}, {Fm-Fe, B*h*L-dt*UH, Fe*dt*N-Q*B*L}, {Fm-Fe, B*h*L-dt*UH, v*Fe*N-E*i*L}, {Fm-Fe, qe*B*L-Fe*dt, i*B*L-Fe*N}, {Fm-Fe, qe*B*L-Fe*dt, Fe*dt*N-Q*B*L}, {Fm-Fe, qe*B*L-Fe*dt, v*Fe*N-E*i*L}, {Fm-Fe, i*B*L-Fe*N, Fe*dt*N-Q*B*L}, {Fm-Fe, i*B*L-Fe*N, v*Fe*N-E*i*L}, {Fm-Fe, Fe*dt*N-Q*B*L, v*Fe*N-E*i*L}, {E*h-UH, Fe*h-qe*UH, v*B-E}, {E*h-UH, Fe*h-qe*UH, N*qe-Q}, {E*h-UH, Fe*h-qe*UH, E*qe-Fe}, {E*h-UH, Fe*h-qe*UH, dt*i-Q}, {E*h-UH, Fe*h-qe*UH, E*Q-Fe*N}, {E*h-UH, Fe*h-qe*UH, v*Q-i*L}, {E*h-UH, Fe*h-qe*UH, E*dt-B*L}, {E*h-UH, Fe*h-qe*UH, v*dt-L}, {E*h-UH, Fe*h-qe*UH, B*h*L-dt*UH}, {E*h-UH, Fe*h-qe*UH, qe*B*L-Fe*dt}, {E*h-UH, Fe*h-qe*UH, i*B*L-Fe*N}, {E*h-UH, Fe*h-qe*UH, Fe*dt*N-Q*B*L}, {E*h-UH, Fe*h-qe*UH, v*Fe*N-E*i*L}, {E*h-UH, v*B-E, N*qe-Q}, {E*h-UH, v*B-E, E*qe-Fe}, {E*h-UH, v*B-E, dt*i-Q}, {E*h-UH, v*B-E, E*Q-Fe*N}, {E*h-UH, v*B-E, v*Q-i*L}, {E*h-UH, v*B-E, E*dt-B*L}, {E*h-UH, v*B-E, v*dt-L}, {E*h-UH, v*B-E, B*h*L-dt*UH}, {E*h-UH, v*B-E, qe*B*L-Fe*dt}, {E*h-UH, v*B-E, i*B*L-Fe*N}, {E*h-UH, v*B-E, Fe*dt*N-Q*B*L}, {E*h-UH, v*B-E, v*Fe*N-E*i*L}, {E*h-UH, N*qe-Q, E*qe-Fe}, {E*h-UH, N*qe-Q, dt*i-Q}, {E*h-UH, N*qe-Q, E*Q-Fe*N}, {E*h-UH, N*qe-Q, v*Q-i*L}, {E*h-UH, N*qe-Q, E*dt-B*L}, {E*h-UH, N*qe-Q, v*dt-L}, {E*h-UH, N*qe-Q, B*h*L-dt*UH}, {E*h-UH, N*qe-Q, qe*B*L-Fe*dt}, {E*h-UH, N*qe-Q, i*B*L-Fe*N}, {E*h-UH, N*qe-Q, Fe*dt*N-Q*B*L}, {E*h-UH, N*qe-Q, v*Fe*N-E*i*L}, {E*h-UH, E*qe-Fe, dt*i-Q}, {E*h-UH, E*qe-Fe, E*Q-Fe*N}, {E*h-UH, E*qe-Fe, v*Q-i*L}, {E*h-UH, E*qe-Fe, E*dt-B*L}, {E*h-UH, E*qe-Fe, v*dt-L}, {E*h-UH, E*qe-Fe, B*h*L-dt*UH}, {E*h-UH, E*qe-Fe, qe*B*L-Fe*dt}, {E*h-UH, E*qe-Fe, i*B*L-Fe*N}, {E*h-UH, E*qe-Fe, Fe*dt*N-Q*B*L}, {E*h-UH, E*qe-Fe, v*Fe*N-E*i*L}, {E*h-UH, dt*i-Q, E*Q-Fe*N}, {E*h-UH, dt*i-Q, v*Q-i*L}, {E*h-UH, dt*i-Q, E*dt-B*L}, {E*h-UH, dt*i-Q, v*dt-L}, {E*h-UH, dt*i-Q, B*h*L-dt*UH}, {E*h-UH, dt*i-Q, qe*B*L-Fe*dt}, {E*h-UH, dt*i-Q, i*B*L-Fe*N}, {E*h-UH, dt*i-Q, Fe*dt*N-Q*B*L}, {E*h-UH, dt*i-Q, v*Fe*N-E*i*L}, {E*h-UH, E*Q-Fe*N, v*Q-i*L}, {E*h-UH, E*Q-Fe*N, E*dt-B*L}, {E*h-UH, E*Q-Fe*N, v*dt-L}, {E*h-UH, E*Q-Fe*N, B*h*L-dt*UH}, {E*h-UH, E*Q-Fe*N, qe*B*L-Fe*dt}, {E*h-UH, E*Q-Fe*N, i*B*L-Fe*N}, {E*h-UH, E*Q-Fe*N, Fe*dt*N-Q*B*L}, {E*h-UH, E*Q-Fe*N, v*Fe*N-E*i*L}, {E*h-UH, v*Q-i*L, E*dt-B*L}, {E*h-UH, v*Q-i*L, v*dt-L}, {E*h-UH, v*Q-i*L, B*h*L-dt*UH}, {E*h-UH, v*Q-i*L, qe*B*L-Fe*dt}, {E*h-UH, v*Q-i*L, i*B*L-Fe*N}, {E*h-UH, v*Q-i*L, Fe*dt*N-Q*B*L}, {E*h-UH, v*Q-i*L, v*Fe*N-E*i*L}, {E*h-UH, E*dt-B*L, v*dt-L}, {E*h-UH, E*dt-B*L, B*h*L-dt*UH}, {E*h-UH, E*dt-B*L, qe*B*L-Fe*dt}, {E*h-UH, E*dt-B*L, i*B*L-Fe*N}, {E*h-UH, E*dt-B*L, Fe*dt*N-Q*B*L}, {E*h-UH, E*dt-B*L, v*Fe*N-E*i*L}, {E*h-UH, v*dt-L, B*h*L-dt*UH}, {E*h-UH, v*dt-L, qe*B*L-Fe*dt}, {E*h-UH, v*dt-L, i*B*L-Fe*N}, {E*h-UH, v*dt-L, Fe*dt*N-Q*B*L}, {E*h-UH, v*dt-L, v*Fe*N-E*i*L}, {E*h-UH, B*h*L-dt*UH, qe*B*L-Fe*dt}, {E*h-UH, B*h*L-dt*UH, i*B*L-Fe*N}, {E*h-UH, B*h*L-dt*UH, Fe*dt*N-Q*B*L}, {E*h-UH, B*h*L-dt*UH, v*Fe*N-E*i*L}, {E*h-UH, qe*B*L-Fe*dt, i*B*L-Fe*N}, {E*h-UH, qe*B*L-Fe*dt, Fe*dt*N-Q*B*L}, {E*h-UH, qe*B*L-Fe*dt, v*Fe*N-E*i*L}, {E*h-UH, i*B*L-Fe*N, Fe*dt*N-Q*B*L}, {E*h-UH, i*B*L-Fe*N, v*Fe*N-E*i*L}, {E*h-UH, Fe*dt*N-Q*B*L, v*Fe*N-E*i*L}, {Fe*h-qe*UH, v*B-E, N*qe-Q}, {Fe*h-qe*UH, v*B-E, E*qe-Fe}, {Fe*h-qe*UH, v*B-E, dt*i-Q}, {Fe*h-qe*UH, v*B-E, E*Q-Fe*N}, {Fe*h-qe*UH, v*B-E, v*Q-i*L}, {Fe*h-qe*UH, v*B-E, E*dt-B*L}, {Fe*h-qe*UH, v*B-E, v*dt-L}, {Fe*h-qe*UH, v*B-E, B*h*L-dt*UH}, {Fe*h-qe*UH, v*B-E, qe*B*L-Fe*dt}, {Fe*h-qe*UH, v*B-E, i*B*L-Fe*N}, {Fe*h-qe*UH, v*B-E, Fe*dt*N-Q*B*L}, {Fe*h-qe*UH, v*B-E, v*Fe*N-E*i*L}, {Fe*h-qe*UH, N*qe-Q, E*qe-Fe}, {Fe*h-qe*UH, N*qe-Q, dt*i-Q}, {Fe*h-qe*UH, N*qe-Q, E*Q-Fe*N}, {Fe*h-qe*UH, N*qe-Q, v*Q-i*L}, {Fe*h-qe*UH, N*qe-Q, E*dt-B*L}, {Fe*h-qe*UH, N*qe-Q, v*dt-L}, {Fe*h-qe*UH, N*qe-Q, B*h*L-dt*UH}, {Fe*h-qe*UH, N*qe-Q, qe*B*L-Fe*dt}, {Fe*h-qe*UH, N*qe-Q, i*B*L-Fe*N}, {Fe*h-qe*UH, N*qe-Q, Fe*dt*N-Q*B*L}, {Fe*h-qe*UH, N*qe-Q, v*Fe*N-E*i*L}, {Fe*h-qe*UH, E*qe-Fe, dt*i-Q}, {Fe*h-qe*UH, E*qe-Fe, E*Q-Fe*N}, {Fe*h-qe*UH, E*qe-Fe, v*Q-i*L}, {Fe*h-qe*UH, E*qe-Fe, E*dt-B*L}, {Fe*h-qe*UH, E*qe-Fe, v*dt-L}, {Fe*h-qe*UH, E*qe-Fe, B*h*L-dt*UH}, {Fe*h-qe*UH, E*qe-Fe, qe*B*L-Fe*dt}, {Fe*h-qe*UH, E*qe-Fe, i*B*L-Fe*N}, {Fe*h-qe*UH, E*qe-Fe, Fe*dt*N-Q*B*L}, {Fe*h-qe*UH, E*qe-Fe, v*Fe*N-E*i*L}, {Fe*h-qe*UH, dt*i-Q, E*Q-Fe*N}, {Fe*h-qe*UH, dt*i-Q, v*Q-i*L}, {Fe*h-qe*UH, dt*i-Q, E*dt-B*L}, {Fe*h-qe*UH, dt*i-Q, v*dt-L}, {Fe*h-qe*UH, dt*i-Q, B*h*L-dt*UH}, {Fe*h-qe*UH, dt*i-Q, qe*B*L-Fe*dt}, {Fe*h-qe*UH, dt*i-Q, i*B*L-Fe*N}, {Fe*h-qe*UH, dt*i-Q, Fe*dt*N-Q*B*L}, {Fe*h-qe*UH, dt*i-Q, v*Fe*N-E*i*L}, {Fe*h-qe*UH, E*Q-Fe*N, v*Q-i*L}, {Fe*h-qe*UH, E*Q-Fe*N, E*dt-B*L}, {Fe*h-qe*UH, E*Q-Fe*N, v*dt-L}, {Fe*h-qe*UH, E*Q-Fe*N, B*h*L-dt*UH}, {Fe*h-qe*UH, E*Q-Fe*N, qe*B*L-Fe*dt}, {Fe*h-qe*UH, E*Q-Fe*N, i*B*L-Fe*N}, {Fe*h-qe*UH, E*Q-Fe*N, Fe*dt*N-Q*B*L}, {Fe*h-qe*UH, E*Q-Fe*N, v*Fe*N-E*i*L}, {Fe*h-qe*UH, v*Q-i*L, E*dt-B*L}, {Fe*h-qe*UH, v*Q-i*L, v*dt-L}, {Fe*h-qe*UH, v*Q-i*L, B*h*L-dt*UH}, {Fe*h-qe*UH, v*Q-i*L, qe*B*L-Fe*dt}, {Fe*h-qe*UH, v*Q-i*L, i*B*L-Fe*N}, {Fe*h-qe*UH, v*Q-i*L, Fe*dt*N-Q*B*L}, {Fe*h-qe*UH, v*Q-i*L, v*Fe*N-E*i*L}, {Fe*h-qe*UH, E*dt-B*L, v*dt-L}, {Fe*h-qe*UH, E*dt-B*L, B*h*L-dt*UH}, {Fe*h-qe*UH, E*dt-B*L, qe*B*L-Fe*dt}, {Fe*h-qe*UH, E*dt-B*L, i*B*L-Fe*N}, {Fe*h-qe*UH, E*dt-B*L, Fe*dt*N-Q*B*L}, {Fe*h-qe*UH, E*dt-B*L, v*Fe*N-E*i*L}, {Fe*h-qe*UH, v*dt-L, B*h*L-dt*UH}, {Fe*h-qe*UH, v*dt-L, qe*B*L-Fe*dt}, {Fe*h-qe*UH, v*dt-L, i*B*L-Fe*N}, {Fe*h-qe*UH, v*dt-L, Fe*dt*N-Q*B*L}, {Fe*h-qe*UH, v*dt-L, v*Fe*N-E*i*L}, {Fe*h-qe*UH, B*h*L-dt*UH, qe*B*L-Fe*dt}, {Fe*h-qe*UH, B*h*L-dt*UH, i*B*L-Fe*N}, {Fe*h-qe*UH, B*h*L-dt*UH, Fe*dt*N-Q*B*L}, {Fe*h-qe*UH, B*h*L-dt*UH, v*Fe*N-E*i*L}, {Fe*h-qe*UH, qe*B*L-Fe*dt, i*B*L-Fe*N}, {Fe*h-qe*UH, qe*B*L-Fe*dt, Fe*dt*N-Q*B*L}, {Fe*h-qe*UH, qe*B*L-Fe*dt, v*Fe*N-E*i*L}, {Fe*h-qe*UH, i*B*L-Fe*N, Fe*dt*N-Q*B*L}, {Fe*h-qe*UH, i*B*L-Fe*N, v*Fe*N-E*i*L}, {Fe*h-qe*UH, Fe*dt*N-Q*B*L, v*Fe*N-E*i*L}, {v*B-E, N*qe-Q, E*qe-Fe}, {v*B-E, N*qe-Q, dt*i-Q}, {v*B-E, N*qe-Q, E*Q-Fe*N}, {v*B-E, N*qe-Q, v*Q-i*L}, {v*B-E, N*qe-Q, E*dt-B*L}, {v*B-E, N*qe-Q, v*dt-L}, {v*B-E, N*qe-Q, B*h*L-dt*UH}, {v*B-E, N*qe-Q, qe*B*L-Fe*dt}, {v*B-E, N*qe-Q, i*B*L-Fe*N}, {v*B-E, N*qe-Q, Fe*dt*N-Q*B*L}, {v*B-E, N*qe-Q, v*Fe*N-E*i*L}, {v*B-E, E*qe-Fe, dt*i-Q}, {v*B-E, E*qe-Fe, E*Q-Fe*N}, {v*B-E, E*qe-Fe, v*Q-i*L}, {v*B-E, E*qe-Fe, E*dt-B*L}, {v*B-E, E*qe-Fe, v*dt-L}, {v*B-E, E*qe-Fe, B*h*L-dt*UH}, {v*B-E, E*qe-Fe, qe*B*L-Fe*dt}, {v*B-E, E*qe-Fe, i*B*L-Fe*N}, {v*B-E, E*qe-Fe, Fe*dt*N-Q*B*L}, {v*B-E, E*qe-Fe, v*Fe*N-E*i*L}, {v*B-E, dt*i-Q, E*Q-Fe*N}, {v*B-E, dt*i-Q, v*Q-i*L}, {v*B-E, dt*i-Q, E*dt-B*L}, {v*B-E, dt*i-Q, v*dt-L}, {v*B-E, dt*i-Q, B*h*L-dt*UH}, {v*B-E, dt*i-Q, qe*B*L-Fe*dt}, {v*B-E, dt*i-Q, i*B*L-Fe*N}, {v*B-E, dt*i-Q, Fe*dt*N-Q*B*L}, {v*B-E, dt*i-Q, v*Fe*N-E*i*L}, {v*B-E, E*Q-Fe*N, v*Q-i*L}, {v*B-E, E*Q-Fe*N, E*dt-B*L}, {v*B-E, E*Q-Fe*N, v*dt-L}, {v*B-E, E*Q-Fe*N, B*h*L-dt*UH}, {v*B-E, E*Q-Fe*N, qe*B*L-Fe*dt}, {v*B-E, E*Q-Fe*N, i*B*L-Fe*N}, {v*B-E, E*Q-Fe*N, Fe*dt*N-Q*B*L}, {v*B-E, E*Q-Fe*N, v*Fe*N-E*i*L}, {v*B-E, v*Q-i*L, E*dt-B*L}, {v*B-E, v*Q-i*L, v*dt-L}, {v*B-E, v*Q-i*L, B*h*L-dt*UH}, {v*B-E, v*Q-i*L, qe*B*L-Fe*dt}, {v*B-E, v*Q-i*L, i*B*L-Fe*N}, {v*B-E, v*Q-i*L, Fe*dt*N-Q*B*L}, {v*B-E, v*Q-i*L, v*Fe*N-E*i*L}, {v*B-E, E*dt-B*L, v*dt-L}, {v*B-E, E*dt-B*L, B*h*L-dt*UH}, {v*B-E, E*dt-B*L, qe*B*L-Fe*dt}, {v*B-E, E*dt-B*L, i*B*L-Fe*N}, {v*B-E, E*dt-B*L, Fe*dt*N-Q*B*L}, {v*B-E, E*dt-B*L, v*Fe*N-E*i*L}, {v*B-E, v*dt-L, B*h*L-dt*UH}, {v*B-E, v*dt-L, qe*B*L-Fe*dt}, {v*B-E, v*dt-L, i*B*L-Fe*N}, {v*B-E, v*dt-L, Fe*dt*N-Q*B*L}, {v*B-E, v*dt-L, v*Fe*N-E*i*L}, {v*B-E, B*h*L-dt*UH, qe*B*L-Fe*dt}, {v*B-E, B*h*L-dt*UH, i*B*L-Fe*N}, {v*B-E, B*h*L-dt*UH, Fe*dt*N-Q*B*L}, {v*B-E, B*h*L-dt*UH, v*Fe*N-E*i*L}, {v*B-E, qe*B*L-Fe*dt, i*B*L-Fe*N}, {v*B-E, qe*B*L-Fe*dt, Fe*dt*N-Q*B*L}, {v*B-E, qe*B*L-Fe*dt, v*Fe*N-E*i*L}, {v*B-E, i*B*L-Fe*N, Fe*dt*N-Q*B*L}, {v*B-E, i*B*L-Fe*N, v*Fe*N-E*i*L}, {v*B-E, Fe*dt*N-Q*B*L, v*Fe*N-E*i*L}, {N*qe-Q, E*qe-Fe, dt*i-Q}, {N*qe-Q, E*qe-Fe, E*Q-Fe*N}, {N*qe-Q, E*qe-Fe, v*Q-i*L}, {N*qe-Q, E*qe-Fe, E*dt-B*L}, {N*qe-Q, E*qe-Fe, v*dt-L}, {N*qe-Q, E*qe-Fe, B*h*L-dt*UH}, {N*qe-Q, E*qe-Fe, qe*B*L-Fe*dt}, {N*qe-Q, E*qe-Fe, i*B*L-Fe*N}, {N*qe-Q, E*qe-Fe, Fe*dt*N-Q*B*L}, {N*qe-Q, E*qe-Fe, v*Fe*N-E*i*L}, {N*qe-Q, dt*i-Q, E*Q-Fe*N}, {N*qe-Q, dt*i-Q, v*Q-i*L}, {N*qe-Q, dt*i-Q, E*dt-B*L}, {N*qe-Q, dt*i-Q, v*dt-L}, {N*qe-Q, dt*i-Q, B*h*L-dt*UH}, {N*qe-Q, dt*i-Q, qe*B*L-Fe*dt}, {N*qe-Q, dt*i-Q, i*B*L-Fe*N}, {N*qe-Q, dt*i-Q, Fe*dt*N-Q*B*L}, {N*qe-Q, dt*i-Q, v*Fe*N-E*i*L}, {N*qe-Q, E*Q-Fe*N, v*Q-i*L}, {N*qe-Q, E*Q-Fe*N, E*dt-B*L}, {N*qe-Q, E*Q-Fe*N, v*dt-L}, {N*qe-Q, E*Q-Fe*N, B*h*L-dt*UH}, {N*qe-Q, E*Q-Fe*N, qe*B*L-Fe*dt}, {N*qe-Q, E*Q-Fe*N, i*B*L-Fe*N}, {N*qe-Q, E*Q-Fe*N, Fe*dt*N-Q*B*L}, {N*qe-Q, E*Q-Fe*N, v*Fe*N-E*i*L}, {N*qe-Q, v*Q-i*L, E*dt-B*L}, {N*qe-Q, v*Q-i*L, v*dt-L}, {N*qe-Q, v*Q-i*L, B*h*L-dt*UH}, {N*qe-Q, v*Q-i*L, qe*B*L-Fe*dt}, {N*qe-Q, v*Q-i*L, i*B*L-Fe*N}, {N*qe-Q, v*Q-i*L, Fe*dt*N-Q*B*L}, {N*qe-Q, v*Q-i*L, v*Fe*N-E*i*L}, {N*qe-Q, E*dt-B*L, v*dt-L}, {N*qe-Q, E*dt-B*L, B*h*L-dt*UH}, {N*qe-Q, E*dt-B*L, qe*B*L-Fe*dt}, {N*qe-Q, E*dt-B*L, i*B*L-Fe*N}, {N*qe-Q, E*dt-B*L, Fe*dt*N-Q*B*L}, {N*qe-Q, E*dt-B*L, v*Fe*N-E*i*L}, {N*qe-Q, v*dt-L, B*h*L-dt*UH}, {N*qe-Q, v*dt-L, qe*B*L-Fe*dt}, {N*qe-Q, v*dt-L, i*B*L-Fe*N}, {N*qe-Q, v*dt-L, Fe*dt*N-Q*B*L}, {N*qe-Q, v*dt-L, v*Fe*N-E*i*L}, {N*qe-Q, B*h*L-dt*UH, qe*B*L-Fe*dt}, {N*qe-Q, B*h*L-dt*UH, i*B*L-Fe*N}, {N*qe-Q, B*h*L-dt*UH, Fe*dt*N-Q*B*L}, {N*qe-Q, B*h*L-dt*UH, v*Fe*N-E*i*L}, {N*qe-Q, qe*B*L-Fe*dt, i*B*L-Fe*N}, {N*qe-Q, qe*B*L-Fe*dt, Fe*dt*N-Q*B*L}, {N*qe-Q, qe*B*L-Fe*dt, v*Fe*N-E*i*L}, {N*qe-Q, i*B*L-Fe*N, Fe*dt*N-Q*B*L}, {N*qe-Q, i*B*L-Fe*N, v*Fe*N-E*i*L}, {N*qe-Q, Fe*dt*N-Q*B*L, v*Fe*N-E*i*L}, {E*qe-Fe, dt*i-Q, E*Q-Fe*N}, {E*qe-Fe, dt*i-Q, v*Q-i*L}, {E*qe-Fe, dt*i-Q, E*dt-B*L}, {E*qe-Fe, dt*i-Q, v*dt-L}, {E*qe-Fe, dt*i-Q, B*h*L-dt*UH}, {E*qe-Fe, dt*i-Q, qe*B*L-Fe*dt}, {E*qe-Fe, dt*i-Q, i*B*L-Fe*N}, {E*qe-Fe, dt*i-Q, Fe*dt*N-Q*B*L}, {E*qe-Fe, dt*i-Q, v*Fe*N-E*i*L}, {E*qe-Fe, E*Q-Fe*N, v*Q-i*L}, {E*qe-Fe, E*Q-Fe*N, E*dt-B*L}, {E*qe-Fe, E*Q-Fe*N, v*dt-L}, {E*qe-Fe, E*Q-Fe*N, B*h*L-dt*UH}, {E*qe-Fe, E*Q-Fe*N, qe*B*L-Fe*dt}, {E*qe-Fe, E*Q-Fe*N, i*B*L-Fe*N}, {E*qe-Fe, E*Q-Fe*N, Fe*dt*N-Q*B*L}, {E*qe-Fe, E*Q-Fe*N, v*Fe*N-E*i*L}, {E*qe-Fe, v*Q-i*L, E*dt-B*L}, {E*qe-Fe, v*Q-i*L, v*dt-L}, {E*qe-Fe, v*Q-i*L, B*h*L-dt*UH}, {E*qe-Fe, v*Q-i*L, qe*B*L-Fe*dt}, {E*qe-Fe, v*Q-i*L, i*B*L-Fe*N}, {E*qe-Fe, v*Q-i*L, Fe*dt*N-Q*B*L}, {E*qe-Fe, v*Q-i*L, v*Fe*N-E*i*L}, {E*qe-Fe, E*dt-B*L, v*dt-L}, {E*qe-Fe, E*dt-B*L, B*h*L-dt*UH}, {E*qe-Fe, E*dt-B*L, qe*B*L-Fe*dt}, {E*qe-Fe, E*dt-B*L, i*B*L-Fe*N}, {E*qe-Fe, E*dt-B*L, Fe*dt*N-Q*B*L}, {E*qe-Fe, E*dt-B*L, v*Fe*N-E*i*L}, {E*qe-Fe, v*dt-L, B*h*L-dt*UH}, {E*qe-Fe, v*dt-L, qe*B*L-Fe*dt}, {E*qe-Fe, v*dt-L, i*B*L-Fe*N}, {E*qe-Fe, v*dt-L, Fe*dt*N-Q*B*L}, {E*qe-Fe, v*dt-L, v*Fe*N-E*i*L}, {E*qe-Fe, B*h*L-dt*UH, qe*B*L-Fe*dt}, {E*qe-Fe, B*h*L-dt*UH, i*B*L-Fe*N}, {E*qe-Fe, B*h*L-dt*UH, Fe*dt*N-Q*B*L}, {E*qe-Fe, B*h*L-dt*UH, v*Fe*N-E*i*L}, {E*qe-Fe, qe*B*L-Fe*dt, i*B*L-Fe*N}, {E*qe-Fe, qe*B*L-Fe*dt, Fe*dt*N-Q*B*L}, {E*qe-Fe, qe*B*L-Fe*dt, v*Fe*N-E*i*L}, {E*qe-Fe, i*B*L-Fe*N, Fe*dt*N-Q*B*L}, {E*qe-Fe, i*B*L-Fe*N, v*Fe*N-E*i*L}, {E*qe-Fe, Fe*dt*N-Q*B*L, v*Fe*N-E*i*L}, {dt*i-Q, E*Q-Fe*N, v*Q-i*L}, {dt*i-Q, E*Q-Fe*N, E*dt-B*L}, {dt*i-Q, E*Q-Fe*N, v*dt-L}, {dt*i-Q, E*Q-Fe*N, B*h*L-dt*UH}, {dt*i-Q, E*Q-Fe*N, qe*B*L-Fe*dt}, {dt*i-Q, E*Q-Fe*N, i*B*L-Fe*N}, {dt*i-Q, E*Q-Fe*N, Fe*dt*N-Q*B*L}, {dt*i-Q, E*Q-Fe*N, v*Fe*N-E*i*L}, {dt*i-Q, v*Q-i*L, E*dt-B*L}, {dt*i-Q, v*Q-i*L, v*dt-L}, {dt*i-Q, v*Q-i*L, B*h*L-dt*UH}, {dt*i-Q, v*Q-i*L, qe*B*L-Fe*dt}, {dt*i-Q, v*Q-i*L, i*B*L-Fe*N}, {dt*i-Q, v*Q-i*L, Fe*dt*N-Q*B*L}, {dt*i-Q, v*Q-i*L, v*Fe*N-E*i*L}, {dt*i-Q, E*dt-B*L, v*dt-L}, {dt*i-Q, E*dt-B*L, B*h*L-dt*UH}, {dt*i-Q, E*dt-B*L, qe*B*L-Fe*dt}, {dt*i-Q, E*dt-B*L, i*B*L-Fe*N}, {dt*i-Q, E*dt-B*L, Fe*dt*N-Q*B*L}, {dt*i-Q, E*dt-B*L, v*Fe*N-E*i*L}, {dt*i-Q, v*dt-L, B*h*L-dt*UH}, {dt*i-Q, v*dt-L, qe*B*L-Fe*dt}, {dt*i-Q, v*dt-L, i*B*L-Fe*N}, {dt*i-Q, v*dt-L, Fe*dt*N-Q*B*L}, {dt*i-Q, v*dt-L, v*Fe*N-E*i*L}, {dt*i-Q, B*h*L-dt*UH, qe*B*L-Fe*dt}, {dt*i-Q, B*h*L-dt*UH, i*B*L-Fe*N}, {dt*i-Q, B*h*L-dt*UH, Fe*dt*N-Q*B*L}, {dt*i-Q, B*h*L-dt*UH, v*Fe*N-E*i*L}, {dt*i-Q, qe*B*L-Fe*dt, i*B*L-Fe*N}, {dt*i-Q, qe*B*L-Fe*dt, Fe*dt*N-Q*B*L}, {dt*i-Q, qe*B*L-Fe*dt, v*Fe*N-E*i*L}, {dt*i-Q, i*B*L-Fe*N, Fe*dt*N-Q*B*L}, {dt*i-Q, i*B*L-Fe*N, v*Fe*N-E*i*L}, {dt*i-Q, Fe*dt*N-Q*B*L, v*Fe*N-E*i*L}, {E*Q-Fe*N, v*Q-i*L, E*dt-B*L}, {E*Q-Fe*N, v*Q-i*L, v*dt-L}, {E*Q-Fe*N, v*Q-i*L, B*h*L-dt*UH}, {E*Q-Fe*N, v*Q-i*L, qe*B*L-Fe*dt}, {E*Q-Fe*N, v*Q-i*L, i*B*L-Fe*N}, {E*Q-Fe*N, v*Q-i*L, Fe*dt*N-Q*B*L}, {E*Q-Fe*N, v*Q-i*L, v*Fe*N-E*i*L}, {E*Q-Fe*N, E*dt-B*L, v*dt-L}, {E*Q-Fe*N, E*dt-B*L, B*h*L-dt*UH}, {E*Q-Fe*N, E*dt-B*L, qe*B*L-Fe*dt}, {E*Q-Fe*N, E*dt-B*L, i*B*L-Fe*N}, {E*Q-Fe*N, E*dt-B*L, Fe*dt*N-Q*B*L}, {E*Q-Fe*N, E*dt-B*L, v*Fe*N-E*i*L}, {E*Q-Fe*N, v*dt-L, B*h*L-dt*UH}, {E*Q-Fe*N, v*dt-L, qe*B*L-Fe*dt}, {E*Q-Fe*N, v*dt-L, i*B*L-Fe*N}, {E*Q-Fe*N, v*dt-L, Fe*dt*N-Q*B*L}, {E*Q-Fe*N, v*dt-L, v*Fe*N-E*i*L}, {E*Q-Fe*N, B*h*L-dt*UH, qe*B*L-Fe*dt}, {E*Q-Fe*N, B*h*L-dt*UH, i*B*L-Fe*N}, {E*Q-Fe*N, B*h*L-dt*UH, Fe*dt*N-Q*B*L}, {E*Q-Fe*N, B*h*L-dt*UH, v*Fe*N-E*i*L}, {E*Q-Fe*N, qe*B*L-Fe*dt, i*B*L-Fe*N}, {E*Q-Fe*N, qe*B*L-Fe*dt, Fe*dt*N-Q*B*L}, {E*Q-Fe*N, qe*B*L-Fe*dt, v*Fe*N-E*i*L}, {E*Q-Fe*N, i*B*L-Fe*N, Fe*dt*N-Q*B*L}, {E*Q-Fe*N, i*B*L-Fe*N, v*Fe*N-E*i*L}, {E*Q-Fe*N, Fe*dt*N-Q*B*L, v*Fe*N-E*i*L}, {v*Q-i*L, E*dt-B*L, v*dt-L}, {v*Q-i*L, E*dt-B*L, B*h*L-dt*UH}, {v*Q-i*L, E*dt-B*L, qe*B*L-Fe*dt}, {v*Q-i*L, E*dt-B*L, i*B*L-Fe*N}, {v*Q-i*L, E*dt-B*L, Fe*dt*N-Q*B*L}, {v*Q-i*L, E*dt-B*L, v*Fe*N-E*i*L}, {v*Q-i*L, v*dt-L, B*h*L-dt*UH}, {v*Q-i*L, v*dt-L, qe*B*L-Fe*dt}, {v*Q-i*L, v*dt-L, i*B*L-Fe*N}, {v*Q-i*L, v*dt-L, Fe*dt*N-Q*B*L}, {v*Q-i*L, v*dt-L, v*Fe*N-E*i*L}, {v*Q-i*L, B*h*L-dt*UH, qe*B*L-Fe*dt}, {v*Q-i*L, B*h*L-dt*UH, i*B*L-Fe*N}, {v*Q-i*L, B*h*L-dt*UH, Fe*dt*N-Q*B*L}, {v*Q-i*L, B*h*L-dt*UH, v*Fe*N-E*i*L}, {v*Q-i*L, qe*B*L-Fe*dt, i*B*L-Fe*N}, {v*Q-i*L, qe*B*L-Fe*dt, Fe*dt*N-Q*B*L}, {v*Q-i*L, qe*B*L-Fe*dt, v*Fe*N-E*i*L}, {v*Q-i*L, i*B*L-Fe*N, Fe*dt*N-Q*B*L}, {v*Q-i*L, i*B*L-Fe*N, v*Fe*N-E*i*L}, {v*Q-i*L, Fe*dt*N-Q*B*L, v*Fe*N-E*i*L}, {E*dt-B*L, v*dt-L, B*h*L-dt*UH}, {E*dt-B*L, v*dt-L, qe*B*L-Fe*dt}, {E*dt-B*L, v*dt-L, i*B*L-Fe*N}, {E*dt-B*L, v*dt-L, Fe*dt*N-Q*B*L}, {E*dt-B*L, v*dt-L, v*Fe*N-E*i*L}, {E*dt-B*L, B*h*L-dt*UH, qe*B*L-Fe*dt}, {E*dt-B*L, B*h*L-dt*UH, i*B*L-Fe*N}, {E*dt-B*L, B*h*L-dt*UH, Fe*dt*N-Q*B*L}, {E*dt-B*L, B*h*L-dt*UH, v*Fe*N-E*i*L}, {E*dt-B*L, qe*B*L-Fe*dt, i*B*L-Fe*N}, {E*dt-B*L, qe*B*L-Fe*dt, Fe*dt*N-Q*B*L}, {E*dt-B*L, qe*B*L-Fe*dt, v*Fe*N-E*i*L}, {E*dt-B*L, i*B*L-Fe*N, Fe*dt*N-Q*B*L}, {E*dt-B*L, i*B*L-Fe*N, v*Fe*N-E*i*L}, {E*dt-B*L, Fe*dt*N-Q*B*L, v*Fe*N-E*i*L}, {v*dt-L, B*h*L-dt*UH, qe*B*L-Fe*dt}, {v*dt-L, B*h*L-dt*UH, i*B*L-Fe*N}, {v*dt-L, B*h*L-dt*UH, Fe*dt*N-Q*B*L}, {v*dt-L, B*h*L-dt*UH, v*Fe*N-E*i*L}, {v*dt-L, qe*B*L-Fe*dt, i*B*L-Fe*N}, {v*dt-L, qe*B*L-Fe*dt, Fe*dt*N-Q*B*L}, {v*dt-L, qe*B*L-Fe*dt, v*Fe*N-E*i*L}, {v*dt-L, i*B*L-Fe*N, Fe*dt*N-Q*B*L}, {v*dt-L, i*B*L-Fe*N, v*Fe*N-E*i*L}, {v*dt-L, Fe*dt*N-Q*B*L, v*Fe*N-E*i*L}, {B*h*L-dt*UH, qe*B*L-Fe*dt, i*B*L-Fe*N}, {B*h*L-dt*UH, qe*B*L-Fe*dt, Fe*dt*N-Q*B*L}, {B*h*L-dt*UH, qe*B*L-Fe*dt, v*Fe*N-E*i*L}, {B*h*L-dt*UH, i*B*L-Fe*N, Fe*dt*N-Q*B*L}, {B*h*L-dt*UH, i*B*L-Fe*N, v*Fe*N-E*i*L}, {B*h*L-dt*UH, Fe*dt*N-Q*B*L, v*Fe*N-E*i*L}, {qe*B*L-Fe*dt, i*B*L-Fe*N, Fe*dt*N-Q*B*L}, {qe*B*L-Fe*dt, i*B*L-Fe*N, v*Fe*N-E*i*L}, {qe*B*L-Fe*dt, Fe*dt*N-Q*B*L, v*Fe*N-E*i*L}, {i*B*L-Fe*N, Fe*dt*N-Q*B*L, v*Fe*N-E*i*L}, {qe}, {i}, {Q}, {Fe}, {Fm}, {E*h-UH}, {v*dt-L}, {qe, i}, {qe, Q}, {qe, Fe}, {qe, Fm}, {qe, E*h-UH}, {qe, v*dt-L}, {i, Q}, {i, Fe}, {i, Fm}, {i, E*h-UH}, {i, v*dt-L}, {Q, Fe}, {Q, Fm}, {Q, E*h-UH}, {Q, v*dt-L}, {Fe, Fm}, {Fe, E*h-UH}, {Fe, v*dt-L}, {Fm, E*h-UH}, {Fm, v*dt-L}, {E*h-UH, v*dt-L}, {qe, i, Q}, {qe, i, Fe}, {qe, i, Fm}, {qe, i, E*h-UH}, {qe, i, v*dt-L}, {qe, Q, Fe}, {qe, Q, Fm}, {qe, Q, E*h-UH}, {qe, Q, v*dt-L}, {qe, Fe, Fm}, {qe, Fe, E*h-UH}, {qe, Fe, v*dt-L}, {qe, Fm, E*h-UH}, {qe, Fm, v*dt-L}, {qe, E*h-UH, v*dt-L}, {i, Q, Fe}, {i, Q, Fm}, {i, Q, E*h-UH}, {i, Q, v*dt-L}, {i, Fe, Fm}, {i, Fe, E*h-UH}, {i, Fe, v*dt-L}, {i, Fm, E*h-UH}, {i, Fm, v*dt-L}, {i, E*h-UH, v*dt-L}, {Q, Fe, Fm}, {Q, Fe, E*h-UH}, {Q, Fe, v*dt-L}, {Q, Fm, E*h-UH}, {Q, Fm, v*dt-L}, {Q, E*h-UH, v*dt-L}, {Fe, Fm, E*h-UH}, {Fe, Fm, v*dt-L}, {Fe, E*h-UH, v*dt-L}, {Fm, E*h-UH, v*dt-L}, {L}, {qe}, {Q}, {dt}, {Fe}, {Fm}, {E*h-UH}, {L, qe}, {L, Q}, {L, dt}, {L, Fe}, {L, Fm}, {L, E*h-UH}, {qe, Q}, {qe, dt}, {qe, Fe}, {qe, Fm}, {qe, E*h-UH}, {Q, dt}, {Q, Fe}, {Q, Fm}, {Q, E*h-UH}, {dt, Fe}, {dt, Fm}, {dt, E*h-UH}, {Fe, Fm}, {Fe, E*h-UH}, {Fm, E*h-UH}, {L, qe, Q}, {L, qe, dt}, {L, qe, Fe}, {L, qe, Fm}, {L, qe, E*h-UH}, {L, Q, dt}, {L, Q, Fe}, {L, Q, Fm}, {L, Q, E*h-UH}, {L, dt, Fe}, {L, dt, Fm}, {L, dt, E*h-UH}, {L, Fe, Fm}, {L, Fe, E*h-UH}, {L, Fm, E*h-UH}, {qe, Q, dt}, {qe, Q, Fe}, {qe, Q, Fm}, {qe, Q, E*h-UH}, {qe, dt, Fe}, {qe, dt, Fm}, {qe, dt, E*h-UH}, {qe, Fe, Fm}, {qe, Fe, E*h-UH}, {qe, Fm, E*h-UH}, {Q, dt, Fe}, {Q, dt, Fm}, {Q, dt, E*h-UH}, {Q, Fe, Fm}, {Q, Fe, E*h-UH}, {Q, Fm, E*h-UH}, {dt, Fe, Fm}, {dt, Fe, E*h-UH}, {dt, Fm, E*h-UH}, {Fe, Fm, E*h-UH}};

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
f = openOut "results/hall/abduction/noiseless/2_axiom(s)_removed/combo_8_9/reasoning/reasoning_output.txt";
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

print("Reasoning complete. Output written to results/hall/abduction/noiseless/2_axiom(s)_removed/combo_8_9/reasoning/reasoning_output.txt");
