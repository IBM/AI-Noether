-- AI-Noether: Reasoning Template (Noiseless)
-- Tests if candidate axiom sets, when added to remaining axioms, prove targets

needsPackage("PrimaryDecomposition", Reload => true)

-- Ring definition
R = QQ[Fm, d, v, Fe, E, dt, Q, N, V, i, n, qe, B, h, L, UH, MonomialOrder => Lex];

-- Input data
remainingAxioms = toList([Fm - qe*v*B, Fe - qe*E, Fm - Fe, E*h - UH, i*dt - Q, Q - N*qe, n*V - N, V - L*h*d]);
qList = toList([N*qe*UH - i*B*h*L]);
k = #qList;

-- Per-target variable partitions
measuredPerTarget = {{UH, h, L, i, B, N, qe}};
nonMeasuredPerTarget = {{Fm, d, v, Fe, E, dt, Q, V, n}};

-- Candidate axiom sets to test (list of lists)
candidateSets = {{}, {Fm-Fe}, {E*h-UH}, {Fe*h-qe*UH}, {v*B-E}, {N*qe-Q}, {E*qe-Fe}, {V*n-N}, {dt*i-N*qe}, {E*Q-Fe*N}, {v*Q-i*L}, {E*dt-B*L}, {v*dt-L}, {d*L*UH-E*V}, {d*dt*UH-V*B}, {B*h*L-dt*UH}, {d*h*L-V}, {qe*B*L-Fe*dt}, {i*B*L-Fe*N}, {V*i*B-d*Q*UH}, {Fe*dt*N-Q*B*L}, {v*Fe*N-E*i*L}, {d*n*qe*UH-i*B}, {d*Q*n*UH-N*i*B}, {d*Fe*n*UH-E*i*B}, {d*v*n*qe*h-i}, {Fm-Fe, E*h-UH}, {Fm-Fe, Fe*h-qe*UH}, {Fm-Fe, v*B-E}, {Fm-Fe, N*qe-Q}, {Fm-Fe, E*qe-Fe}, {Fm-Fe, V*n-N}, {Fm-Fe, dt*i-N*qe}, {Fm-Fe, E*Q-Fe*N}, {Fm-Fe, v*Q-i*L}, {Fm-Fe, E*dt-B*L}, {Fm-Fe, v*dt-L}, {Fm-Fe, d*L*UH-E*V}, {Fm-Fe, d*dt*UH-V*B}, {Fm-Fe, B*h*L-dt*UH}, {Fm-Fe, d*h*L-V}, {Fm-Fe, qe*B*L-Fe*dt}, {Fm-Fe, i*B*L-Fe*N}, {Fm-Fe, V*i*B-d*Q*UH}, {Fm-Fe, Fe*dt*N-Q*B*L}, {Fm-Fe, v*Fe*N-E*i*L}, {Fm-Fe, d*n*qe*UH-i*B}, {Fm-Fe, d*Q*n*UH-N*i*B}, {Fm-Fe, d*Fe*n*UH-E*i*B}, {Fm-Fe, d*v*n*qe*h-i}, {E*h-UH, Fe*h-qe*UH}, {E*h-UH, v*B-E}, {E*h-UH, N*qe-Q}, {E*h-UH, E*qe-Fe}, {E*h-UH, V*n-N}, {E*h-UH, dt*i-N*qe}, {E*h-UH, E*Q-Fe*N}, {E*h-UH, v*Q-i*L}, {E*h-UH, E*dt-B*L}, {E*h-UH, v*dt-L}, {E*h-UH, d*L*UH-E*V}, {E*h-UH, d*dt*UH-V*B}, {E*h-UH, B*h*L-dt*UH}, {E*h-UH, d*h*L-V}, {E*h-UH, qe*B*L-Fe*dt}, {E*h-UH, i*B*L-Fe*N}, {E*h-UH, V*i*B-d*Q*UH}, {E*h-UH, Fe*dt*N-Q*B*L}, {E*h-UH, v*Fe*N-E*i*L}, {E*h-UH, d*n*qe*UH-i*B}, {E*h-UH, d*Q*n*UH-N*i*B}, {E*h-UH, d*Fe*n*UH-E*i*B}, {E*h-UH, d*v*n*qe*h-i}, {Fe*h-qe*UH, v*B-E}, {Fe*h-qe*UH, N*qe-Q}, {Fe*h-qe*UH, E*qe-Fe}, {Fe*h-qe*UH, V*n-N}, {Fe*h-qe*UH, dt*i-N*qe}, {Fe*h-qe*UH, E*Q-Fe*N}, {Fe*h-qe*UH, v*Q-i*L}, {Fe*h-qe*UH, E*dt-B*L}, {Fe*h-qe*UH, v*dt-L}, {Fe*h-qe*UH, d*L*UH-E*V}, {Fe*h-qe*UH, d*dt*UH-V*B}, {Fe*h-qe*UH, B*h*L-dt*UH}, {Fe*h-qe*UH, d*h*L-V}, {Fe*h-qe*UH, qe*B*L-Fe*dt}, {Fe*h-qe*UH, i*B*L-Fe*N}, {Fe*h-qe*UH, V*i*B-d*Q*UH}, {Fe*h-qe*UH, Fe*dt*N-Q*B*L}, {Fe*h-qe*UH, v*Fe*N-E*i*L}, {Fe*h-qe*UH, d*n*qe*UH-i*B}, {Fe*h-qe*UH, d*Q*n*UH-N*i*B}, {Fe*h-qe*UH, d*Fe*n*UH-E*i*B}, {Fe*h-qe*UH, d*v*n*qe*h-i}, {v*B-E, N*qe-Q}, {v*B-E, E*qe-Fe}, {v*B-E, V*n-N}, {v*B-E, dt*i-N*qe}, {v*B-E, E*Q-Fe*N}, {v*B-E, v*Q-i*L}, {v*B-E, E*dt-B*L}, {v*B-E, v*dt-L}, {v*B-E, d*L*UH-E*V}, {v*B-E, d*dt*UH-V*B}, {v*B-E, B*h*L-dt*UH}, {v*B-E, d*h*L-V}, {v*B-E, qe*B*L-Fe*dt}, {v*B-E, i*B*L-Fe*N}, {v*B-E, V*i*B-d*Q*UH}, {v*B-E, Fe*dt*N-Q*B*L}, {v*B-E, v*Fe*N-E*i*L}, {v*B-E, d*n*qe*UH-i*B}, {v*B-E, d*Q*n*UH-N*i*B}, {v*B-E, d*Fe*n*UH-E*i*B}, {v*B-E, d*v*n*qe*h-i}, {N*qe-Q, E*qe-Fe}, {N*qe-Q, V*n-N}, {N*qe-Q, dt*i-N*qe}, {N*qe-Q, E*Q-Fe*N}, {N*qe-Q, v*Q-i*L}, {N*qe-Q, E*dt-B*L}, {N*qe-Q, v*dt-L}, {N*qe-Q, d*L*UH-E*V}, {N*qe-Q, d*dt*UH-V*B}, {N*qe-Q, B*h*L-dt*UH}, {N*qe-Q, d*h*L-V}, {N*qe-Q, qe*B*L-Fe*dt}, {N*qe-Q, i*B*L-Fe*N}, {N*qe-Q, V*i*B-d*Q*UH}, {N*qe-Q, Fe*dt*N-Q*B*L}, {N*qe-Q, v*Fe*N-E*i*L}, {N*qe-Q, d*n*qe*UH-i*B}, {N*qe-Q, d*Q*n*UH-N*i*B}, {N*qe-Q, d*Fe*n*UH-E*i*B}, {N*qe-Q, d*v*n*qe*h-i}, {E*qe-Fe, V*n-N}, {E*qe-Fe, dt*i-N*qe}, {E*qe-Fe, E*Q-Fe*N}, {E*qe-Fe, v*Q-i*L}, {E*qe-Fe, E*dt-B*L}, {E*qe-Fe, v*dt-L}, {E*qe-Fe, d*L*UH-E*V}, {E*qe-Fe, d*dt*UH-V*B}, {E*qe-Fe, B*h*L-dt*UH}, {E*qe-Fe, d*h*L-V}, {E*qe-Fe, qe*B*L-Fe*dt}, {E*qe-Fe, i*B*L-Fe*N}, {E*qe-Fe, V*i*B-d*Q*UH}, {E*qe-Fe, Fe*dt*N-Q*B*L}, {E*qe-Fe, v*Fe*N-E*i*L}, {E*qe-Fe, d*n*qe*UH-i*B}, {E*qe-Fe, d*Q*n*UH-N*i*B}, {E*qe-Fe, d*Fe*n*UH-E*i*B}, {E*qe-Fe, d*v*n*qe*h-i}, {V*n-N, dt*i-N*qe}, {V*n-N, E*Q-Fe*N}, {V*n-N, v*Q-i*L}, {V*n-N, E*dt-B*L}, {V*n-N, v*dt-L}, {V*n-N, d*L*UH-E*V}, {V*n-N, d*dt*UH-V*B}, {V*n-N, B*h*L-dt*UH}, {V*n-N, d*h*L-V}, {V*n-N, qe*B*L-Fe*dt}, {V*n-N, i*B*L-Fe*N}, {V*n-N, V*i*B-d*Q*UH}, {V*n-N, Fe*dt*N-Q*B*L}, {V*n-N, v*Fe*N-E*i*L}, {V*n-N, d*n*qe*UH-i*B}, {V*n-N, d*Q*n*UH-N*i*B}, {V*n-N, d*Fe*n*UH-E*i*B}, {V*n-N, d*v*n*qe*h-i}, {dt*i-N*qe, E*Q-Fe*N}, {dt*i-N*qe, v*Q-i*L}, {dt*i-N*qe, E*dt-B*L}, {dt*i-N*qe, v*dt-L}, {dt*i-N*qe, d*L*UH-E*V}, {dt*i-N*qe, d*dt*UH-V*B}, {dt*i-N*qe, B*h*L-dt*UH}, {dt*i-N*qe, d*h*L-V}, {dt*i-N*qe, qe*B*L-Fe*dt}, {dt*i-N*qe, i*B*L-Fe*N}, {dt*i-N*qe, V*i*B-d*Q*UH}, {dt*i-N*qe, Fe*dt*N-Q*B*L}, {dt*i-N*qe, v*Fe*N-E*i*L}, {dt*i-N*qe, d*n*qe*UH-i*B}, {dt*i-N*qe, d*Q*n*UH-N*i*B}, {dt*i-N*qe, d*Fe*n*UH-E*i*B}, {dt*i-N*qe, d*v*n*qe*h-i}, {E*Q-Fe*N, v*Q-i*L}, {E*Q-Fe*N, E*dt-B*L}, {E*Q-Fe*N, v*dt-L}, {E*Q-Fe*N, d*L*UH-E*V}, {E*Q-Fe*N, d*dt*UH-V*B}, {E*Q-Fe*N, B*h*L-dt*UH}, {E*Q-Fe*N, d*h*L-V}, {E*Q-Fe*N, qe*B*L-Fe*dt}, {E*Q-Fe*N, i*B*L-Fe*N}, {E*Q-Fe*N, V*i*B-d*Q*UH}, {E*Q-Fe*N, Fe*dt*N-Q*B*L}, {E*Q-Fe*N, v*Fe*N-E*i*L}, {E*Q-Fe*N, d*n*qe*UH-i*B}, {E*Q-Fe*N, d*Q*n*UH-N*i*B}, {E*Q-Fe*N, d*Fe*n*UH-E*i*B}, {E*Q-Fe*N, d*v*n*qe*h-i}, {v*Q-i*L, E*dt-B*L}, {v*Q-i*L, v*dt-L}, {v*Q-i*L, d*L*UH-E*V}, {v*Q-i*L, d*dt*UH-V*B}, {v*Q-i*L, B*h*L-dt*UH}, {v*Q-i*L, d*h*L-V}, {v*Q-i*L, qe*B*L-Fe*dt}, {v*Q-i*L, i*B*L-Fe*N}, {v*Q-i*L, V*i*B-d*Q*UH}, {v*Q-i*L, Fe*dt*N-Q*B*L}, {v*Q-i*L, v*Fe*N-E*i*L}, {v*Q-i*L, d*n*qe*UH-i*B}, {v*Q-i*L, d*Q*n*UH-N*i*B}, {v*Q-i*L, d*Fe*n*UH-E*i*B}, {v*Q-i*L, d*v*n*qe*h-i}, {E*dt-B*L, v*dt-L}, {E*dt-B*L, d*L*UH-E*V}, {E*dt-B*L, d*dt*UH-V*B}, {E*dt-B*L, B*h*L-dt*UH}, {E*dt-B*L, d*h*L-V}, {E*dt-B*L, qe*B*L-Fe*dt}, {E*dt-B*L, i*B*L-Fe*N}, {E*dt-B*L, V*i*B-d*Q*UH}, {E*dt-B*L, Fe*dt*N-Q*B*L}, {E*dt-B*L, v*Fe*N-E*i*L}, {E*dt-B*L, d*n*qe*UH-i*B}, {E*dt-B*L, d*Q*n*UH-N*i*B}, {E*dt-B*L, d*Fe*n*UH-E*i*B}, {E*dt-B*L, d*v*n*qe*h-i}, {v*dt-L, d*L*UH-E*V}, {v*dt-L, d*dt*UH-V*B}, {v*dt-L, B*h*L-dt*UH}, {v*dt-L, d*h*L-V}, {v*dt-L, qe*B*L-Fe*dt}, {v*dt-L, i*B*L-Fe*N}, {v*dt-L, V*i*B-d*Q*UH}, {v*dt-L, Fe*dt*N-Q*B*L}, {v*dt-L, v*Fe*N-E*i*L}, {v*dt-L, d*n*qe*UH-i*B}, {v*dt-L, d*Q*n*UH-N*i*B}, {v*dt-L, d*Fe*n*UH-E*i*B}, {v*dt-L, d*v*n*qe*h-i}, {d*L*UH-E*V, d*dt*UH-V*B}, {d*L*UH-E*V, B*h*L-dt*UH}, {d*L*UH-E*V, d*h*L-V}, {d*L*UH-E*V, qe*B*L-Fe*dt}, {d*L*UH-E*V, i*B*L-Fe*N}, {d*L*UH-E*V, V*i*B-d*Q*UH}, {d*L*UH-E*V, Fe*dt*N-Q*B*L}, {d*L*UH-E*V, v*Fe*N-E*i*L}, {d*L*UH-E*V, d*n*qe*UH-i*B}, {d*L*UH-E*V, d*Q*n*UH-N*i*B}, {d*L*UH-E*V, d*Fe*n*UH-E*i*B}, {d*L*UH-E*V, d*v*n*qe*h-i}, {d*dt*UH-V*B, B*h*L-dt*UH}, {d*dt*UH-V*B, d*h*L-V}, {d*dt*UH-V*B, qe*B*L-Fe*dt}, {d*dt*UH-V*B, i*B*L-Fe*N}, {d*dt*UH-V*B, V*i*B-d*Q*UH}, {d*dt*UH-V*B, Fe*dt*N-Q*B*L}, {d*dt*UH-V*B, v*Fe*N-E*i*L}, {d*dt*UH-V*B, d*n*qe*UH-i*B}, {d*dt*UH-V*B, d*Q*n*UH-N*i*B}, {d*dt*UH-V*B, d*Fe*n*UH-E*i*B}, {d*dt*UH-V*B, d*v*n*qe*h-i}, {B*h*L-dt*UH, d*h*L-V}, {B*h*L-dt*UH, qe*B*L-Fe*dt}, {B*h*L-dt*UH, i*B*L-Fe*N}, {B*h*L-dt*UH, V*i*B-d*Q*UH}, {B*h*L-dt*UH, Fe*dt*N-Q*B*L}, {B*h*L-dt*UH, v*Fe*N-E*i*L}, {B*h*L-dt*UH, d*n*qe*UH-i*B}, {B*h*L-dt*UH, d*Q*n*UH-N*i*B}, {B*h*L-dt*UH, d*Fe*n*UH-E*i*B}, {B*h*L-dt*UH, d*v*n*qe*h-i}, {d*h*L-V, qe*B*L-Fe*dt}, {d*h*L-V, i*B*L-Fe*N}, {d*h*L-V, V*i*B-d*Q*UH}, {d*h*L-V, Fe*dt*N-Q*B*L}, {d*h*L-V, v*Fe*N-E*i*L}, {d*h*L-V, d*n*qe*UH-i*B}, {d*h*L-V, d*Q*n*UH-N*i*B}, {d*h*L-V, d*Fe*n*UH-E*i*B}, {d*h*L-V, d*v*n*qe*h-i}, {qe*B*L-Fe*dt, i*B*L-Fe*N}, {qe*B*L-Fe*dt, V*i*B-d*Q*UH}, {qe*B*L-Fe*dt, Fe*dt*N-Q*B*L}, {qe*B*L-Fe*dt, v*Fe*N-E*i*L}, {qe*B*L-Fe*dt, d*n*qe*UH-i*B}, {qe*B*L-Fe*dt, d*Q*n*UH-N*i*B}, {qe*B*L-Fe*dt, d*Fe*n*UH-E*i*B}, {qe*B*L-Fe*dt, d*v*n*qe*h-i}, {i*B*L-Fe*N, V*i*B-d*Q*UH}, {i*B*L-Fe*N, Fe*dt*N-Q*B*L}, {i*B*L-Fe*N, v*Fe*N-E*i*L}, {i*B*L-Fe*N, d*n*qe*UH-i*B}, {i*B*L-Fe*N, d*Q*n*UH-N*i*B}, {i*B*L-Fe*N, d*Fe*n*UH-E*i*B}, {i*B*L-Fe*N, d*v*n*qe*h-i}, {V*i*B-d*Q*UH, Fe*dt*N-Q*B*L}, {V*i*B-d*Q*UH, v*Fe*N-E*i*L}, {V*i*B-d*Q*UH, d*n*qe*UH-i*B}, {V*i*B-d*Q*UH, d*Q*n*UH-N*i*B}, {V*i*B-d*Q*UH, d*Fe*n*UH-E*i*B}, {V*i*B-d*Q*UH, d*v*n*qe*h-i}, {Fe*dt*N-Q*B*L, v*Fe*N-E*i*L}, {Fe*dt*N-Q*B*L, d*n*qe*UH-i*B}, {Fe*dt*N-Q*B*L, d*Q*n*UH-N*i*B}, {Fe*dt*N-Q*B*L, d*Fe*n*UH-E*i*B}, {Fe*dt*N-Q*B*L, d*v*n*qe*h-i}, {v*Fe*N-E*i*L, d*n*qe*UH-i*B}, {v*Fe*N-E*i*L, d*Q*n*UH-N*i*B}, {v*Fe*N-E*i*L, d*Fe*n*UH-E*i*B}, {v*Fe*N-E*i*L, d*v*n*qe*h-i}, {d*n*qe*UH-i*B, d*Q*n*UH-N*i*B}, {d*n*qe*UH-i*B, d*Fe*n*UH-E*i*B}, {d*n*qe*UH-i*B, d*v*n*qe*h-i}, {d*Q*n*UH-N*i*B, d*Fe*n*UH-E*i*B}, {d*Q*n*UH-N*i*B, d*v*n*qe*h-i}, {d*Fe*n*UH-E*i*B, d*v*n*qe*h-i}, {UH}, {h}, {qe}, {V}, {N}, {Q}, {dt}, {Fe}, {Fm}, {UH, h}, {UH, qe}, {UH, V}, {UH, N}, {UH, Q}, {UH, dt}, {UH, Fe}, {UH, Fm}, {h, qe}, {h, V}, {h, N}, {h, Q}, {h, dt}, {h, Fe}, {h, Fm}, {qe, V}, {qe, N}, {qe, Q}, {qe, dt}, {qe, Fe}, {qe, Fm}, {V, N}, {V, Q}, {V, dt}, {V, Fe}, {V, Fm}, {N, Q}, {N, dt}, {N, Fe}, {N, Fm}, {Q, dt}, {Q, Fe}, {Q, Fm}, {dt, Fe}, {dt, Fm}, {Fe, Fm}, {UH}, {h}, {V}, {N}, {Q}, {dt}, {Fm-Fe}, {v*B-E}, {E*qe-Fe}, {UH, h}, {UH, V}, {UH, N}, {UH, Q}, {UH, dt}, {UH, Fm-Fe}, {UH, v*B-E}, {UH, E*qe-Fe}, {h, V}, {h, N}, {h, Q}, {h, dt}, {h, Fm-Fe}, {h, v*B-E}, {h, E*qe-Fe}, {V, N}, {V, Q}, {V, dt}, {V, Fm-Fe}, {V, v*B-E}, {V, E*qe-Fe}, {N, Q}, {N, dt}, {N, Fm-Fe}, {N, v*B-E}, {N, E*qe-Fe}, {Q, dt}, {Q, Fm-Fe}, {Q, v*B-E}, {Q, E*qe-Fe}, {dt, Fm-Fe}, {dt, v*B-E}, {dt, E*qe-Fe}, {Fm-Fe, v*B-E}, {Fm-Fe, E*qe-Fe}, {v*B-E, E*qe-Fe}, {UH}, {h}, {i}, {V}, {N}, {Q}, {Fm-Fe}, {v*B-E}, {E*qe-Fe}, {UH, h}, {UH, i}, {UH, V}, {UH, N}, {UH, Q}, {UH, Fm-Fe}, {UH, v*B-E}, {UH, E*qe-Fe}, {h, i}, {h, V}, {h, N}, {h, Q}, {h, Fm-Fe}, {h, v*B-E}, {h, E*qe-Fe}, {i, V}, {i, N}, {i, Q}, {i, Fm-Fe}, {i, v*B-E}, {i, E*qe-Fe}, {V, N}, {V, Q}, {V, Fm-Fe}, {V, v*B-E}, {V, E*qe-Fe}, {N, Q}, {N, Fm-Fe}, {N, v*B-E}, {N, E*qe-Fe}, {Q, Fm-Fe}, {Q, v*B-E}, {Q, E*qe-Fe}, {Fm-Fe, v*B-E}, {Fm-Fe, E*qe-Fe}, {v*B-E, E*qe-Fe}, {B}, {qe}, {Q}, {dt}, {Fe}, {Fm}, {E*h-UH}, {V*n-N}, {d*L*UH-E*V}, {d*h*L-V}, {B, qe}, {B, Q}, {B, dt}, {B, Fe}, {B, Fm}, {B, E*h-UH}, {B, V*n-N}, {B, d*L*UH-E*V}, {B, d*h*L-V}, {qe, Q}, {qe, dt}, {qe, Fe}, {qe, Fm}, {qe, E*h-UH}, {qe, V*n-N}, {qe, d*L*UH-E*V}, {qe, d*h*L-V}, {Q, dt}, {Q, Fe}, {Q, Fm}, {Q, E*h-UH}, {Q, V*n-N}, {Q, d*L*UH-E*V}, {Q, d*h*L-V}, {dt, Fe}, {dt, Fm}, {dt, E*h-UH}, {dt, V*n-N}, {dt, d*L*UH-E*V}, {dt, d*h*L-V}, {Fe, Fm}, {Fe, E*h-UH}, {Fe, V*n-N}, {Fe, d*L*UH-E*V}, {Fe, d*h*L-V}, {Fm, E*h-UH}, {Fm, V*n-N}, {Fm, d*L*UH-E*V}, {Fm, d*h*L-V}, {E*h-UH, V*n-N}, {E*h-UH, d*L*UH-E*V}, {E*h-UH, d*h*L-V}, {V*n-N, d*L*UH-E*V}, {V*n-N, d*h*L-V}, {d*L*UH-E*V, d*h*L-V}, {L}, {qe}, {V}, {N}, {Q}, {dt}, {Fe}, {Fm}, {E*h-UH}, {L, qe}, {L, V}, {L, N}, {L, Q}, {L, dt}, {L, Fe}, {L, Fm}, {L, E*h-UH}, {qe, V}, {qe, N}, {qe, Q}, {qe, dt}, {qe, Fe}, {qe, Fm}, {qe, E*h-UH}, {V, N}, {V, Q}, {V, dt}, {V, Fe}, {V, Fm}, {V, E*h-UH}, {N, Q}, {N, dt}, {N, Fe}, {N, Fm}, {N, E*h-UH}, {Q, dt}, {Q, Fe}, {Q, Fm}, {Q, E*h-UH}, {dt, Fe}, {dt, Fm}, {dt, E*h-UH}, {Fe, Fm}, {Fe, E*h-UH}, {Fm, E*h-UH}, {qe}, {i}, {Q}, {Fe}, {Fm}, {E*h-UH}, {V*n-N}, {d*L*UH-E*V}, {d*h*L-V}, {qe, i}, {qe, Q}, {qe, Fe}, {qe, Fm}, {qe, E*h-UH}, {qe, V*n-N}, {qe, d*L*UH-E*V}, {qe, d*h*L-V}, {i, Q}, {i, Fe}, {i, Fm}, {i, E*h-UH}, {i, V*n-N}, {i, d*L*UH-E*V}, {i, d*h*L-V}, {Q, Fe}, {Q, Fm}, {Q, E*h-UH}, {Q, V*n-N}, {Q, d*L*UH-E*V}, {Q, d*h*L-V}, {Fe, Fm}, {Fe, E*h-UH}, {Fe, V*n-N}, {Fe, d*L*UH-E*V}, {Fe, d*h*L-V}, {Fm, E*h-UH}, {Fm, V*n-N}, {Fm, d*L*UH-E*V}, {Fm, d*h*L-V}, {E*h-UH, V*n-N}, {E*h-UH, d*L*UH-E*V}, {E*h-UH, d*h*L-V}, {V*n-N, d*L*UH-E*V}, {V*n-N, d*h*L-V}, {d*L*UH-E*V, d*h*L-V}, {L}, {V}, {N}, {Q}, {dt}, {Fm-Fe}, {E*h-UH}, {Fe*h-qe*UH}, {v*B-E}, {E*qe-Fe}, {L, V}, {L, N}, {L, Q}, {L, dt}, {L, Fm-Fe}, {L, E*h-UH}, {L, Fe*h-qe*UH}, {L, v*B-E}, {L, E*qe-Fe}, {V, N}, {V, Q}, {V, dt}, {V, Fm-Fe}, {V, E*h-UH}, {V, Fe*h-qe*UH}, {V, v*B-E}, {V, E*qe-Fe}, {N, Q}, {N, dt}, {N, Fm-Fe}, {N, E*h-UH}, {N, Fe*h-qe*UH}, {N, v*B-E}, {N, E*qe-Fe}, {Q, dt}, {Q, Fm-Fe}, {Q, E*h-UH}, {Q, Fe*h-qe*UH}, {Q, v*B-E}, {Q, E*qe-Fe}, {dt, Fm-Fe}, {dt, E*h-UH}, {dt, Fe*h-qe*UH}, {dt, v*B-E}, {dt, E*qe-Fe}, {Fm-Fe, E*h-UH}, {Fm-Fe, Fe*h-qe*UH}, {Fm-Fe, v*B-E}, {Fm-Fe, E*qe-Fe}, {E*h-UH, Fe*h-qe*UH}, {E*h-UH, v*B-E}, {E*h-UH, E*qe-Fe}, {Fe*h-qe*UH, v*B-E}, {Fe*h-qe*UH, E*qe-Fe}, {v*B-E, E*qe-Fe}, {L}, {i}, {V}, {N}, {Q}, {Fm-Fe}, {E*h-UH}, {Fe*h-qe*UH}, {v*B-E}, {E*qe-Fe}, {L, i}, {L, V}, {L, N}, {L, Q}, {L, Fm-Fe}, {L, E*h-UH}, {L, Fe*h-qe*UH}, {L, v*B-E}, {L, E*qe-Fe}, {i, V}, {i, N}, {i, Q}, {i, Fm-Fe}, {i, E*h-UH}, {i, Fe*h-qe*UH}, {i, v*B-E}, {i, E*qe-Fe}, {V, N}, {V, Q}, {V, Fm-Fe}, {V, E*h-UH}, {V, Fe*h-qe*UH}, {V, v*B-E}, {V, E*qe-Fe}, {N, Q}, {N, Fm-Fe}, {N, E*h-UH}, {N, Fe*h-qe*UH}, {N, v*B-E}, {N, E*qe-Fe}, {Q, Fm-Fe}, {Q, E*h-UH}, {Q, Fe*h-qe*UH}, {Q, v*B-E}, {Q, E*qe-Fe}, {Fm-Fe, E*h-UH}, {Fm-Fe, Fe*h-qe*UH}, {Fm-Fe, v*B-E}, {Fm-Fe, E*qe-Fe}, {E*h-UH, Fe*h-qe*UH}, {E*h-UH, v*B-E}, {E*h-UH, E*qe-Fe}, {Fe*h-qe*UH, v*B-E}, {Fe*h-qe*UH, E*qe-Fe}, {v*B-E, E*qe-Fe}, {i}, {V}, {N}, {Q}, {d}, {Fm-Fe}, {E*h-UH}, {Fe*h-qe*UH}, {v*B-E}, {E*qe-Fe}, {i, V}, {i, N}, {i, Q}, {i, d}, {i, Fm-Fe}, {i, E*h-UH}, {i, Fe*h-qe*UH}, {i, v*B-E}, {i, E*qe-Fe}, {V, N}, {V, Q}, {V, d}, {V, Fm-Fe}, {V, E*h-UH}, {V, Fe*h-qe*UH}, {V, v*B-E}, {V, E*qe-Fe}, {N, Q}, {N, d}, {N, Fm-Fe}, {N, E*h-UH}, {N, Fe*h-qe*UH}, {N, v*B-E}, {N, E*qe-Fe}, {Q, d}, {Q, Fm-Fe}, {Q, E*h-UH}, {Q, Fe*h-qe*UH}, {Q, v*B-E}, {Q, E*qe-Fe}, {d, Fm-Fe}, {d, E*h-UH}, {d, Fe*h-qe*UH}, {d, v*B-E}, {d, E*qe-Fe}, {Fm-Fe, E*h-UH}, {Fm-Fe, Fe*h-qe*UH}, {Fm-Fe, v*B-E}, {Fm-Fe, E*qe-Fe}, {E*h-UH, Fe*h-qe*UH}, {E*h-UH, v*B-E}, {E*h-UH, E*qe-Fe}, {Fe*h-qe*UH, v*B-E}, {Fe*h-qe*UH, E*qe-Fe}, {v*B-E, E*qe-Fe}, {n}, {i}, {N}, {Q}, {Fm-Fe}, {E*h-UH}, {Fe*h-qe*UH}, {v*B-E}, {E*qe-Fe}, {d*L*UH-E*V}, {d*h*L-V}, {n, i}, {n, N}, {n, Q}, {n, Fm-Fe}, {n, E*h-UH}, {n, Fe*h-qe*UH}, {n, v*B-E}, {n, E*qe-Fe}, {n, d*L*UH-E*V}, {n, d*h*L-V}, {i, N}, {i, Q}, {i, Fm-Fe}, {i, E*h-UH}, {i, Fe*h-qe*UH}, {i, v*B-E}, {i, E*qe-Fe}, {i, d*L*UH-E*V}, {i, d*h*L-V}, {N, Q}, {N, Fm-Fe}, {N, E*h-UH}, {N, Fe*h-qe*UH}, {N, v*B-E}, {N, E*qe-Fe}, {N, d*L*UH-E*V}, {N, d*h*L-V}, {Q, Fm-Fe}, {Q, E*h-UH}, {Q, Fe*h-qe*UH}, {Q, v*B-E}, {Q, E*qe-Fe}, {Q, d*L*UH-E*V}, {Q, d*h*L-V}, {Fm-Fe, E*h-UH}, {Fm-Fe, Fe*h-qe*UH}, {Fm-Fe, v*B-E}, {Fm-Fe, E*qe-Fe}, {Fm-Fe, d*L*UH-E*V}, {Fm-Fe, d*h*L-V}, {E*h-UH, Fe*h-qe*UH}, {E*h-UH, v*B-E}, {E*h-UH, E*qe-Fe}, {E*h-UH, d*L*UH-E*V}, {E*h-UH, d*h*L-V}, {Fe*h-qe*UH, v*B-E}, {Fe*h-qe*UH, E*qe-Fe}, {Fe*h-qe*UH, d*L*UH-E*V}, {Fe*h-qe*UH, d*h*L-V}, {v*B-E, E*qe-Fe}, {v*B-E, d*L*UH-E*V}, {v*B-E, d*h*L-V}, {E*qe-Fe, d*L*UH-E*V}, {E*qe-Fe, d*h*L-V}, {d*L*UH-E*V, d*h*L-V}, {UH}, {B}, {E}, {Fe}, {Fm}, {N*qe-Q}, {V*n-N}, {dt*i-Q}, {d*h*L-V}, {UH, B}, {UH, E}, {UH, Fe}, {UH, Fm}, {UH, N*qe-Q}, {UH, V*n-N}, {UH, dt*i-Q}, {UH, d*h*L-V}, {B, E}, {B, Fe}, {B, Fm}, {B, N*qe-Q}, {B, V*n-N}, {B, dt*i-Q}, {B, d*h*L-V}, {E, Fe}, {E, Fm}, {E, N*qe-Q}, {E, V*n-N}, {E, dt*i-Q}, {E, d*h*L-V}, {Fe, Fm}, {Fe, N*qe-Q}, {Fe, V*n-N}, {Fe, dt*i-Q}, {Fe, d*h*L-V}, {Fm, N*qe-Q}, {Fm, V*n-N}, {Fm, dt*i-Q}, {Fm, d*h*L-V}, {N*qe-Q, V*n-N}, {N*qe-Q, dt*i-Q}, {N*qe-Q, d*h*L-V}, {V*n-N, dt*i-Q}, {V*n-N, d*h*L-V}, {dt*i-Q, d*h*L-V}};

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
f = openOut "results/hall/abduction/noiseless/1_axiom(s)_removed/combo_5/reasoning/reasoning_output.txt";
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

print("Reasoning complete. Output written to results/hall/abduction/noiseless/1_axiom(s)_removed/combo_5/reasoning/reasoning_output.txt");
