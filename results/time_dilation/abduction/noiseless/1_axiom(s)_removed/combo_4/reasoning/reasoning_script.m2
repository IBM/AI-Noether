-- AI-Noether: Reasoning Template (Noiseless)
-- Tests if candidate axiom sets, when added to remaining axioms, prove targets

needsPackage("PrimaryDecomposition", Reload => true)

-- Ring definition
R = QQ[d, dt, dt0, L, c, F0, F, v, MonomialOrder => Lex];

-- Input data
remainingAxioms = toList([c*dt0 - 2*d, 4*L^2 - 4*d^2 - v^2*dt^2, F0*dt0 - 1, c*dt - 2*L]);
qList = toList([c^2*F0^2-c^2*F^2-F0^2*v^2]);
k = #qList;

-- Per-target variable partitions
measuredPerTarget = {{c, F0, F, v}};
nonMeasuredPerTarget = {{d, dt, dt0, L}};

-- Candidate axiom sets to test (list of lists)
candidateSets = {{}, {2*L*F-c}, {dt*F-1}, {dt0*F0-1}, {2*d*F0-c}, {dt0*c-2*d}, {dt*c-2*L}, {d*dt-dt0*L}, {4*d^2*F+dt*v^2-2*L*c}, {dt*F0*v^2-2*L*c*F0+2*d*c*F}, {dt*L*v^2+2*d^2*c-2*L^2*c}, {dt^2*v^2+4*d^2-4*L^2}, {2*d*c*F^2-c^2*F0+F0*v^2}, {c^2*F0^2-c^2*F^2-F0^2*v^2}, {L*c^2*F0-d*c^2*F-L*F0*v^2}, {d^2*c^2-L^2*c^2+L^2*v^2}, {dt0*L^2*v^2+2*d^3*c-2*d*L^2*c}, {2*L*F-c, dt*F-1}, {2*L*F-c, dt0*F0-1}, {2*L*F-c, 2*d*F0-c}, {2*L*F-c, dt0*c-2*d}, {2*L*F-c, dt*c-2*L}, {2*L*F-c, d*dt-dt0*L}, {2*L*F-c, 4*d^2*F+dt*v^2-2*L*c}, {2*L*F-c, dt*F0*v^2-2*L*c*F0+2*d*c*F}, {2*L*F-c, dt*L*v^2+2*d^2*c-2*L^2*c}, {2*L*F-c, dt^2*v^2+4*d^2-4*L^2}, {2*L*F-c, 2*d*c*F^2-c^2*F0+F0*v^2}, {2*L*F-c, c^2*F0^2-c^2*F^2-F0^2*v^2}, {2*L*F-c, L*c^2*F0-d*c^2*F-L*F0*v^2}, {2*L*F-c, d^2*c^2-L^2*c^2+L^2*v^2}, {2*L*F-c, dt0*L^2*v^2+2*d^3*c-2*d*L^2*c}, {dt*F-1, dt0*F0-1}, {dt*F-1, 2*d*F0-c}, {dt*F-1, dt0*c-2*d}, {dt*F-1, dt*c-2*L}, {dt*F-1, d*dt-dt0*L}, {dt*F-1, 4*d^2*F+dt*v^2-2*L*c}, {dt*F-1, dt*F0*v^2-2*L*c*F0+2*d*c*F}, {dt*F-1, dt*L*v^2+2*d^2*c-2*L^2*c}, {dt*F-1, dt^2*v^2+4*d^2-4*L^2}, {dt*F-1, 2*d*c*F^2-c^2*F0+F0*v^2}, {dt*F-1, c^2*F0^2-c^2*F^2-F0^2*v^2}, {dt*F-1, L*c^2*F0-d*c^2*F-L*F0*v^2}, {dt*F-1, d^2*c^2-L^2*c^2+L^2*v^2}, {dt*F-1, dt0*L^2*v^2+2*d^3*c-2*d*L^2*c}, {dt0*F0-1, 2*d*F0-c}, {dt0*F0-1, dt0*c-2*d}, {dt0*F0-1, dt*c-2*L}, {dt0*F0-1, d*dt-dt0*L}, {dt0*F0-1, 4*d^2*F+dt*v^2-2*L*c}, {dt0*F0-1, dt*F0*v^2-2*L*c*F0+2*d*c*F}, {dt0*F0-1, dt*L*v^2+2*d^2*c-2*L^2*c}, {dt0*F0-1, dt^2*v^2+4*d^2-4*L^2}, {dt0*F0-1, 2*d*c*F^2-c^2*F0+F0*v^2}, {dt0*F0-1, c^2*F0^2-c^2*F^2-F0^2*v^2}, {dt0*F0-1, L*c^2*F0-d*c^2*F-L*F0*v^2}, {dt0*F0-1, d^2*c^2-L^2*c^2+L^2*v^2}, {dt0*F0-1, dt0*L^2*v^2+2*d^3*c-2*d*L^2*c}, {2*d*F0-c, dt0*c-2*d}, {2*d*F0-c, dt*c-2*L}, {2*d*F0-c, d*dt-dt0*L}, {2*d*F0-c, 4*d^2*F+dt*v^2-2*L*c}, {2*d*F0-c, dt*F0*v^2-2*L*c*F0+2*d*c*F}, {2*d*F0-c, dt*L*v^2+2*d^2*c-2*L^2*c}, {2*d*F0-c, dt^2*v^2+4*d^2-4*L^2}, {2*d*F0-c, 2*d*c*F^2-c^2*F0+F0*v^2}, {2*d*F0-c, c^2*F0^2-c^2*F^2-F0^2*v^2}, {2*d*F0-c, L*c^2*F0-d*c^2*F-L*F0*v^2}, {2*d*F0-c, d^2*c^2-L^2*c^2+L^2*v^2}, {2*d*F0-c, dt0*L^2*v^2+2*d^3*c-2*d*L^2*c}, {dt0*c-2*d, dt*c-2*L}, {dt0*c-2*d, d*dt-dt0*L}, {dt0*c-2*d, 4*d^2*F+dt*v^2-2*L*c}, {dt0*c-2*d, dt*F0*v^2-2*L*c*F0+2*d*c*F}, {dt0*c-2*d, dt*L*v^2+2*d^2*c-2*L^2*c}, {dt0*c-2*d, dt^2*v^2+4*d^2-4*L^2}, {dt0*c-2*d, 2*d*c*F^2-c^2*F0+F0*v^2}, {dt0*c-2*d, c^2*F0^2-c^2*F^2-F0^2*v^2}, {dt0*c-2*d, L*c^2*F0-d*c^2*F-L*F0*v^2}, {dt0*c-2*d, d^2*c^2-L^2*c^2+L^2*v^2}, {dt0*c-2*d, dt0*L^2*v^2+2*d^3*c-2*d*L^2*c}, {dt*c-2*L, d*dt-dt0*L}, {dt*c-2*L, 4*d^2*F+dt*v^2-2*L*c}, {dt*c-2*L, dt*F0*v^2-2*L*c*F0+2*d*c*F}, {dt*c-2*L, dt*L*v^2+2*d^2*c-2*L^2*c}, {dt*c-2*L, dt^2*v^2+4*d^2-4*L^2}, {dt*c-2*L, 2*d*c*F^2-c^2*F0+F0*v^2}, {dt*c-2*L, c^2*F0^2-c^2*F^2-F0^2*v^2}, {dt*c-2*L, L*c^2*F0-d*c^2*F-L*F0*v^2}, {dt*c-2*L, d^2*c^2-L^2*c^2+L^2*v^2}, {dt*c-2*L, dt0*L^2*v^2+2*d^3*c-2*d*L^2*c}, {d*dt-dt0*L, 4*d^2*F+dt*v^2-2*L*c}, {d*dt-dt0*L, dt*F0*v^2-2*L*c*F0+2*d*c*F}, {d*dt-dt0*L, dt*L*v^2+2*d^2*c-2*L^2*c}, {d*dt-dt0*L, dt^2*v^2+4*d^2-4*L^2}, {d*dt-dt0*L, 2*d*c*F^2-c^2*F0+F0*v^2}, {d*dt-dt0*L, c^2*F0^2-c^2*F^2-F0^2*v^2}, {d*dt-dt0*L, L*c^2*F0-d*c^2*F-L*F0*v^2}, {d*dt-dt0*L, d^2*c^2-L^2*c^2+L^2*v^2}, {d*dt-dt0*L, dt0*L^2*v^2+2*d^3*c-2*d*L^2*c}, {4*d^2*F+dt*v^2-2*L*c, dt*F0*v^2-2*L*c*F0+2*d*c*F}, {4*d^2*F+dt*v^2-2*L*c, dt*L*v^2+2*d^2*c-2*L^2*c}, {4*d^2*F+dt*v^2-2*L*c, dt^2*v^2+4*d^2-4*L^2}, {4*d^2*F+dt*v^2-2*L*c, 2*d*c*F^2-c^2*F0+F0*v^2}, {4*d^2*F+dt*v^2-2*L*c, c^2*F0^2-c^2*F^2-F0^2*v^2}, {4*d^2*F+dt*v^2-2*L*c, L*c^2*F0-d*c^2*F-L*F0*v^2}, {4*d^2*F+dt*v^2-2*L*c, d^2*c^2-L^2*c^2+L^2*v^2}, {4*d^2*F+dt*v^2-2*L*c, dt0*L^2*v^2+2*d^3*c-2*d*L^2*c}, {dt*F0*v^2-2*L*c*F0+2*d*c*F, dt*L*v^2+2*d^2*c-2*L^2*c}, {dt*F0*v^2-2*L*c*F0+2*d*c*F, dt^2*v^2+4*d^2-4*L^2}, {dt*F0*v^2-2*L*c*F0+2*d*c*F, 2*d*c*F^2-c^2*F0+F0*v^2}, {dt*F0*v^2-2*L*c*F0+2*d*c*F, c^2*F0^2-c^2*F^2-F0^2*v^2}, {dt*F0*v^2-2*L*c*F0+2*d*c*F, L*c^2*F0-d*c^2*F-L*F0*v^2}, {dt*F0*v^2-2*L*c*F0+2*d*c*F, d^2*c^2-L^2*c^2+L^2*v^2}, {dt*F0*v^2-2*L*c*F0+2*d*c*F, dt0*L^2*v^2+2*d^3*c-2*d*L^2*c}, {dt*L*v^2+2*d^2*c-2*L^2*c, dt^2*v^2+4*d^2-4*L^2}, {dt*L*v^2+2*d^2*c-2*L^2*c, 2*d*c*F^2-c^2*F0+F0*v^2}, {dt*L*v^2+2*d^2*c-2*L^2*c, c^2*F0^2-c^2*F^2-F0^2*v^2}, {dt*L*v^2+2*d^2*c-2*L^2*c, L*c^2*F0-d*c^2*F-L*F0*v^2}, {dt*L*v^2+2*d^2*c-2*L^2*c, d^2*c^2-L^2*c^2+L^2*v^2}, {dt*L*v^2+2*d^2*c-2*L^2*c, dt0*L^2*v^2+2*d^3*c-2*d*L^2*c}, {dt^2*v^2+4*d^2-4*L^2, 2*d*c*F^2-c^2*F0+F0*v^2}, {dt^2*v^2+4*d^2-4*L^2, c^2*F0^2-c^2*F^2-F0^2*v^2}, {dt^2*v^2+4*d^2-4*L^2, L*c^2*F0-d*c^2*F-L*F0*v^2}, {dt^2*v^2+4*d^2-4*L^2, d^2*c^2-L^2*c^2+L^2*v^2}, {dt^2*v^2+4*d^2-4*L^2, dt0*L^2*v^2+2*d^3*c-2*d*L^2*c}, {2*d*c*F^2-c^2*F0+F0*v^2, c^2*F0^2-c^2*F^2-F0^2*v^2}, {2*d*c*F^2-c^2*F0+F0*v^2, L*c^2*F0-d*c^2*F-L*F0*v^2}, {2*d*c*F^2-c^2*F0+F0*v^2, d^2*c^2-L^2*c^2+L^2*v^2}, {2*d*c*F^2-c^2*F0+F0*v^2, dt0*L^2*v^2+2*d^3*c-2*d*L^2*c}, {c^2*F0^2-c^2*F^2-F0^2*v^2, L*c^2*F0-d*c^2*F-L*F0*v^2}, {c^2*F0^2-c^2*F^2-F0^2*v^2, d^2*c^2-L^2*c^2+L^2*v^2}, {c^2*F0^2-c^2*F^2-F0^2*v^2, dt0*L^2*v^2+2*d^3*c-2*d*L^2*c}, {L*c^2*F0-d*c^2*F-L*F0*v^2, d^2*c^2-L^2*c^2+L^2*v^2}, {L*c^2*F0-d*c^2*F-L*F0*v^2, dt0*L^2*v^2+2*d^3*c-2*d*L^2*c}, {d^2*c^2-L^2*c^2+L^2*v^2, dt0*L^2*v^2+2*d^3*c-2*d*L^2*c}, {2*L*F+c}, {dt*F+1}, {dt0*F0-1}, {2*d*F0-c}, {dt0*c-2*d}, {dt*c-2*L}, {d*dt-dt0*L}, {4*d^2*F-dt*v^2+2*L*c}, {dt*F0*v^2-2*L*c*F0-2*d*c*F}, {dt*L*v^2+2*d^2*c-2*L^2*c}, {dt^2*v^2+4*d^2-4*L^2}, {2*d*c*F^2-c^2*F0+F0*v^2}, {c^2*F0^2-c^2*F^2-F0^2*v^2}, {L*c^2*F0+d*c^2*F-L*F0*v^2}, {d^2*c^2-L^2*c^2+L^2*v^2}, {dt0*L^2*v^2+2*d^3*c-2*d*L^2*c}, {2*L*F+c, dt*F+1}, {2*L*F+c, dt0*F0-1}, {2*L*F+c, 2*d*F0-c}, {2*L*F+c, dt0*c-2*d}, {2*L*F+c, dt*c-2*L}, {2*L*F+c, d*dt-dt0*L}, {2*L*F+c, 4*d^2*F-dt*v^2+2*L*c}, {2*L*F+c, dt*F0*v^2-2*L*c*F0-2*d*c*F}, {2*L*F+c, dt*L*v^2+2*d^2*c-2*L^2*c}, {2*L*F+c, dt^2*v^2+4*d^2-4*L^2}, {2*L*F+c, 2*d*c*F^2-c^2*F0+F0*v^2}, {2*L*F+c, c^2*F0^2-c^2*F^2-F0^2*v^2}, {2*L*F+c, L*c^2*F0+d*c^2*F-L*F0*v^2}, {2*L*F+c, d^2*c^2-L^2*c^2+L^2*v^2}, {2*L*F+c, dt0*L^2*v^2+2*d^3*c-2*d*L^2*c}, {dt*F+1, dt0*F0-1}, {dt*F+1, 2*d*F0-c}, {dt*F+1, dt0*c-2*d}, {dt*F+1, dt*c-2*L}, {dt*F+1, d*dt-dt0*L}, {dt*F+1, 4*d^2*F-dt*v^2+2*L*c}, {dt*F+1, dt*F0*v^2-2*L*c*F0-2*d*c*F}, {dt*F+1, dt*L*v^2+2*d^2*c-2*L^2*c}, {dt*F+1, dt^2*v^2+4*d^2-4*L^2}, {dt*F+1, 2*d*c*F^2-c^2*F0+F0*v^2}, {dt*F+1, c^2*F0^2-c^2*F^2-F0^2*v^2}, {dt*F+1, L*c^2*F0+d*c^2*F-L*F0*v^2}, {dt*F+1, d^2*c^2-L^2*c^2+L^2*v^2}, {dt*F+1, dt0*L^2*v^2+2*d^3*c-2*d*L^2*c}, {dt0*F0-1, 2*d*F0-c}, {dt0*F0-1, dt0*c-2*d}, {dt0*F0-1, dt*c-2*L}, {dt0*F0-1, d*dt-dt0*L}, {dt0*F0-1, 4*d^2*F-dt*v^2+2*L*c}, {dt0*F0-1, dt*F0*v^2-2*L*c*F0-2*d*c*F}, {dt0*F0-1, dt*L*v^2+2*d^2*c-2*L^2*c}, {dt0*F0-1, dt^2*v^2+4*d^2-4*L^2}, {dt0*F0-1, 2*d*c*F^2-c^2*F0+F0*v^2}, {dt0*F0-1, c^2*F0^2-c^2*F^2-F0^2*v^2}, {dt0*F0-1, L*c^2*F0+d*c^2*F-L*F0*v^2}, {dt0*F0-1, d^2*c^2-L^2*c^2+L^2*v^2}, {dt0*F0-1, dt0*L^2*v^2+2*d^3*c-2*d*L^2*c}, {2*d*F0-c, dt0*c-2*d}, {2*d*F0-c, dt*c-2*L}, {2*d*F0-c, d*dt-dt0*L}, {2*d*F0-c, 4*d^2*F-dt*v^2+2*L*c}, {2*d*F0-c, dt*F0*v^2-2*L*c*F0-2*d*c*F}, {2*d*F0-c, dt*L*v^2+2*d^2*c-2*L^2*c}, {2*d*F0-c, dt^2*v^2+4*d^2-4*L^2}, {2*d*F0-c, 2*d*c*F^2-c^2*F0+F0*v^2}, {2*d*F0-c, c^2*F0^2-c^2*F^2-F0^2*v^2}, {2*d*F0-c, L*c^2*F0+d*c^2*F-L*F0*v^2}, {2*d*F0-c, d^2*c^2-L^2*c^2+L^2*v^2}, {2*d*F0-c, dt0*L^2*v^2+2*d^3*c-2*d*L^2*c}, {dt0*c-2*d, dt*c-2*L}, {dt0*c-2*d, d*dt-dt0*L}, {dt0*c-2*d, 4*d^2*F-dt*v^2+2*L*c}, {dt0*c-2*d, dt*F0*v^2-2*L*c*F0-2*d*c*F}, {dt0*c-2*d, dt*L*v^2+2*d^2*c-2*L^2*c}, {dt0*c-2*d, dt^2*v^2+4*d^2-4*L^2}, {dt0*c-2*d, 2*d*c*F^2-c^2*F0+F0*v^2}, {dt0*c-2*d, c^2*F0^2-c^2*F^2-F0^2*v^2}, {dt0*c-2*d, L*c^2*F0+d*c^2*F-L*F0*v^2}, {dt0*c-2*d, d^2*c^2-L^2*c^2+L^2*v^2}, {dt0*c-2*d, dt0*L^2*v^2+2*d^3*c-2*d*L^2*c}, {dt*c-2*L, d*dt-dt0*L}, {dt*c-2*L, 4*d^2*F-dt*v^2+2*L*c}, {dt*c-2*L, dt*F0*v^2-2*L*c*F0-2*d*c*F}, {dt*c-2*L, dt*L*v^2+2*d^2*c-2*L^2*c}, {dt*c-2*L, dt^2*v^2+4*d^2-4*L^2}, {dt*c-2*L, 2*d*c*F^2-c^2*F0+F0*v^2}, {dt*c-2*L, c^2*F0^2-c^2*F^2-F0^2*v^2}, {dt*c-2*L, L*c^2*F0+d*c^2*F-L*F0*v^2}, {dt*c-2*L, d^2*c^2-L^2*c^2+L^2*v^2}, {dt*c-2*L, dt0*L^2*v^2+2*d^3*c-2*d*L^2*c}, {d*dt-dt0*L, 4*d^2*F-dt*v^2+2*L*c}, {d*dt-dt0*L, dt*F0*v^2-2*L*c*F0-2*d*c*F}, {d*dt-dt0*L, dt*L*v^2+2*d^2*c-2*L^2*c}, {d*dt-dt0*L, dt^2*v^2+4*d^2-4*L^2}, {d*dt-dt0*L, 2*d*c*F^2-c^2*F0+F0*v^2}, {d*dt-dt0*L, c^2*F0^2-c^2*F^2-F0^2*v^2}, {d*dt-dt0*L, L*c^2*F0+d*c^2*F-L*F0*v^2}, {d*dt-dt0*L, d^2*c^2-L^2*c^2+L^2*v^2}, {d*dt-dt0*L, dt0*L^2*v^2+2*d^3*c-2*d*L^2*c}, {4*d^2*F-dt*v^2+2*L*c, dt*F0*v^2-2*L*c*F0-2*d*c*F}, {4*d^2*F-dt*v^2+2*L*c, dt*L*v^2+2*d^2*c-2*L^2*c}, {4*d^2*F-dt*v^2+2*L*c, dt^2*v^2+4*d^2-4*L^2}, {4*d^2*F-dt*v^2+2*L*c, 2*d*c*F^2-c^2*F0+F0*v^2}, {4*d^2*F-dt*v^2+2*L*c, c^2*F0^2-c^2*F^2-F0^2*v^2}, {4*d^2*F-dt*v^2+2*L*c, L*c^2*F0+d*c^2*F-L*F0*v^2}, {4*d^2*F-dt*v^2+2*L*c, d^2*c^2-L^2*c^2+L^2*v^2}, {4*d^2*F-dt*v^2+2*L*c, dt0*L^2*v^2+2*d^3*c-2*d*L^2*c}, {dt*F0*v^2-2*L*c*F0-2*d*c*F, dt*L*v^2+2*d^2*c-2*L^2*c}, {dt*F0*v^2-2*L*c*F0-2*d*c*F, dt^2*v^2+4*d^2-4*L^2}, {dt*F0*v^2-2*L*c*F0-2*d*c*F, 2*d*c*F^2-c^2*F0+F0*v^2}, {dt*F0*v^2-2*L*c*F0-2*d*c*F, c^2*F0^2-c^2*F^2-F0^2*v^2}, {dt*F0*v^2-2*L*c*F0-2*d*c*F, L*c^2*F0+d*c^2*F-L*F0*v^2}, {dt*F0*v^2-2*L*c*F0-2*d*c*F, d^2*c^2-L^2*c^2+L^2*v^2}, {dt*F0*v^2-2*L*c*F0-2*d*c*F, dt0*L^2*v^2+2*d^3*c-2*d*L^2*c}, {dt*L*v^2+2*d^2*c-2*L^2*c, dt^2*v^2+4*d^2-4*L^2}, {dt*L*v^2+2*d^2*c-2*L^2*c, 2*d*c*F^2-c^2*F0+F0*v^2}, {dt*L*v^2+2*d^2*c-2*L^2*c, c^2*F0^2-c^2*F^2-F0^2*v^2}, {dt*L*v^2+2*d^2*c-2*L^2*c, L*c^2*F0+d*c^2*F-L*F0*v^2}, {dt*L*v^2+2*d^2*c-2*L^2*c, d^2*c^2-L^2*c^2+L^2*v^2}, {dt*L*v^2+2*d^2*c-2*L^2*c, dt0*L^2*v^2+2*d^3*c-2*d*L^2*c}, {dt^2*v^2+4*d^2-4*L^2, 2*d*c*F^2-c^2*F0+F0*v^2}, {dt^2*v^2+4*d^2-4*L^2, c^2*F0^2-c^2*F^2-F0^2*v^2}, {dt^2*v^2+4*d^2-4*L^2, L*c^2*F0+d*c^2*F-L*F0*v^2}, {dt^2*v^2+4*d^2-4*L^2, d^2*c^2-L^2*c^2+L^2*v^2}, {dt^2*v^2+4*d^2-4*L^2, dt0*L^2*v^2+2*d^3*c-2*d*L^2*c}, {2*d*c*F^2-c^2*F0+F0*v^2, c^2*F0^2-c^2*F^2-F0^2*v^2}, {2*d*c*F^2-c^2*F0+F0*v^2, L*c^2*F0+d*c^2*F-L*F0*v^2}, {2*d*c*F^2-c^2*F0+F0*v^2, d^2*c^2-L^2*c^2+L^2*v^2}, {2*d*c*F^2-c^2*F0+F0*v^2, dt0*L^2*v^2+2*d^3*c-2*d*L^2*c}, {c^2*F0^2-c^2*F^2-F0^2*v^2, L*c^2*F0+d*c^2*F-L*F0*v^2}, {c^2*F0^2-c^2*F^2-F0^2*v^2, d^2*c^2-L^2*c^2+L^2*v^2}, {c^2*F0^2-c^2*F^2-F0^2*v^2, dt0*L^2*v^2+2*d^3*c-2*d*L^2*c}, {L*c^2*F0+d*c^2*F-L*F0*v^2, d^2*c^2-L^2*c^2+L^2*v^2}, {L*c^2*F0+d*c^2*F-L*F0*v^2, dt0*L^2*v^2+2*d^3*c-2*d*L^2*c}, {d^2*c^2-L^2*c^2+L^2*v^2, dt0*L^2*v^2+2*d^3*c-2*d*L^2*c}, {v}, {c}, {L}, {d}, {dt0*F0-1}, {v, c}, {v, L}, {v, d}, {v, dt0*F0-1}, {c, L}, {c, d}, {c, dt0*F0-1}, {L, d}, {L, dt0*F0-1}, {d, dt0*F0-1}};

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
f = openOut "results/time_dilation/abduction/noiseless/1_axiom(s)_removed/combo_4/reasoning/reasoning_output.txt";
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

print("Reasoning complete. Output written to results/time_dilation/abduction/noiseless/1_axiom(s)_removed/combo_4/reasoning/reasoning_output.txt");
