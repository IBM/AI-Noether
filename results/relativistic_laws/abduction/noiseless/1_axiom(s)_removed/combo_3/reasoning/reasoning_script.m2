-- AI-Noether: Reasoning Template (Noiseless)
-- Tests if candidate axiom sets, when added to remaining axioms, prove targets

needsPackage("PrimaryDecomposition", Reload => true)

-- Ring definition
R = QQ[c, dt, v, F0, F, dt0, L0, L, m0, u0, m, u, MonomialOrder => Lex];

-- Input data
remainingAxioms = toList([F0*dt0 - 1, F*dt - 1, c^2*dt^2 - 4*L0^2 - v^2*dt^2, m0*u0 - m*u, u0*dt0 - u*dt, dt*(c^2 - v^2) - 2*L*c]);
qList = toList([c^2*F0^2-c^2*F^2-F0^2*v^2, c^2*m0^2*u0-c^2*u0*m^2+v^2*u0*m^2, c^2*L0^2-c^2*L^2-v^2*L0^2]);
k = #qList;

-- Per-target variable partitions
measuredPerTarget = {{v, c, F0, F}, {v, c, m, m0, u0}, {L, L0, v, c}};
nonMeasuredPerTarget = {{dt, dt0, L0, L, m0, u0, m, u}, {dt, F0, F, dt0, L0, L, u}, {dt, F0, F, dt0, m0, u0, m, u}};

-- Candidate axiom sets to test (list of lists)
candidateSets = {{}, {F*dt0*L0+L}, {F*L0+F0*L}, {-4*F0^2*L0^2+4*F0^2*L^2+v^2}, {dt0*L0+dt*L}, {u}, {u0}, {2*F0*L0+c}, {F*dt0*L0+L, F*L0+F0*L}, {F*dt0*L0+L, -4*F0^2*L0^2+4*F0^2*L^2+v^2}, {F*dt0*L0+L, dt0*L0+dt*L}, {F*dt0*L0+L, u}, {F*dt0*L0+L, u0}, {F*dt0*L0+L, 2*F0*L0+c}, {F*L0+F0*L, -4*F0^2*L0^2+4*F0^2*L^2+v^2}, {F*L0+F0*L, dt0*L0+dt*L}, {F*L0+F0*L, u}, {F*L0+F0*L, u0}, {F*L0+F0*L, 2*F0*L0+c}, {-4*F0^2*L0^2+4*F0^2*L^2+v^2, dt0*L0+dt*L}, {-4*F0^2*L0^2+4*F0^2*L^2+v^2, u}, {-4*F0^2*L0^2+4*F0^2*L^2+v^2, u0}, {-4*F0^2*L0^2+4*F0^2*L^2+v^2, 2*F0*L0+c}, {dt0*L0+dt*L, u}, {dt0*L0+dt*L, u0}, {dt0*L0+dt*L, 2*F0*L0+c}, {u, u0}, {u, 2*F0*L0+c}, {u0, 2*F0*L0+c}, {F*dt0*L0+L, F*L0+F0*L, -4*F0^2*L0^2+4*F0^2*L^2+v^2}, {F*dt0*L0+L, F*L0+F0*L, dt0*L0+dt*L}, {F*dt0*L0+L, F*L0+F0*L, u}, {F*dt0*L0+L, F*L0+F0*L, u0}, {F*dt0*L0+L, F*L0+F0*L, 2*F0*L0+c}, {F*dt0*L0+L, -4*F0^2*L0^2+4*F0^2*L^2+v^2, dt0*L0+dt*L}, {F*dt0*L0+L, -4*F0^2*L0^2+4*F0^2*L^2+v^2, u}, {F*dt0*L0+L, -4*F0^2*L0^2+4*F0^2*L^2+v^2, u0}, {F*dt0*L0+L, -4*F0^2*L0^2+4*F0^2*L^2+v^2, 2*F0*L0+c}, {F*dt0*L0+L, dt0*L0+dt*L, u}, {F*dt0*L0+L, dt0*L0+dt*L, u0}, {F*dt0*L0+L, dt0*L0+dt*L, 2*F0*L0+c}, {F*dt0*L0+L, u, u0}, {F*dt0*L0+L, u, 2*F0*L0+c}, {F*dt0*L0+L, u0, 2*F0*L0+c}, {F*L0+F0*L, -4*F0^2*L0^2+4*F0^2*L^2+v^2, dt0*L0+dt*L}, {F*L0+F0*L, -4*F0^2*L0^2+4*F0^2*L^2+v^2, u}, {F*L0+F0*L, -4*F0^2*L0^2+4*F0^2*L^2+v^2, u0}, {F*L0+F0*L, -4*F0^2*L0^2+4*F0^2*L^2+v^2, 2*F0*L0+c}, {F*L0+F0*L, dt0*L0+dt*L, u}, {F*L0+F0*L, dt0*L0+dt*L, u0}, {F*L0+F0*L, dt0*L0+dt*L, 2*F0*L0+c}, {F*L0+F0*L, u, u0}, {F*L0+F0*L, u, 2*F0*L0+c}, {F*L0+F0*L, u0, 2*F0*L0+c}, {-4*F0^2*L0^2+4*F0^2*L^2+v^2, dt0*L0+dt*L, u}, {-4*F0^2*L0^2+4*F0^2*L^2+v^2, dt0*L0+dt*L, u0}, {-4*F0^2*L0^2+4*F0^2*L^2+v^2, dt0*L0+dt*L, 2*F0*L0+c}, {-4*F0^2*L0^2+4*F0^2*L^2+v^2, u, u0}, {-4*F0^2*L0^2+4*F0^2*L^2+v^2, u, 2*F0*L0+c}, {-4*F0^2*L0^2+4*F0^2*L^2+v^2, u0, 2*F0*L0+c}, {dt0*L0+dt*L, u, u0}, {dt0*L0+dt*L, u, 2*F0*L0+c}, {dt0*L0+dt*L, u0, 2*F0*L0+c}, {u, u0, 2*F0*L0+c}, {F*dt0*L0-L}, {-F*L0+F0*L}, {-dt0*L0+dt*L}, {-2*F0*L0+c}, {F*dt0*L0-L, -F*L0+F0*L}, {F*dt0*L0-L, -4*F0^2*L0^2+4*F0^2*L^2+v^2}, {F*dt0*L0-L, -dt0*L0+dt*L}, {F*dt0*L0-L, u}, {F*dt0*L0-L, u0}, {F*dt0*L0-L, -2*F0*L0+c}, {-F*L0+F0*L, -4*F0^2*L0^2+4*F0^2*L^2+v^2}, {-F*L0+F0*L, -dt0*L0+dt*L}, {-F*L0+F0*L, u}, {-F*L0+F0*L, u0}, {-F*L0+F0*L, -2*F0*L0+c}, {-4*F0^2*L0^2+4*F0^2*L^2+v^2, -dt0*L0+dt*L}, {-4*F0^2*L0^2+4*F0^2*L^2+v^2, -2*F0*L0+c}, {-dt0*L0+dt*L, u}, {-dt0*L0+dt*L, u0}, {-dt0*L0+dt*L, -2*F0*L0+c}, {u, -2*F0*L0+c}, {u0, -2*F0*L0+c}, {F*dt0*L0-L, -F*L0+F0*L, -4*F0^2*L0^2+4*F0^2*L^2+v^2}, {F*dt0*L0-L, -F*L0+F0*L, -dt0*L0+dt*L}, {F*dt0*L0-L, -F*L0+F0*L, u}, {F*dt0*L0-L, -F*L0+F0*L, u0}, {F*dt0*L0-L, -F*L0+F0*L, -2*F0*L0+c}, {F*dt0*L0-L, -4*F0^2*L0^2+4*F0^2*L^2+v^2, -dt0*L0+dt*L}, {F*dt0*L0-L, -4*F0^2*L0^2+4*F0^2*L^2+v^2, u}, {F*dt0*L0-L, -4*F0^2*L0^2+4*F0^2*L^2+v^2, u0}, {F*dt0*L0-L, -4*F0^2*L0^2+4*F0^2*L^2+v^2, -2*F0*L0+c}, {F*dt0*L0-L, -dt0*L0+dt*L, u}, {F*dt0*L0-L, -dt0*L0+dt*L, u0}, {F*dt0*L0-L, -dt0*L0+dt*L, -2*F0*L0+c}, {F*dt0*L0-L, u, u0}, {F*dt0*L0-L, u, -2*F0*L0+c}, {F*dt0*L0-L, u0, -2*F0*L0+c}, {-F*L0+F0*L, -4*F0^2*L0^2+4*F0^2*L^2+v^2, -dt0*L0+dt*L}, {-F*L0+F0*L, -4*F0^2*L0^2+4*F0^2*L^2+v^2, u}, {-F*L0+F0*L, -4*F0^2*L0^2+4*F0^2*L^2+v^2, u0}, {-F*L0+F0*L, -4*F0^2*L0^2+4*F0^2*L^2+v^2, -2*F0*L0+c}, {-F*L0+F0*L, -dt0*L0+dt*L, u}, {-F*L0+F0*L, -dt0*L0+dt*L, u0}, {-F*L0+F0*L, -dt0*L0+dt*L, -2*F0*L0+c}, {-F*L0+F0*L, u, u0}, {-F*L0+F0*L, u, -2*F0*L0+c}, {-F*L0+F0*L, u0, -2*F0*L0+c}, {-4*F0^2*L0^2+4*F0^2*L^2+v^2, -dt0*L0+dt*L, u}, {-4*F0^2*L0^2+4*F0^2*L^2+v^2, -dt0*L0+dt*L, u0}, {-4*F0^2*L0^2+4*F0^2*L^2+v^2, -dt0*L0+dt*L, -2*F0*L0+c}, {-4*F0^2*L0^2+4*F0^2*L^2+v^2, u, -2*F0*L0+c}, {-4*F0^2*L0^2+4*F0^2*L^2+v^2, u0, -2*F0*L0+c}, {-dt0*L0+dt*L, u, u0}, {-dt0*L0+dt*L, u, -2*F0*L0+c}, {-dt0*L0+dt*L, u0, -2*F0*L0+c}, {u, u0, -2*F0*L0+c}, {L0}, {v}, {c}, {u, L0}, {u, v}, {u, c}, {u0, L0}, {u0, v}, {u0, c}, {L0, v}, {L0, c}, {v, c}, {u, u0, L0}, {u, u0, v}, {u, u0, c}, {u, L0, v}, {u, L0, c}, {u, v, c}, {u0, L0, v}, {u0, L0, c}, {u0, v, c}, {L0, v, c}, {L*u0+L0*u}, {L0*m0+L*m}, {F*dt0*m-m0}, {F0*m0-F*m}, {dt*m0-dt0*m}, {L*u0+L0*u, L0*m0+L*m}, {L*u0+L0*u, F*dt0*m-m0}, {L*u0+L0*u, F*dt0*L0+L}, {L*u0+L0*u, F0*m0-F*m}, {L*u0+L0*u, F*L0+F0*L}, {L*u0+L0*u, -4*F0^2*L0^2+4*F0^2*L^2+v^2}, {L*u0+L0*u, dt*m0-dt0*m}, {L*u0+L0*u, dt0*L0+dt*L}, {L*u0+L0*u, 2*F0*L0+c}, {L0*m0+L*m, F*dt0*m-m0}, {L0*m0+L*m, F*dt0*L0+L}, {L0*m0+L*m, F0*m0-F*m}, {L0*m0+L*m, F*L0+F0*L}, {L0*m0+L*m, -4*F0^2*L0^2+4*F0^2*L^2+v^2}, {L0*m0+L*m, dt*m0-dt0*m}, {L0*m0+L*m, dt0*L0+dt*L}, {L0*m0+L*m, 2*F0*L0+c}, {F*dt0*m-m0, F*dt0*L0+L}, {F*dt0*m-m0, F0*m0-F*m}, {F*dt0*m-m0, F*L0+F0*L}, {F*dt0*m-m0, -4*F0^2*L0^2+4*F0^2*L^2+v^2}, {F*dt0*m-m0, dt*m0-dt0*m}, {F*dt0*m-m0, dt0*L0+dt*L}, {F*dt0*m-m0, 2*F0*L0+c}, {F*dt0*L0+L, F0*m0-F*m}, {F*dt0*L0+L, dt*m0-dt0*m}, {F0*m0-F*m, F*L0+F0*L}, {F0*m0-F*m, -4*F0^2*L0^2+4*F0^2*L^2+v^2}, {F0*m0-F*m, dt*m0-dt0*m}, {F0*m0-F*m, dt0*L0+dt*L}, {F0*m0-F*m, 2*F0*L0+c}, {F*L0+F0*L, dt*m0-dt0*m}, {-4*F0^2*L0^2+4*F0^2*L^2+v^2, dt*m0-dt0*m}, {dt*m0-dt0*m, dt0*L0+dt*L}, {dt*m0-dt0*m, 2*F0*L0+c}, {L*u0+L0*u, L0*m0+L*m, F*dt0*m-m0}, {L*u0+L0*u, L0*m0+L*m, F*dt0*L0+L}, {L*u0+L0*u, L0*m0+L*m, F0*m0-F*m}, {L*u0+L0*u, L0*m0+L*m, F*L0+F0*L}, {L*u0+L0*u, L0*m0+L*m, -4*F0^2*L0^2+4*F0^2*L^2+v^2}, {L*u0+L0*u, L0*m0+L*m, dt*m0-dt0*m}, {L*u0+L0*u, L0*m0+L*m, dt0*L0+dt*L}, {L*u0+L0*u, L0*m0+L*m, 2*F0*L0+c}, {L*u0+L0*u, F*dt0*m-m0, F*dt0*L0+L}, {L*u0+L0*u, F*dt0*m-m0, F0*m0-F*m}, {L*u0+L0*u, F*dt0*m-m0, F*L0+F0*L}, {L*u0+L0*u, F*dt0*m-m0, -4*F0^2*L0^2+4*F0^2*L^2+v^2}, {L*u0+L0*u, F*dt0*m-m0, dt*m0-dt0*m}, {L*u0+L0*u, F*dt0*m-m0, dt0*L0+dt*L}, {L*u0+L0*u, F*dt0*m-m0, 2*F0*L0+c}, {L*u0+L0*u, F*dt0*L0+L, F0*m0-F*m}, {L*u0+L0*u, F*dt0*L0+L, F*L0+F0*L}, {L*u0+L0*u, F*dt0*L0+L, -4*F0^2*L0^2+4*F0^2*L^2+v^2}, {L*u0+L0*u, F*dt0*L0+L, dt*m0-dt0*m}, {L*u0+L0*u, F*dt0*L0+L, dt0*L0+dt*L}, {L*u0+L0*u, F*dt0*L0+L, 2*F0*L0+c}, {L*u0+L0*u, F0*m0-F*m, F*L0+F0*L}, {L*u0+L0*u, F0*m0-F*m, -4*F0^2*L0^2+4*F0^2*L^2+v^2}, {L*u0+L0*u, F0*m0-F*m, dt*m0-dt0*m}, {L*u0+L0*u, F0*m0-F*m, dt0*L0+dt*L}, {L*u0+L0*u, F0*m0-F*m, 2*F0*L0+c}, {L*u0+L0*u, F*L0+F0*L, -4*F0^2*L0^2+4*F0^2*L^2+v^2}, {L*u0+L0*u, F*L0+F0*L, dt*m0-dt0*m}, {L*u0+L0*u, F*L0+F0*L, dt0*L0+dt*L}, {L*u0+L0*u, F*L0+F0*L, 2*F0*L0+c}, {L*u0+L0*u, -4*F0^2*L0^2+4*F0^2*L^2+v^2, dt*m0-dt0*m}, {L*u0+L0*u, -4*F0^2*L0^2+4*F0^2*L^2+v^2, dt0*L0+dt*L}, {L*u0+L0*u, -4*F0^2*L0^2+4*F0^2*L^2+v^2, 2*F0*L0+c}, {L*u0+L0*u, dt*m0-dt0*m, dt0*L0+dt*L}, {L*u0+L0*u, dt*m0-dt0*m, 2*F0*L0+c}, {L*u0+L0*u, dt0*L0+dt*L, 2*F0*L0+c}, {L0*m0+L*m, F*dt0*m-m0, F*dt0*L0+L}, {L0*m0+L*m, F*dt0*m-m0, F0*m0-F*m}, {L0*m0+L*m, F*dt0*m-m0, F*L0+F0*L}, {L0*m0+L*m, F*dt0*m-m0, -4*F0^2*L0^2+4*F0^2*L^2+v^2}, {L0*m0+L*m, F*dt0*m-m0, dt*m0-dt0*m}, {L0*m0+L*m, F*dt0*m-m0, dt0*L0+dt*L}, {L0*m0+L*m, F*dt0*m-m0, 2*F0*L0+c}, {L0*m0+L*m, F*dt0*L0+L, F0*m0-F*m}, {L0*m0+L*m, F*dt0*L0+L, F*L0+F0*L}, {L0*m0+L*m, F*dt0*L0+L, -4*F0^2*L0^2+4*F0^2*L^2+v^2}, {L0*m0+L*m, F*dt0*L0+L, dt*m0-dt0*m}, {L0*m0+L*m, F*dt0*L0+L, dt0*L0+dt*L}, {L0*m0+L*m, F*dt0*L0+L, 2*F0*L0+c}, {L0*m0+L*m, F0*m0-F*m, F*L0+F0*L}, {L0*m0+L*m, F0*m0-F*m, -4*F0^2*L0^2+4*F0^2*L^2+v^2}, {L0*m0+L*m, F0*m0-F*m, dt*m0-dt0*m}, {L0*m0+L*m, F0*m0-F*m, dt0*L0+dt*L}, {L0*m0+L*m, F0*m0-F*m, 2*F0*L0+c}, {L0*m0+L*m, F*L0+F0*L, -4*F0^2*L0^2+4*F0^2*L^2+v^2}, {L0*m0+L*m, F*L0+F0*L, dt*m0-dt0*m}, {L0*m0+L*m, F*L0+F0*L, dt0*L0+dt*L}, {L0*m0+L*m, F*L0+F0*L, 2*F0*L0+c}, {L0*m0+L*m, -4*F0^2*L0^2+4*F0^2*L^2+v^2, dt*m0-dt0*m}, {L0*m0+L*m, -4*F0^2*L0^2+4*F0^2*L^2+v^2, dt0*L0+dt*L}, {L0*m0+L*m, -4*F0^2*L0^2+4*F0^2*L^2+v^2, 2*F0*L0+c}, {L0*m0+L*m, dt*m0-dt0*m, dt0*L0+dt*L}, {L0*m0+L*m, dt*m0-dt0*m, 2*F0*L0+c}, {L0*m0+L*m, dt0*L0+dt*L, 2*F0*L0+c}, {F*dt0*m-m0, F*dt0*L0+L, F0*m0-F*m}, {F*dt0*m-m0, F*dt0*L0+L, F*L0+F0*L}, {F*dt0*m-m0, F*dt0*L0+L, -4*F0^2*L0^2+4*F0^2*L^2+v^2}, {F*dt0*m-m0, F*dt0*L0+L, dt*m0-dt0*m}, {F*dt0*m-m0, F*dt0*L0+L, dt0*L0+dt*L}, {F*dt0*m-m0, F*dt0*L0+L, 2*F0*L0+c}, {F*dt0*m-m0, F0*m0-F*m, F*L0+F0*L}, {F*dt0*m-m0, F0*m0-F*m, -4*F0^2*L0^2+4*F0^2*L^2+v^2}, {F*dt0*m-m0, F0*m0-F*m, dt*m0-dt0*m}, {F*dt0*m-m0, F0*m0-F*m, dt0*L0+dt*L}, {F*dt0*m-m0, F0*m0-F*m, 2*F0*L0+c}, {F*dt0*m-m0, F*L0+F0*L, -4*F0^2*L0^2+4*F0^2*L^2+v^2}, {F*dt0*m-m0, F*L0+F0*L, dt*m0-dt0*m}, {F*dt0*m-m0, F*L0+F0*L, dt0*L0+dt*L}, {F*dt0*m-m0, F*L0+F0*L, 2*F0*L0+c}, {F*dt0*m-m0, -4*F0^2*L0^2+4*F0^2*L^2+v^2, dt*m0-dt0*m}, {F*dt0*m-m0, -4*F0^2*L0^2+4*F0^2*L^2+v^2, dt0*L0+dt*L}, {F*dt0*m-m0, -4*F0^2*L0^2+4*F0^2*L^2+v^2, 2*F0*L0+c}, {F*dt0*m-m0, dt*m0-dt0*m, dt0*L0+dt*L}, {F*dt0*m-m0, dt*m0-dt0*m, 2*F0*L0+c}, {F*dt0*m-m0, dt0*L0+dt*L, 2*F0*L0+c}, {F*dt0*L0+L, F0*m0-F*m, F*L0+F0*L}, {F*dt0*L0+L, F0*m0-F*m, -4*F0^2*L0^2+4*F0^2*L^2+v^2}, {F*dt0*L0+L, F0*m0-F*m, dt*m0-dt0*m}, {F*dt0*L0+L, F0*m0-F*m, dt0*L0+dt*L}, {F*dt0*L0+L, F0*m0-F*m, 2*F0*L0+c}, {F*dt0*L0+L, F*L0+F0*L, dt*m0-dt0*m}, {F*dt0*L0+L, -4*F0^2*L0^2+4*F0^2*L^2+v^2, dt*m0-dt0*m}, {F*dt0*L0+L, dt*m0-dt0*m, dt0*L0+dt*L}, {F*dt0*L0+L, dt*m0-dt0*m, 2*F0*L0+c}, {F0*m0-F*m, F*L0+F0*L, -4*F0^2*L0^2+4*F0^2*L^2+v^2}, {F0*m0-F*m, F*L0+F0*L, dt*m0-dt0*m}, {F0*m0-F*m, F*L0+F0*L, dt0*L0+dt*L}, {F0*m0-F*m, F*L0+F0*L, 2*F0*L0+c}, {F0*m0-F*m, -4*F0^2*L0^2+4*F0^2*L^2+v^2, dt*m0-dt0*m}, {F0*m0-F*m, -4*F0^2*L0^2+4*F0^2*L^2+v^2, dt0*L0+dt*L}, {F0*m0-F*m, -4*F0^2*L0^2+4*F0^2*L^2+v^2, 2*F0*L0+c}, {F0*m0-F*m, dt*m0-dt0*m, dt0*L0+dt*L}, {F0*m0-F*m, dt*m0-dt0*m, 2*F0*L0+c}, {F0*m0-F*m, dt0*L0+dt*L, 2*F0*L0+c}, {F*L0+F0*L, -4*F0^2*L0^2+4*F0^2*L^2+v^2, dt*m0-dt0*m}, {F*L0+F0*L, dt*m0-dt0*m, dt0*L0+dt*L}, {F*L0+F0*L, dt*m0-dt0*m, 2*F0*L0+c}, {-4*F0^2*L0^2+4*F0^2*L^2+v^2, dt*m0-dt0*m, dt0*L0+dt*L}, {-4*F0^2*L0^2+4*F0^2*L^2+v^2, dt*m0-dt0*m, 2*F0*L0+c}, {dt*m0-dt0*m, dt0*L0+dt*L, 2*F0*L0+c}, {-L*u0+L0*u}, {L0*m0-L*m}, {-L*u0+L0*u, L0*m0-L*m}, {-L*u0+L0*u, F*dt0*m-m0}, {-L*u0+L0*u, F*dt0*L0-L}, {-L*u0+L0*u, F0*m0-F*m}, {-L*u0+L0*u, -F*L0+F0*L}, {-L*u0+L0*u, -4*F0^2*L0^2+4*F0^2*L^2+v^2}, {-L*u0+L0*u, dt*m0-dt0*m}, {-L*u0+L0*u, -dt0*L0+dt*L}, {-L*u0+L0*u, -2*F0*L0+c}, {L0*m0-L*m, F*dt0*m-m0}, {L0*m0-L*m, F*dt0*L0-L}, {L0*m0-L*m, F0*m0-F*m}, {L0*m0-L*m, -F*L0+F0*L}, {L0*m0-L*m, -4*F0^2*L0^2+4*F0^2*L^2+v^2}, {L0*m0-L*m, dt*m0-dt0*m}, {L0*m0-L*m, -dt0*L0+dt*L}, {L0*m0-L*m, -2*F0*L0+c}, {F*dt0*m-m0, F*dt0*L0-L}, {F*dt0*m-m0, -F*L0+F0*L}, {F*dt0*m-m0, -dt0*L0+dt*L}, {F*dt0*m-m0, -2*F0*L0+c}, {F*dt0*L0-L, F0*m0-F*m}, {F*dt0*L0-L, dt*m0-dt0*m}, {F0*m0-F*m, -F*L0+F0*L}, {F0*m0-F*m, -dt0*L0+dt*L}, {F0*m0-F*m, -2*F0*L0+c}, {-F*L0+F0*L, dt*m0-dt0*m}, {dt*m0-dt0*m, -dt0*L0+dt*L}, {dt*m0-dt0*m, -2*F0*L0+c}, {-L*u0+L0*u, L0*m0-L*m, F*dt0*m-m0}, {-L*u0+L0*u, L0*m0-L*m, F*dt0*L0-L}, {-L*u0+L0*u, L0*m0-L*m, F0*m0-F*m}, {-L*u0+L0*u, L0*m0-L*m, -F*L0+F0*L}, {-L*u0+L0*u, L0*m0-L*m, -4*F0^2*L0^2+4*F0^2*L^2+v^2}, {-L*u0+L0*u, L0*m0-L*m, dt*m0-dt0*m}, {-L*u0+L0*u, L0*m0-L*m, -dt0*L0+dt*L}, {-L*u0+L0*u, L0*m0-L*m, -2*F0*L0+c}, {-L*u0+L0*u, F*dt0*m-m0, F*dt0*L0-L}, {-L*u0+L0*u, F*dt0*m-m0, F0*m0-F*m}, {-L*u0+L0*u, F*dt0*m-m0, -F*L0+F0*L}, {-L*u0+L0*u, F*dt0*m-m0, -4*F0^2*L0^2+4*F0^2*L^2+v^2}, {-L*u0+L0*u, F*dt0*m-m0, dt*m0-dt0*m}, {-L*u0+L0*u, F*dt0*m-m0, -dt0*L0+dt*L}, {-L*u0+L0*u, F*dt0*m-m0, -2*F0*L0+c}, {-L*u0+L0*u, F*dt0*L0-L, F0*m0-F*m}, {-L*u0+L0*u, F*dt0*L0-L, -F*L0+F0*L}, {-L*u0+L0*u, F*dt0*L0-L, -4*F0^2*L0^2+4*F0^2*L^2+v^2}, {-L*u0+L0*u, F*dt0*L0-L, dt*m0-dt0*m}, {-L*u0+L0*u, F*dt0*L0-L, -dt0*L0+dt*L}, {-L*u0+L0*u, F*dt0*L0-L, -2*F0*L0+c}, {-L*u0+L0*u, F0*m0-F*m, -F*L0+F0*L}, {-L*u0+L0*u, F0*m0-F*m, -4*F0^2*L0^2+4*F0^2*L^2+v^2}, {-L*u0+L0*u, F0*m0-F*m, dt*m0-dt0*m}, {-L*u0+L0*u, F0*m0-F*m, -dt0*L0+dt*L}, {-L*u0+L0*u, F0*m0-F*m, -2*F0*L0+c}, {-L*u0+L0*u, -F*L0+F0*L, -4*F0^2*L0^2+4*F0^2*L^2+v^2}, {-L*u0+L0*u, -F*L0+F0*L, dt*m0-dt0*m}, {-L*u0+L0*u, -F*L0+F0*L, -dt0*L0+dt*L}, {-L*u0+L0*u, -F*L0+F0*L, -2*F0*L0+c}, {-L*u0+L0*u, -4*F0^2*L0^2+4*F0^2*L^2+v^2, dt*m0-dt0*m}, {-L*u0+L0*u, -4*F0^2*L0^2+4*F0^2*L^2+v^2, -dt0*L0+dt*L}, {-L*u0+L0*u, -4*F0^2*L0^2+4*F0^2*L^2+v^2, -2*F0*L0+c}, {-L*u0+L0*u, dt*m0-dt0*m, -dt0*L0+dt*L}, {-L*u0+L0*u, dt*m0-dt0*m, -2*F0*L0+c}, {-L*u0+L0*u, -dt0*L0+dt*L, -2*F0*L0+c}, {L0*m0-L*m, F*dt0*m-m0, F*dt0*L0-L}, {L0*m0-L*m, F*dt0*m-m0, F0*m0-F*m}, {L0*m0-L*m, F*dt0*m-m0, -F*L0+F0*L}, {L0*m0-L*m, F*dt0*m-m0, -4*F0^2*L0^2+4*F0^2*L^2+v^2}, {L0*m0-L*m, F*dt0*m-m0, dt*m0-dt0*m}, {L0*m0-L*m, F*dt0*m-m0, -dt0*L0+dt*L}, {L0*m0-L*m, F*dt0*m-m0, -2*F0*L0+c}, {L0*m0-L*m, F*dt0*L0-L, F0*m0-F*m}, {L0*m0-L*m, F*dt0*L0-L, -F*L0+F0*L}, {L0*m0-L*m, F*dt0*L0-L, -4*F0^2*L0^2+4*F0^2*L^2+v^2}, {L0*m0-L*m, F*dt0*L0-L, dt*m0-dt0*m}, {L0*m0-L*m, F*dt0*L0-L, -dt0*L0+dt*L}, {L0*m0-L*m, F*dt0*L0-L, -2*F0*L0+c}, {L0*m0-L*m, F0*m0-F*m, -F*L0+F0*L}, {L0*m0-L*m, F0*m0-F*m, -4*F0^2*L0^2+4*F0^2*L^2+v^2}, {L0*m0-L*m, F0*m0-F*m, dt*m0-dt0*m}, {L0*m0-L*m, F0*m0-F*m, -dt0*L0+dt*L}, {L0*m0-L*m, F0*m0-F*m, -2*F0*L0+c}, {L0*m0-L*m, -F*L0+F0*L, -4*F0^2*L0^2+4*F0^2*L^2+v^2}, {L0*m0-L*m, -F*L0+F0*L, dt*m0-dt0*m}, {L0*m0-L*m, -F*L0+F0*L, -dt0*L0+dt*L}, {L0*m0-L*m, -F*L0+F0*L, -2*F0*L0+c}, {L0*m0-L*m, -4*F0^2*L0^2+4*F0^2*L^2+v^2, dt*m0-dt0*m}, {L0*m0-L*m, -4*F0^2*L0^2+4*F0^2*L^2+v^2, -dt0*L0+dt*L}, {L0*m0-L*m, -4*F0^2*L0^2+4*F0^2*L^2+v^2, -2*F0*L0+c}, {L0*m0-L*m, dt*m0-dt0*m, -dt0*L0+dt*L}, {L0*m0-L*m, dt*m0-dt0*m, -2*F0*L0+c}, {L0*m0-L*m, -dt0*L0+dt*L, -2*F0*L0+c}, {F*dt0*m-m0, F*dt0*L0-L, F0*m0-F*m}, {F*dt0*m-m0, F*dt0*L0-L, -F*L0+F0*L}, {F*dt0*m-m0, F*dt0*L0-L, -4*F0^2*L0^2+4*F0^2*L^2+v^2}, {F*dt0*m-m0, F*dt0*L0-L, dt*m0-dt0*m}, {F*dt0*m-m0, F*dt0*L0-L, -dt0*L0+dt*L}, {F*dt0*m-m0, F*dt0*L0-L, -2*F0*L0+c}, {F*dt0*m-m0, F0*m0-F*m, -F*L0+F0*L}, {F*dt0*m-m0, F0*m0-F*m, -dt0*L0+dt*L}, {F*dt0*m-m0, F0*m0-F*m, -2*F0*L0+c}, {F*dt0*m-m0, -F*L0+F0*L, -4*F0^2*L0^2+4*F0^2*L^2+v^2}, {F*dt0*m-m0, -F*L0+F0*L, dt*m0-dt0*m}, {F*dt0*m-m0, -F*L0+F0*L, -dt0*L0+dt*L}, {F*dt0*m-m0, -F*L0+F0*L, -2*F0*L0+c}, {F*dt0*m-m0, -4*F0^2*L0^2+4*F0^2*L^2+v^2, -dt0*L0+dt*L}, {F*dt0*m-m0, -4*F0^2*L0^2+4*F0^2*L^2+v^2, -2*F0*L0+c}, {F*dt0*m-m0, dt*m0-dt0*m, -dt0*L0+dt*L}, {F*dt0*m-m0, dt*m0-dt0*m, -2*F0*L0+c}, {F*dt0*m-m0, -dt0*L0+dt*L, -2*F0*L0+c}, {F*dt0*L0-L, F0*m0-F*m, -F*L0+F0*L}, {F*dt0*L0-L, F0*m0-F*m, -4*F0^2*L0^2+4*F0^2*L^2+v^2}, {F*dt0*L0-L, F0*m0-F*m, dt*m0-dt0*m}, {F*dt0*L0-L, F0*m0-F*m, -dt0*L0+dt*L}, {F*dt0*L0-L, F0*m0-F*m, -2*F0*L0+c}, {F*dt0*L0-L, -F*L0+F0*L, dt*m0-dt0*m}, {F*dt0*L0-L, -4*F0^2*L0^2+4*F0^2*L^2+v^2, dt*m0-dt0*m}, {F*dt0*L0-L, dt*m0-dt0*m, -dt0*L0+dt*L}, {F*dt0*L0-L, dt*m0-dt0*m, -2*F0*L0+c}, {F0*m0-F*m, -F*L0+F0*L, -4*F0^2*L0^2+4*F0^2*L^2+v^2}, {F0*m0-F*m, -F*L0+F0*L, dt*m0-dt0*m}, {F0*m0-F*m, -F*L0+F0*L, -dt0*L0+dt*L}, {F0*m0-F*m, -F*L0+F0*L, -2*F0*L0+c}, {F0*m0-F*m, -4*F0^2*L0^2+4*F0^2*L^2+v^2, -dt0*L0+dt*L}, {F0*m0-F*m, -4*F0^2*L0^2+4*F0^2*L^2+v^2, -2*F0*L0+c}, {F0*m0-F*m, dt*m0-dt0*m, -dt0*L0+dt*L}, {F0*m0-F*m, dt*m0-dt0*m, -2*F0*L0+c}, {F0*m0-F*m, -dt0*L0+dt*L, -2*F0*L0+c}, {-F*L0+F0*L, -4*F0^2*L0^2+4*F0^2*L^2+v^2, dt*m0-dt0*m}, {-F*L0+F0*L, dt*m0-dt0*m, -dt0*L0+dt*L}, {-F*L0+F0*L, dt*m0-dt0*m, -2*F0*L0+c}, {-4*F0^2*L0^2+4*F0^2*L^2+v^2, dt*m0-dt0*m, -dt0*L0+dt*L}, {-4*F0^2*L0^2+4*F0^2*L^2+v^2, dt*m0-dt0*m, -2*F0*L0+c}, {dt*m0-dt0*m, -dt0*L0+dt*L, -2*F0*L0+c}, {F*dt0*m-m0, L0}, {F*dt0*m-m0, v}, {F*dt0*m-m0, c}, {F0*m0-F*m, L0}, {F0*m0-F*m, v}, {F0*m0-F*m, c}, {dt*m0-dt0*m, L0}, {dt*m0-dt0*m, v}, {dt*m0-dt0*m, c}, {F*dt0*m-m0, F0*m0-F*m, L0}, {F*dt0*m-m0, F0*m0-F*m, v}, {F*dt0*m-m0, F0*m0-F*m, c}, {F*dt0*m-m0, dt*m0-dt0*m, L0}, {F*dt0*m-m0, dt*m0-dt0*m, v}, {F*dt0*m-m0, dt*m0-dt0*m, c}, {F*dt0*m-m0, L0, v}, {F*dt0*m-m0, L0, c}, {F*dt0*m-m0, v, c}, {F0*m0-F*m, dt*m0-dt0*m, L0}, {F0*m0-F*m, dt*m0-dt0*m, v}, {F0*m0-F*m, dt*m0-dt0*m, c}, {F0*m0-F*m, L0, v}, {F0*m0-F*m, L0, c}, {F0*m0-F*m, v, c}, {dt*m0-dt0*m, L0, v}, {dt*m0-dt0*m, L0, c}, {dt*m0-dt0*m, v, c}};

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
f = openOut "results/relativistic_laws_updated/abduction/noiseless/1_axiom(s)_removed/combo_3/reasoning/reasoning_output.txt";
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

print("Reasoning complete. Output written to results/relativistic_laws_updated/abduction/noiseless/1_axiom(s)_removed/combo_3/reasoning/reasoning_output.txt");
