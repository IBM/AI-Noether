-- AI-Noether: Reasoning Template (Noiseless)
-- Tests if candidate axiom sets, when added to remaining axioms, prove targets

needsPackage("PrimaryDecomposition", Reload => true)

-- Ring definition
R = QQ[mr, vm, vc, pc, Em, Er, Ec, mc, mm, pm, c, MonomialOrder => Lex];

-- Input data
remainingAxioms = toList([pm^2*(c^2 - vm^2) - mm^2*vm^2*c^2, Ec^2 - (mc*c)^2 - (pc*c)^2, 2*Em*Er - Ec^2 + Em^2 + Er^2, pc - pm, vm - 4/5*c, pc^2*(c^2 - vc^2) - mc^2*vc^2*c^2]);
qList = toList([16*mm^2*c^4 - 9*pm^2*c^2]);
k = #qList;

-- Per-target variable partitions
measuredPerTarget = {{mm, pm, c}};
nonMeasuredPerTarget = {{mr, vm, vc, pc, Em, Er, Ec, mc}};

-- Candidate axiom sets to test (list of lists)
candidateSets = {{}, {c}, {pm}, {Ec}, {Em+Er}, {pc-pm}, {vm-4/5*c}, {c, pm}, {c, Ec}, {c, Em+Er}, {c, pc-pm}, {c, vm-4/5*c}, {pm, Ec}, {pm, Em+Er}, {pm, pc-pm}, {pm, vm-4/5*c}, {Ec, Em+Er}, {Ec, pc-pm}, {Ec, vm-4/5*c}, {Em+Er, pc-pm}, {Em+Er, vm-4/5*c}, {pc-pm, vm-4/5*c}, {c, pm, Ec}, {c, pm, Em+Er}, {c, pm, pc-pm}, {c, pm, vm-4/5*c}, {c, Ec, Em+Er}, {c, Ec, pc-pm}, {c, Ec, vm-4/5*c}, {c, Em+Er, pc-pm}, {c, Em+Er, vm-4/5*c}, {c, pc-pm, vm-4/5*c}, {pm, Ec, Em+Er}, {pm, Ec, pc-pm}, {pm, Ec, vm-4/5*c}, {pm, Em+Er, pc-pm}, {pm, Em+Er, vm-4/5*c}, {pm, pc-pm, vm-4/5*c}, {Ec, Em+Er, pc-pm}, {Ec, Em+Er, vm-4/5*c}, {Ec, pc-pm, vm-4/5*c}, {Em+Er, pc-pm, vm-4/5*c}, {c, pm, Ec, Em+Er}, {c, pm, Ec, pc-pm}, {c, pm, Ec, vm-4/5*c}, {c, pm, Em+Er, pc-pm}, {c, pm, Em+Er, vm-4/5*c}, {c, pm, pc-pm, vm-4/5*c}, {c, Ec, Em+Er, pc-pm}, {c, Ec, Em+Er, vm-4/5*c}, {c, Ec, pc-pm, vm-4/5*c}, {c, Em+Er, pc-pm, vm-4/5*c}, {pm, Ec, Em+Er, pc-pm}, {pm, Ec, Em+Er, vm-4/5*c}, {pm, Ec, pc-pm, vm-4/5*c}, {pm, Em+Er, pc-pm, vm-4/5*c}, {Ec, Em+Er, pc-pm, vm-4/5*c}, {c}, {Ec}, {Em+Er}, {pc-pm}, {vc}, {vm-4/5*c}, {c, Ec}, {c, Em+Er}, {c, pc-pm}, {c, vc}, {c, vm-4/5*c}, {Ec, Em+Er}, {Ec, pc-pm}, {Ec, vc}, {Ec, vm-4/5*c}, {Em+Er, pc-pm}, {Em+Er, vc}, {Em+Er, vm-4/5*c}, {pc-pm, vc}, {pc-pm, vm-4/5*c}, {vc, vm-4/5*c}, {c, Ec, Em+Er}, {c, Ec, pc-pm}, {c, Ec, vc}, {c, Ec, vm-4/5*c}, {c, Em+Er, pc-pm}, {c, Em+Er, vc}, {c, Em+Er, vm-4/5*c}, {c, pc-pm, vc}, {c, pc-pm, vm-4/5*c}, {c, vc, vm-4/5*c}, {Ec, Em+Er, pc-pm}, {Ec, Em+Er, vc}, {Ec, Em+Er, vm-4/5*c}, {Ec, pc-pm, vc}, {Ec, pc-pm, vm-4/5*c}, {Ec, vc, vm-4/5*c}, {Em+Er, pc-pm, vc}, {Em+Er, pc-pm, vm-4/5*c}, {Em+Er, vc, vm-4/5*c}, {pc-pm, vc, vm-4/5*c}, {c, Ec, Em+Er, pc-pm}, {c, Ec, Em+Er, vc}, {c, Ec, Em+Er, vm-4/5*c}, {c, Ec, pc-pm, vc}, {c, Ec, pc-pm, vm-4/5*c}, {c, Ec, vc, vm-4/5*c}, {c, Em+Er, pc-pm, vc}, {c, Em+Er, pc-pm, vm-4/5*c}, {c, Em+Er, vc, vm-4/5*c}, {c, pc-pm, vc, vm-4/5*c}, {Ec, Em+Er, pc-pm, vc}, {Ec, Em+Er, pc-pm, vm-4/5*c}, {Ec, Em+Er, vc, vm-4/5*c}, {Ec, pc-pm, vc, vm-4/5*c}, {Em+Er, pc-pm, vc, vm-4/5*c}, {4*mm*c+3*pm}, {-mc^2*c^2-pm^2*c^2+Ec^2}, {9*vc^2*mc^2+16*vc^2*mm^2-9*pm^2}, {Em+Er+Ec}, {pc-pm}, {vm-4/5*c}, {4*mm*c+3*pm, -mc^2*c^2-pm^2*c^2+Ec^2}, {4*mm*c+3*pm, 9*vc^2*mc^2+16*vc^2*mm^2-9*pm^2}, {4*mm*c+3*pm, Em+Er+Ec}, {4*mm*c+3*pm, pc-pm}, {4*mm*c+3*pm, vm-4/5*c}, {-mc^2*c^2-pm^2*c^2+Ec^2, 9*vc^2*mc^2+16*vc^2*mm^2-9*pm^2}, {-mc^2*c^2-pm^2*c^2+Ec^2, Em+Er+Ec}, {-mc^2*c^2-pm^2*c^2+Ec^2, pc-pm}, {-mc^2*c^2-pm^2*c^2+Ec^2, vm-4/5*c}, {9*vc^2*mc^2+16*vc^2*mm^2-9*pm^2, Em+Er+Ec}, {9*vc^2*mc^2+16*vc^2*mm^2-9*pm^2, pc-pm}, {9*vc^2*mc^2+16*vc^2*mm^2-9*pm^2, vm-4/5*c}, {Em+Er+Ec, pc-pm}, {Em+Er+Ec, vm-4/5*c}, {pc-pm, vm-4/5*c}, {4*mm*c+3*pm, -mc^2*c^2-pm^2*c^2+Ec^2, 9*vc^2*mc^2+16*vc^2*mm^2-9*pm^2}, {4*mm*c+3*pm, -mc^2*c^2-pm^2*c^2+Ec^2, Em+Er+Ec}, {4*mm*c+3*pm, -mc^2*c^2-pm^2*c^2+Ec^2, pc-pm}, {4*mm*c+3*pm, -mc^2*c^2-pm^2*c^2+Ec^2, vm-4/5*c}, {4*mm*c+3*pm, 9*vc^2*mc^2+16*vc^2*mm^2-9*pm^2, Em+Er+Ec}, {4*mm*c+3*pm, 9*vc^2*mc^2+16*vc^2*mm^2-9*pm^2, pc-pm}, {4*mm*c+3*pm, 9*vc^2*mc^2+16*vc^2*mm^2-9*pm^2, vm-4/5*c}, {4*mm*c+3*pm, Em+Er+Ec, pc-pm}, {4*mm*c+3*pm, Em+Er+Ec, vm-4/5*c}, {4*mm*c+3*pm, pc-pm, vm-4/5*c}, {-mc^2*c^2-pm^2*c^2+Ec^2, 9*vc^2*mc^2+16*vc^2*mm^2-9*pm^2, Em+Er+Ec}, {-mc^2*c^2-pm^2*c^2+Ec^2, 9*vc^2*mc^2+16*vc^2*mm^2-9*pm^2, pc-pm}, {-mc^2*c^2-pm^2*c^2+Ec^2, 9*vc^2*mc^2+16*vc^2*mm^2-9*pm^2, vm-4/5*c}, {-mc^2*c^2-pm^2*c^2+Ec^2, Em+Er+Ec, pc-pm}, {-mc^2*c^2-pm^2*c^2+Ec^2, Em+Er+Ec, vm-4/5*c}, {-mc^2*c^2-pm^2*c^2+Ec^2, pc-pm, vm-4/5*c}, {9*vc^2*mc^2+16*vc^2*mm^2-9*pm^2, Em+Er+Ec, pc-pm}, {9*vc^2*mc^2+16*vc^2*mm^2-9*pm^2, Em+Er+Ec, vm-4/5*c}, {9*vc^2*mc^2+16*vc^2*mm^2-9*pm^2, pc-pm, vm-4/5*c}, {Em+Er+Ec, pc-pm, vm-4/5*c}, {4*mm*c+3*pm, -mc^2*c^2-pm^2*c^2+Ec^2, 9*vc^2*mc^2+16*vc^2*mm^2-9*pm^2, Em+Er+Ec}, {4*mm*c+3*pm, -mc^2*c^2-pm^2*c^2+Ec^2, 9*vc^2*mc^2+16*vc^2*mm^2-9*pm^2, pc-pm}, {4*mm*c+3*pm, -mc^2*c^2-pm^2*c^2+Ec^2, 9*vc^2*mc^2+16*vc^2*mm^2-9*pm^2, vm-4/5*c}, {4*mm*c+3*pm, -mc^2*c^2-pm^2*c^2+Ec^2, Em+Er+Ec, pc-pm}, {4*mm*c+3*pm, -mc^2*c^2-pm^2*c^2+Ec^2, Em+Er+Ec, vm-4/5*c}, {4*mm*c+3*pm, -mc^2*c^2-pm^2*c^2+Ec^2, pc-pm, vm-4/5*c}, {4*mm*c+3*pm, 9*vc^2*mc^2+16*vc^2*mm^2-9*pm^2, Em+Er+Ec, pc-pm}, {4*mm*c+3*pm, 9*vc^2*mc^2+16*vc^2*mm^2-9*pm^2, Em+Er+Ec, vm-4/5*c}, {4*mm*c+3*pm, 9*vc^2*mc^2+16*vc^2*mm^2-9*pm^2, pc-pm, vm-4/5*c}, {4*mm*c+3*pm, Em+Er+Ec, pc-pm, vm-4/5*c}, {-mc^2*c^2-pm^2*c^2+Ec^2, 9*vc^2*mc^2+16*vc^2*mm^2-9*pm^2, Em+Er+Ec, pc-pm}, {-mc^2*c^2-pm^2*c^2+Ec^2, 9*vc^2*mc^2+16*vc^2*mm^2-9*pm^2, Em+Er+Ec, vm-4/5*c}, {-mc^2*c^2-pm^2*c^2+Ec^2, 9*vc^2*mc^2+16*vc^2*mm^2-9*pm^2, pc-pm, vm-4/5*c}, {-mc^2*c^2-pm^2*c^2+Ec^2, Em+Er+Ec, pc-pm, vm-4/5*c}, {9*vc^2*mc^2+16*vc^2*mm^2-9*pm^2, Em+Er+Ec, pc-pm, vm-4/5*c}, {4*mm*c-3*pm}, {-mc^2*c^2-pm^2*c^2+Ec^2}, {9*vc^2*mc^2+16*vc^2*mm^2-9*pm^2}, {Em+Er+Ec}, {pc-pm}, {vm-4/5*c}, {4*mm*c-3*pm, -mc^2*c^2-pm^2*c^2+Ec^2}, {4*mm*c-3*pm, 9*vc^2*mc^2+16*vc^2*mm^2-9*pm^2}, {4*mm*c-3*pm, Em+Er+Ec}, {4*mm*c-3*pm, pc-pm}, {4*mm*c-3*pm, vm-4/5*c}, {-mc^2*c^2-pm^2*c^2+Ec^2, 9*vc^2*mc^2+16*vc^2*mm^2-9*pm^2}, {-mc^2*c^2-pm^2*c^2+Ec^2, Em+Er+Ec}, {-mc^2*c^2-pm^2*c^2+Ec^2, pc-pm}, {-mc^2*c^2-pm^2*c^2+Ec^2, vm-4/5*c}, {9*vc^2*mc^2+16*vc^2*mm^2-9*pm^2, Em+Er+Ec}, {9*vc^2*mc^2+16*vc^2*mm^2-9*pm^2, pc-pm}, {9*vc^2*mc^2+16*vc^2*mm^2-9*pm^2, vm-4/5*c}, {Em+Er+Ec, pc-pm}, {Em+Er+Ec, vm-4/5*c}, {pc-pm, vm-4/5*c}, {4*mm*c-3*pm, -mc^2*c^2-pm^2*c^2+Ec^2, 9*vc^2*mc^2+16*vc^2*mm^2-9*pm^2}, {4*mm*c-3*pm, -mc^2*c^2-pm^2*c^2+Ec^2, Em+Er+Ec}, {4*mm*c-3*pm, -mc^2*c^2-pm^2*c^2+Ec^2, pc-pm}, {4*mm*c-3*pm, -mc^2*c^2-pm^2*c^2+Ec^2, vm-4/5*c}, {4*mm*c-3*pm, 9*vc^2*mc^2+16*vc^2*mm^2-9*pm^2, Em+Er+Ec}, {4*mm*c-3*pm, 9*vc^2*mc^2+16*vc^2*mm^2-9*pm^2, pc-pm}, {4*mm*c-3*pm, 9*vc^2*mc^2+16*vc^2*mm^2-9*pm^2, vm-4/5*c}, {4*mm*c-3*pm, Em+Er+Ec, pc-pm}, {4*mm*c-3*pm, Em+Er+Ec, vm-4/5*c}, {4*mm*c-3*pm, pc-pm, vm-4/5*c}, {-mc^2*c^2-pm^2*c^2+Ec^2, 9*vc^2*mc^2+16*vc^2*mm^2-9*pm^2, Em+Er+Ec}, {-mc^2*c^2-pm^2*c^2+Ec^2, 9*vc^2*mc^2+16*vc^2*mm^2-9*pm^2, pc-pm}, {-mc^2*c^2-pm^2*c^2+Ec^2, 9*vc^2*mc^2+16*vc^2*mm^2-9*pm^2, vm-4/5*c}, {-mc^2*c^2-pm^2*c^2+Ec^2, Em+Er+Ec, pc-pm}, {-mc^2*c^2-pm^2*c^2+Ec^2, Em+Er+Ec, vm-4/5*c}, {-mc^2*c^2-pm^2*c^2+Ec^2, pc-pm, vm-4/5*c}, {9*vc^2*mc^2+16*vc^2*mm^2-9*pm^2, Em+Er+Ec, pc-pm}, {9*vc^2*mc^2+16*vc^2*mm^2-9*pm^2, Em+Er+Ec, vm-4/5*c}, {9*vc^2*mc^2+16*vc^2*mm^2-9*pm^2, pc-pm, vm-4/5*c}, {Em+Er+Ec, pc-pm, vm-4/5*c}, {4*mm*c-3*pm, -mc^2*c^2-pm^2*c^2+Ec^2, 9*vc^2*mc^2+16*vc^2*mm^2-9*pm^2, Em+Er+Ec}, {4*mm*c-3*pm, -mc^2*c^2-pm^2*c^2+Ec^2, 9*vc^2*mc^2+16*vc^2*mm^2-9*pm^2, pc-pm}, {4*mm*c-3*pm, -mc^2*c^2-pm^2*c^2+Ec^2, 9*vc^2*mc^2+16*vc^2*mm^2-9*pm^2, vm-4/5*c}, {4*mm*c-3*pm, -mc^2*c^2-pm^2*c^2+Ec^2, Em+Er+Ec, pc-pm}, {4*mm*c-3*pm, -mc^2*c^2-pm^2*c^2+Ec^2, Em+Er+Ec, vm-4/5*c}, {4*mm*c-3*pm, -mc^2*c^2-pm^2*c^2+Ec^2, pc-pm, vm-4/5*c}, {4*mm*c-3*pm, 9*vc^2*mc^2+16*vc^2*mm^2-9*pm^2, Em+Er+Ec, pc-pm}, {4*mm*c-3*pm, 9*vc^2*mc^2+16*vc^2*mm^2-9*pm^2, Em+Er+Ec, vm-4/5*c}, {4*mm*c-3*pm, 9*vc^2*mc^2+16*vc^2*mm^2-9*pm^2, pc-pm, vm-4/5*c}, {4*mm*c-3*pm, Em+Er+Ec, pc-pm, vm-4/5*c}, {-mc^2*c^2-pm^2*c^2+Ec^2, 9*vc^2*mc^2+16*vc^2*mm^2-9*pm^2, Em+Er+Ec, pc-pm}, {-mc^2*c^2-pm^2*c^2+Ec^2, 9*vc^2*mc^2+16*vc^2*mm^2-9*pm^2, Em+Er+Ec, vm-4/5*c}, {-mc^2*c^2-pm^2*c^2+Ec^2, 9*vc^2*mc^2+16*vc^2*mm^2-9*pm^2, pc-pm, vm-4/5*c}, {-mc^2*c^2-pm^2*c^2+Ec^2, Em+Er+Ec, pc-pm, vm-4/5*c}, {9*vc^2*mc^2+16*vc^2*mm^2-9*pm^2, Em+Er+Ec, pc-pm, vm-4/5*c}, {4*mm*c+3*pm}, {-mc^2*c^2-pm^2*c^2+Ec^2}, {9*vc^2*mc^2+16*vc^2*mm^2-9*pm^2}, {Em+Er-Ec}, {pc-pm}, {vm-4/5*c}, {4*mm*c+3*pm, -mc^2*c^2-pm^2*c^2+Ec^2}, {4*mm*c+3*pm, 9*vc^2*mc^2+16*vc^2*mm^2-9*pm^2}, {4*mm*c+3*pm, Em+Er-Ec}, {4*mm*c+3*pm, pc-pm}, {4*mm*c+3*pm, vm-4/5*c}, {-mc^2*c^2-pm^2*c^2+Ec^2, 9*vc^2*mc^2+16*vc^2*mm^2-9*pm^2}, {-mc^2*c^2-pm^2*c^2+Ec^2, Em+Er-Ec}, {-mc^2*c^2-pm^2*c^2+Ec^2, pc-pm}, {-mc^2*c^2-pm^2*c^2+Ec^2, vm-4/5*c}, {9*vc^2*mc^2+16*vc^2*mm^2-9*pm^2, Em+Er-Ec}, {9*vc^2*mc^2+16*vc^2*mm^2-9*pm^2, pc-pm}, {9*vc^2*mc^2+16*vc^2*mm^2-9*pm^2, vm-4/5*c}, {Em+Er-Ec, pc-pm}, {Em+Er-Ec, vm-4/5*c}, {pc-pm, vm-4/5*c}, {4*mm*c+3*pm, -mc^2*c^2-pm^2*c^2+Ec^2, 9*vc^2*mc^2+16*vc^2*mm^2-9*pm^2}, {4*mm*c+3*pm, -mc^2*c^2-pm^2*c^2+Ec^2, Em+Er-Ec}, {4*mm*c+3*pm, -mc^2*c^2-pm^2*c^2+Ec^2, pc-pm}, {4*mm*c+3*pm, -mc^2*c^2-pm^2*c^2+Ec^2, vm-4/5*c}, {4*mm*c+3*pm, 9*vc^2*mc^2+16*vc^2*mm^2-9*pm^2, Em+Er-Ec}, {4*mm*c+3*pm, 9*vc^2*mc^2+16*vc^2*mm^2-9*pm^2, pc-pm}, {4*mm*c+3*pm, 9*vc^2*mc^2+16*vc^2*mm^2-9*pm^2, vm-4/5*c}, {4*mm*c+3*pm, Em+Er-Ec, pc-pm}, {4*mm*c+3*pm, Em+Er-Ec, vm-4/5*c}, {4*mm*c+3*pm, pc-pm, vm-4/5*c}, {-mc^2*c^2-pm^2*c^2+Ec^2, 9*vc^2*mc^2+16*vc^2*mm^2-9*pm^2, Em+Er-Ec}, {-mc^2*c^2-pm^2*c^2+Ec^2, 9*vc^2*mc^2+16*vc^2*mm^2-9*pm^2, pc-pm}, {-mc^2*c^2-pm^2*c^2+Ec^2, 9*vc^2*mc^2+16*vc^2*mm^2-9*pm^2, vm-4/5*c}, {-mc^2*c^2-pm^2*c^2+Ec^2, Em+Er-Ec, pc-pm}, {-mc^2*c^2-pm^2*c^2+Ec^2, Em+Er-Ec, vm-4/5*c}, {-mc^2*c^2-pm^2*c^2+Ec^2, pc-pm, vm-4/5*c}, {9*vc^2*mc^2+16*vc^2*mm^2-9*pm^2, Em+Er-Ec, pc-pm}, {9*vc^2*mc^2+16*vc^2*mm^2-9*pm^2, Em+Er-Ec, vm-4/5*c}, {9*vc^2*mc^2+16*vc^2*mm^2-9*pm^2, pc-pm, vm-4/5*c}, {Em+Er-Ec, pc-pm, vm-4/5*c}, {4*mm*c+3*pm, -mc^2*c^2-pm^2*c^2+Ec^2, 9*vc^2*mc^2+16*vc^2*mm^2-9*pm^2, Em+Er-Ec}, {4*mm*c+3*pm, -mc^2*c^2-pm^2*c^2+Ec^2, 9*vc^2*mc^2+16*vc^2*mm^2-9*pm^2, pc-pm}, {4*mm*c+3*pm, -mc^2*c^2-pm^2*c^2+Ec^2, 9*vc^2*mc^2+16*vc^2*mm^2-9*pm^2, vm-4/5*c}, {4*mm*c+3*pm, -mc^2*c^2-pm^2*c^2+Ec^2, Em+Er-Ec, pc-pm}, {4*mm*c+3*pm, -mc^2*c^2-pm^2*c^2+Ec^2, Em+Er-Ec, vm-4/5*c}, {4*mm*c+3*pm, -mc^2*c^2-pm^2*c^2+Ec^2, pc-pm, vm-4/5*c}, {4*mm*c+3*pm, 9*vc^2*mc^2+16*vc^2*mm^2-9*pm^2, Em+Er-Ec, pc-pm}, {4*mm*c+3*pm, 9*vc^2*mc^2+16*vc^2*mm^2-9*pm^2, Em+Er-Ec, vm-4/5*c}, {4*mm*c+3*pm, 9*vc^2*mc^2+16*vc^2*mm^2-9*pm^2, pc-pm, vm-4/5*c}, {4*mm*c+3*pm, Em+Er-Ec, pc-pm, vm-4/5*c}, {-mc^2*c^2-pm^2*c^2+Ec^2, 9*vc^2*mc^2+16*vc^2*mm^2-9*pm^2, Em+Er-Ec, pc-pm}, {-mc^2*c^2-pm^2*c^2+Ec^2, 9*vc^2*mc^2+16*vc^2*mm^2-9*pm^2, Em+Er-Ec, vm-4/5*c}, {-mc^2*c^2-pm^2*c^2+Ec^2, 9*vc^2*mc^2+16*vc^2*mm^2-9*pm^2, pc-pm, vm-4/5*c}, {-mc^2*c^2-pm^2*c^2+Ec^2, Em+Er-Ec, pc-pm, vm-4/5*c}, {9*vc^2*mc^2+16*vc^2*mm^2-9*pm^2, Em+Er-Ec, pc-pm, vm-4/5*c}, {4*mm*c-3*pm}, {-mc^2*c^2-pm^2*c^2+Ec^2}, {9*vc^2*mc^2+16*vc^2*mm^2-9*pm^2}, {Em+Er-Ec}, {pc-pm}, {vm-4/5*c}, {4*mm*c-3*pm, -mc^2*c^2-pm^2*c^2+Ec^2}, {4*mm*c-3*pm, 9*vc^2*mc^2+16*vc^2*mm^2-9*pm^2}, {4*mm*c-3*pm, Em+Er-Ec}, {4*mm*c-3*pm, pc-pm}, {4*mm*c-3*pm, vm-4/5*c}, {-mc^2*c^2-pm^2*c^2+Ec^2, 9*vc^2*mc^2+16*vc^2*mm^2-9*pm^2}, {-mc^2*c^2-pm^2*c^2+Ec^2, Em+Er-Ec}, {-mc^2*c^2-pm^2*c^2+Ec^2, pc-pm}, {-mc^2*c^2-pm^2*c^2+Ec^2, vm-4/5*c}, {9*vc^2*mc^2+16*vc^2*mm^2-9*pm^2, Em+Er-Ec}, {9*vc^2*mc^2+16*vc^2*mm^2-9*pm^2, pc-pm}, {9*vc^2*mc^2+16*vc^2*mm^2-9*pm^2, vm-4/5*c}, {Em+Er-Ec, pc-pm}, {Em+Er-Ec, vm-4/5*c}, {pc-pm, vm-4/5*c}, {4*mm*c-3*pm, -mc^2*c^2-pm^2*c^2+Ec^2, 9*vc^2*mc^2+16*vc^2*mm^2-9*pm^2}, {4*mm*c-3*pm, -mc^2*c^2-pm^2*c^2+Ec^2, Em+Er-Ec}, {4*mm*c-3*pm, -mc^2*c^2-pm^2*c^2+Ec^2, pc-pm}, {4*mm*c-3*pm, -mc^2*c^2-pm^2*c^2+Ec^2, vm-4/5*c}, {4*mm*c-3*pm, 9*vc^2*mc^2+16*vc^2*mm^2-9*pm^2, Em+Er-Ec}, {4*mm*c-3*pm, 9*vc^2*mc^2+16*vc^2*mm^2-9*pm^2, pc-pm}, {4*mm*c-3*pm, 9*vc^2*mc^2+16*vc^2*mm^2-9*pm^2, vm-4/5*c}, {4*mm*c-3*pm, Em+Er-Ec, pc-pm}, {4*mm*c-3*pm, Em+Er-Ec, vm-4/5*c}, {4*mm*c-3*pm, pc-pm, vm-4/5*c}, {-mc^2*c^2-pm^2*c^2+Ec^2, 9*vc^2*mc^2+16*vc^2*mm^2-9*pm^2, Em+Er-Ec}, {-mc^2*c^2-pm^2*c^2+Ec^2, 9*vc^2*mc^2+16*vc^2*mm^2-9*pm^2, pc-pm}, {-mc^2*c^2-pm^2*c^2+Ec^2, 9*vc^2*mc^2+16*vc^2*mm^2-9*pm^2, vm-4/5*c}, {-mc^2*c^2-pm^2*c^2+Ec^2, Em+Er-Ec, pc-pm}, {-mc^2*c^2-pm^2*c^2+Ec^2, Em+Er-Ec, vm-4/5*c}, {-mc^2*c^2-pm^2*c^2+Ec^2, pc-pm, vm-4/5*c}, {9*vc^2*mc^2+16*vc^2*mm^2-9*pm^2, Em+Er-Ec, pc-pm}, {9*vc^2*mc^2+16*vc^2*mm^2-9*pm^2, Em+Er-Ec, vm-4/5*c}, {9*vc^2*mc^2+16*vc^2*mm^2-9*pm^2, pc-pm, vm-4/5*c}, {Em+Er-Ec, pc-pm, vm-4/5*c}, {4*mm*c-3*pm, -mc^2*c^2-pm^2*c^2+Ec^2, 9*vc^2*mc^2+16*vc^2*mm^2-9*pm^2, Em+Er-Ec}, {4*mm*c-3*pm, -mc^2*c^2-pm^2*c^2+Ec^2, 9*vc^2*mc^2+16*vc^2*mm^2-9*pm^2, pc-pm}, {4*mm*c-3*pm, -mc^2*c^2-pm^2*c^2+Ec^2, 9*vc^2*mc^2+16*vc^2*mm^2-9*pm^2, vm-4/5*c}, {4*mm*c-3*pm, -mc^2*c^2-pm^2*c^2+Ec^2, Em+Er-Ec, pc-pm}, {4*mm*c-3*pm, -mc^2*c^2-pm^2*c^2+Ec^2, Em+Er-Ec, vm-4/5*c}, {4*mm*c-3*pm, -mc^2*c^2-pm^2*c^2+Ec^2, pc-pm, vm-4/5*c}, {4*mm*c-3*pm, 9*vc^2*mc^2+16*vc^2*mm^2-9*pm^2, Em+Er-Ec, pc-pm}, {4*mm*c-3*pm, 9*vc^2*mc^2+16*vc^2*mm^2-9*pm^2, Em+Er-Ec, vm-4/5*c}, {4*mm*c-3*pm, 9*vc^2*mc^2+16*vc^2*mm^2-9*pm^2, pc-pm, vm-4/5*c}, {4*mm*c-3*pm, Em+Er-Ec, pc-pm, vm-4/5*c}, {-mc^2*c^2-pm^2*c^2+Ec^2, 9*vc^2*mc^2+16*vc^2*mm^2-9*pm^2, Em+Er-Ec, pc-pm}, {-mc^2*c^2-pm^2*c^2+Ec^2, 9*vc^2*mc^2+16*vc^2*mm^2-9*pm^2, Em+Er-Ec, vm-4/5*c}, {-mc^2*c^2-pm^2*c^2+Ec^2, 9*vc^2*mc^2+16*vc^2*mm^2-9*pm^2, pc-pm, vm-4/5*c}, {-mc^2*c^2-pm^2*c^2+Ec^2, Em+Er-Ec, pc-pm, vm-4/5*c}, {9*vc^2*mc^2+16*vc^2*mm^2-9*pm^2, Em+Er-Ec, pc-pm, vm-4/5*c}};

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
f = openOut "results/inelastic_collision/abduction/noiseless/3_axiom(s)_removed/combo_2_3_8/reasoning/reasoning_output.txt";
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

print("Reasoning complete. Output written to results/inelastic_collision/abduction/noiseless/3_axiom(s)_removed/combo_2_3_8/reasoning/reasoning_output.txt");
