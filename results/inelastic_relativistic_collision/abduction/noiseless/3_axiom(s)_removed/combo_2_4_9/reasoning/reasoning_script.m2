-- AI-Noether: Reasoning Template (Noiseless)
-- Tests if candidate axiom sets, when added to remaining axioms, prove targets

needsPackage("PrimaryDecomposition", Reload => true)

-- Ring definition
R = QQ[mr, vm, vc, pc, Em, Er, Ec, mc, mm, pm, c, MonomialOrder => Lex];

-- Input data
remainingAxioms = toList([pm^2*(c^2 - vm^2) - mm^2*vm^2*c^2, Er - mr*c^2, 2*Em*Er - Ec^2 + Em^2 + Er^2, pc - pm, vm - 4/5*c, mr - mm]);
qList = toList([16*mm^2*c^4 - 9*pm^2*c^2]);
k = #qList;

-- Per-target variable partitions
measuredPerTarget = {{mm, pm, c}};
nonMeasuredPerTarget = {{mr, vm, vc, pc, Em, Er, Ec, mc}};

-- Candidate axiom sets to test (list of lists)
candidateSets = {{}, {c}, {Er}, {Em-Ec}, {pc-pm}, {vm}, {mr-mm}, {c, Er}, {c, Em-Ec}, {c, pc-pm}, {c, vm}, {c, mr-mm}, {Er, Em-Ec}, {Er, pc-pm}, {Er, vm}, {Er, mr-mm}, {Em-Ec, pc-pm}, {Em-Ec, vm}, {Em-Ec, mr-mm}, {pc-pm, vm}, {pc-pm, mr-mm}, {vm, mr-mm}, {c, Er, Em-Ec}, {c, Er, pc-pm}, {c, Er, vm}, {c, Er, mr-mm}, {c, Em-Ec, pc-pm}, {c, Em-Ec, vm}, {c, Em-Ec, mr-mm}, {c, pc-pm, vm}, {c, pc-pm, mr-mm}, {c, vm, mr-mm}, {Er, Em-Ec, pc-pm}, {Er, Em-Ec, vm}, {Er, Em-Ec, mr-mm}, {Er, pc-pm, vm}, {Er, pc-pm, mr-mm}, {Er, vm, mr-mm}, {Em-Ec, pc-pm, vm}, {Em-Ec, pc-pm, mr-mm}, {Em-Ec, vm, mr-mm}, {pc-pm, vm, mr-mm}, {c, Er, Em-Ec, pc-pm}, {c, Er, Em-Ec, vm}, {c, Er, Em-Ec, mr-mm}, {c, Er, pc-pm, vm}, {c, Er, pc-pm, mr-mm}, {c, Er, vm, mr-mm}, {c, Em-Ec, pc-pm, vm}, {c, Em-Ec, pc-pm, mr-mm}, {c, Em-Ec, vm, mr-mm}, {c, pc-pm, vm, mr-mm}, {Er, Em-Ec, pc-pm, vm}, {Er, Em-Ec, pc-pm, mr-mm}, {Er, Em-Ec, vm, mr-mm}, {Er, pc-pm, vm, mr-mm}, {Em-Ec, pc-pm, vm, mr-mm}, {c}, {Er}, {Em+Ec}, {pc-pm}, {vm}, {mr-mm}, {c, Er}, {c, Em+Ec}, {c, pc-pm}, {c, vm}, {c, mr-mm}, {Er, Em+Ec}, {Er, pc-pm}, {Er, vm}, {Er, mr-mm}, {Em+Ec, pc-pm}, {Em+Ec, vm}, {Em+Ec, mr-mm}, {pc-pm, vm}, {pc-pm, mr-mm}, {vm, mr-mm}, {c, Er, Em+Ec}, {c, Er, pc-pm}, {c, Er, vm}, {c, Er, mr-mm}, {c, Em+Ec, pc-pm}, {c, Em+Ec, vm}, {c, Em+Ec, mr-mm}, {c, pc-pm, vm}, {c, pc-pm, mr-mm}, {c, vm, mr-mm}, {Er, Em+Ec, pc-pm}, {Er, Em+Ec, vm}, {Er, Em+Ec, mr-mm}, {Er, pc-pm, vm}, {Er, pc-pm, mr-mm}, {Er, vm, mr-mm}, {Em+Ec, pc-pm, vm}, {Em+Ec, pc-pm, mr-mm}, {Em+Ec, vm, mr-mm}, {pc-pm, vm, mr-mm}, {c, Er, Em+Ec, pc-pm}, {c, Er, Em+Ec, vm}, {c, Er, Em+Ec, mr-mm}, {c, Er, pc-pm, vm}, {c, Er, pc-pm, mr-mm}, {c, Er, vm, mr-mm}, {c, Em+Ec, pc-pm, vm}, {c, Em+Ec, pc-pm, mr-mm}, {c, Em+Ec, vm, mr-mm}, {c, pc-pm, vm, mr-mm}, {Er, Em+Ec, pc-pm, vm}, {Er, Em+Ec, pc-pm, mr-mm}, {Er, Em+Ec, vm, mr-mm}, {Er, pc-pm, vm, mr-mm}, {Em+Ec, pc-pm, vm, mr-mm}, {Em+Er-Ec}, {pc-pm}, {5*vm-4*c}, {mr-mm}, {3*pm*c+4*Em-4*Ec}, {4*mm*c-3*pc}, {16*Er*mm-9*pm^2}, {Em+Er-Ec, pc-pm}, {Em+Er-Ec, 5*vm-4*c}, {Em+Er-Ec, mr-mm}, {Em+Er-Ec, 3*pm*c+4*Em-4*Ec}, {Em+Er-Ec, 4*mm*c-3*pc}, {Em+Er-Ec, 16*Er*mm-9*pm^2}, {pc-pm, 5*vm-4*c}, {pc-pm, mr-mm}, {pc-pm, 3*pm*c+4*Em-4*Ec}, {pc-pm, 4*mm*c-3*pc}, {pc-pm, 16*Er*mm-9*pm^2}, {5*vm-4*c, mr-mm}, {5*vm-4*c, 3*pm*c+4*Em-4*Ec}, {5*vm-4*c, 4*mm*c-3*pc}, {5*vm-4*c, 16*Er*mm-9*pm^2}, {mr-mm, 3*pm*c+4*Em-4*Ec}, {mr-mm, 4*mm*c-3*pc}, {mr-mm, 16*Er*mm-9*pm^2}, {3*pm*c+4*Em-4*Ec, 4*mm*c-3*pc}, {3*pm*c+4*Em-4*Ec, 16*Er*mm-9*pm^2}, {4*mm*c-3*pc, 16*Er*mm-9*pm^2}, {Em+Er-Ec, pc-pm, 5*vm-4*c}, {Em+Er-Ec, pc-pm, mr-mm}, {Em+Er-Ec, pc-pm, 3*pm*c+4*Em-4*Ec}, {Em+Er-Ec, pc-pm, 4*mm*c-3*pc}, {Em+Er-Ec, pc-pm, 16*Er*mm-9*pm^2}, {Em+Er-Ec, 5*vm-4*c, mr-mm}, {Em+Er-Ec, 5*vm-4*c, 3*pm*c+4*Em-4*Ec}, {Em+Er-Ec, 5*vm-4*c, 4*mm*c-3*pc}, {Em+Er-Ec, 5*vm-4*c, 16*Er*mm-9*pm^2}, {Em+Er-Ec, mr-mm, 3*pm*c+4*Em-4*Ec}, {Em+Er-Ec, mr-mm, 4*mm*c-3*pc}, {Em+Er-Ec, mr-mm, 16*Er*mm-9*pm^2}, {Em+Er-Ec, 3*pm*c+4*Em-4*Ec, 4*mm*c-3*pc}, {Em+Er-Ec, 3*pm*c+4*Em-4*Ec, 16*Er*mm-9*pm^2}, {Em+Er-Ec, 4*mm*c-3*pc, 16*Er*mm-9*pm^2}, {pc-pm, 5*vm-4*c, mr-mm}, {pc-pm, 5*vm-4*c, 3*pm*c+4*Em-4*Ec}, {pc-pm, 5*vm-4*c, 4*mm*c-3*pc}, {pc-pm, 5*vm-4*c, 16*Er*mm-9*pm^2}, {pc-pm, mr-mm, 3*pm*c+4*Em-4*Ec}, {pc-pm, mr-mm, 4*mm*c-3*pc}, {pc-pm, mr-mm, 16*Er*mm-9*pm^2}, {pc-pm, 3*pm*c+4*Em-4*Ec, 4*mm*c-3*pc}, {pc-pm, 3*pm*c+4*Em-4*Ec, 16*Er*mm-9*pm^2}, {pc-pm, 4*mm*c-3*pc, 16*Er*mm-9*pm^2}, {5*vm-4*c, mr-mm, 3*pm*c+4*Em-4*Ec}, {5*vm-4*c, mr-mm, 4*mm*c-3*pc}, {5*vm-4*c, mr-mm, 16*Er*mm-9*pm^2}, {5*vm-4*c, 3*pm*c+4*Em-4*Ec, 4*mm*c-3*pc}, {5*vm-4*c, 3*pm*c+4*Em-4*Ec, 16*Er*mm-9*pm^2}, {5*vm-4*c, 4*mm*c-3*pc, 16*Er*mm-9*pm^2}, {mr-mm, 3*pm*c+4*Em-4*Ec, 4*mm*c-3*pc}, {mr-mm, 3*pm*c+4*Em-4*Ec, 16*Er*mm-9*pm^2}, {mr-mm, 4*mm*c-3*pc, 16*Er*mm-9*pm^2}, {3*pm*c+4*Em-4*Ec, 4*mm*c-3*pc, 16*Er*mm-9*pm^2}, {Em+Er-Ec, pc-pm, 5*vm-4*c, mr-mm}, {Em+Er-Ec, pc-pm, 5*vm-4*c, 3*pm*c+4*Em-4*Ec}, {Em+Er-Ec, pc-pm, 5*vm-4*c, 4*mm*c-3*pc}, {Em+Er-Ec, pc-pm, 5*vm-4*c, 16*Er*mm-9*pm^2}, {Em+Er-Ec, pc-pm, mr-mm, 3*pm*c+4*Em-4*Ec}, {Em+Er-Ec, pc-pm, mr-mm, 4*mm*c-3*pc}, {Em+Er-Ec, pc-pm, mr-mm, 16*Er*mm-9*pm^2}, {Em+Er-Ec, pc-pm, 3*pm*c+4*Em-4*Ec, 4*mm*c-3*pc}, {Em+Er-Ec, pc-pm, 3*pm*c+4*Em-4*Ec, 16*Er*mm-9*pm^2}, {Em+Er-Ec, pc-pm, 4*mm*c-3*pc, 16*Er*mm-9*pm^2}, {Em+Er-Ec, 5*vm-4*c, mr-mm, 3*pm*c+4*Em-4*Ec}, {Em+Er-Ec, 5*vm-4*c, mr-mm, 4*mm*c-3*pc}, {Em+Er-Ec, 5*vm-4*c, mr-mm, 16*Er*mm-9*pm^2}, {Em+Er-Ec, 5*vm-4*c, 3*pm*c+4*Em-4*Ec, 4*mm*c-3*pc}, {Em+Er-Ec, 5*vm-4*c, 3*pm*c+4*Em-4*Ec, 16*Er*mm-9*pm^2}, {Em+Er-Ec, 5*vm-4*c, 4*mm*c-3*pc, 16*Er*mm-9*pm^2}, {Em+Er-Ec, mr-mm, 3*pm*c+4*Em-4*Ec, 4*mm*c-3*pc}, {Em+Er-Ec, mr-mm, 3*pm*c+4*Em-4*Ec, 16*Er*mm-9*pm^2}, {Em+Er-Ec, mr-mm, 4*mm*c-3*pc, 16*Er*mm-9*pm^2}, {Em+Er-Ec, 3*pm*c+4*Em-4*Ec, 4*mm*c-3*pc, 16*Er*mm-9*pm^2}, {pc-pm, 5*vm-4*c, mr-mm, 3*pm*c+4*Em-4*Ec}, {pc-pm, 5*vm-4*c, mr-mm, 4*mm*c-3*pc}, {pc-pm, 5*vm-4*c, mr-mm, 16*Er*mm-9*pm^2}, {pc-pm, 5*vm-4*c, 3*pm*c+4*Em-4*Ec, 4*mm*c-3*pc}, {pc-pm, 5*vm-4*c, 3*pm*c+4*Em-4*Ec, 16*Er*mm-9*pm^2}, {pc-pm, 5*vm-4*c, 4*mm*c-3*pc, 16*Er*mm-9*pm^2}, {pc-pm, mr-mm, 3*pm*c+4*Em-4*Ec, 4*mm*c-3*pc}, {pc-pm, mr-mm, 3*pm*c+4*Em-4*Ec, 16*Er*mm-9*pm^2}, {pc-pm, mr-mm, 4*mm*c-3*pc, 16*Er*mm-9*pm^2}, {pc-pm, 3*pm*c+4*Em-4*Ec, 4*mm*c-3*pc, 16*Er*mm-9*pm^2}, {5*vm-4*c, mr-mm, 3*pm*c+4*Em-4*Ec, 4*mm*c-3*pc}, {5*vm-4*c, mr-mm, 3*pm*c+4*Em-4*Ec, 16*Er*mm-9*pm^2}, {5*vm-4*c, mr-mm, 4*mm*c-3*pc, 16*Er*mm-9*pm^2}, {5*vm-4*c, 3*pm*c+4*Em-4*Ec, 4*mm*c-3*pc, 16*Er*mm-9*pm^2}, {mr-mm, 3*pm*c+4*Em-4*Ec, 4*mm*c-3*pc, 16*Er*mm-9*pm^2}, {Em+Er+Ec}, {pc-pm}, {5*vm-4*c}, {mr-mm}, {3*pm*c+4*Em+4*Ec}, {4*mm*c-3*pc}, {16*Er*mm-9*pm^2}, {Em+Er+Ec, pc-pm}, {Em+Er+Ec, 5*vm-4*c}, {Em+Er+Ec, mr-mm}, {Em+Er+Ec, 3*pm*c+4*Em+4*Ec}, {Em+Er+Ec, 4*mm*c-3*pc}, {Em+Er+Ec, 16*Er*mm-9*pm^2}, {pc-pm, 5*vm-4*c}, {pc-pm, mr-mm}, {pc-pm, 3*pm*c+4*Em+4*Ec}, {pc-pm, 4*mm*c-3*pc}, {pc-pm, 16*Er*mm-9*pm^2}, {5*vm-4*c, mr-mm}, {5*vm-4*c, 3*pm*c+4*Em+4*Ec}, {5*vm-4*c, 4*mm*c-3*pc}, {5*vm-4*c, 16*Er*mm-9*pm^2}, {mr-mm, 3*pm*c+4*Em+4*Ec}, {mr-mm, 4*mm*c-3*pc}, {mr-mm, 16*Er*mm-9*pm^2}, {3*pm*c+4*Em+4*Ec, 4*mm*c-3*pc}, {3*pm*c+4*Em+4*Ec, 16*Er*mm-9*pm^2}, {4*mm*c-3*pc, 16*Er*mm-9*pm^2}, {Em+Er+Ec, pc-pm, 5*vm-4*c}, {Em+Er+Ec, pc-pm, mr-mm}, {Em+Er+Ec, pc-pm, 3*pm*c+4*Em+4*Ec}, {Em+Er+Ec, pc-pm, 4*mm*c-3*pc}, {Em+Er+Ec, pc-pm, 16*Er*mm-9*pm^2}, {Em+Er+Ec, 5*vm-4*c, mr-mm}, {Em+Er+Ec, 5*vm-4*c, 3*pm*c+4*Em+4*Ec}, {Em+Er+Ec, 5*vm-4*c, 4*mm*c-3*pc}, {Em+Er+Ec, 5*vm-4*c, 16*Er*mm-9*pm^2}, {Em+Er+Ec, mr-mm, 3*pm*c+4*Em+4*Ec}, {Em+Er+Ec, mr-mm, 4*mm*c-3*pc}, {Em+Er+Ec, mr-mm, 16*Er*mm-9*pm^2}, {Em+Er+Ec, 3*pm*c+4*Em+4*Ec, 4*mm*c-3*pc}, {Em+Er+Ec, 3*pm*c+4*Em+4*Ec, 16*Er*mm-9*pm^2}, {Em+Er+Ec, 4*mm*c-3*pc, 16*Er*mm-9*pm^2}, {pc-pm, 5*vm-4*c, mr-mm}, {pc-pm, 5*vm-4*c, 3*pm*c+4*Em+4*Ec}, {pc-pm, 5*vm-4*c, 4*mm*c-3*pc}, {pc-pm, 5*vm-4*c, 16*Er*mm-9*pm^2}, {pc-pm, mr-mm, 3*pm*c+4*Em+4*Ec}, {pc-pm, mr-mm, 4*mm*c-3*pc}, {pc-pm, mr-mm, 16*Er*mm-9*pm^2}, {pc-pm, 3*pm*c+4*Em+4*Ec, 4*mm*c-3*pc}, {pc-pm, 3*pm*c+4*Em+4*Ec, 16*Er*mm-9*pm^2}, {pc-pm, 4*mm*c-3*pc, 16*Er*mm-9*pm^2}, {5*vm-4*c, mr-mm, 3*pm*c+4*Em+4*Ec}, {5*vm-4*c, mr-mm, 4*mm*c-3*pc}, {5*vm-4*c, mr-mm, 16*Er*mm-9*pm^2}, {5*vm-4*c, 3*pm*c+4*Em+4*Ec, 4*mm*c-3*pc}, {5*vm-4*c, 3*pm*c+4*Em+4*Ec, 16*Er*mm-9*pm^2}, {5*vm-4*c, 4*mm*c-3*pc, 16*Er*mm-9*pm^2}, {mr-mm, 3*pm*c+4*Em+4*Ec, 4*mm*c-3*pc}, {mr-mm, 3*pm*c+4*Em+4*Ec, 16*Er*mm-9*pm^2}, {mr-mm, 4*mm*c-3*pc, 16*Er*mm-9*pm^2}, {3*pm*c+4*Em+4*Ec, 4*mm*c-3*pc, 16*Er*mm-9*pm^2}, {Em+Er+Ec, pc-pm, 5*vm-4*c, mr-mm}, {Em+Er+Ec, pc-pm, 5*vm-4*c, 3*pm*c+4*Em+4*Ec}, {Em+Er+Ec, pc-pm, 5*vm-4*c, 4*mm*c-3*pc}, {Em+Er+Ec, pc-pm, 5*vm-4*c, 16*Er*mm-9*pm^2}, {Em+Er+Ec, pc-pm, mr-mm, 3*pm*c+4*Em+4*Ec}, {Em+Er+Ec, pc-pm, mr-mm, 4*mm*c-3*pc}, {Em+Er+Ec, pc-pm, mr-mm, 16*Er*mm-9*pm^2}, {Em+Er+Ec, pc-pm, 3*pm*c+4*Em+4*Ec, 4*mm*c-3*pc}, {Em+Er+Ec, pc-pm, 3*pm*c+4*Em+4*Ec, 16*Er*mm-9*pm^2}, {Em+Er+Ec, pc-pm, 4*mm*c-3*pc, 16*Er*mm-9*pm^2}, {Em+Er+Ec, 5*vm-4*c, mr-mm, 3*pm*c+4*Em+4*Ec}, {Em+Er+Ec, 5*vm-4*c, mr-mm, 4*mm*c-3*pc}, {Em+Er+Ec, 5*vm-4*c, mr-mm, 16*Er*mm-9*pm^2}, {Em+Er+Ec, 5*vm-4*c, 3*pm*c+4*Em+4*Ec, 4*mm*c-3*pc}, {Em+Er+Ec, 5*vm-4*c, 3*pm*c+4*Em+4*Ec, 16*Er*mm-9*pm^2}, {Em+Er+Ec, 5*vm-4*c, 4*mm*c-3*pc, 16*Er*mm-9*pm^2}, {Em+Er+Ec, mr-mm, 3*pm*c+4*Em+4*Ec, 4*mm*c-3*pc}, {Em+Er+Ec, mr-mm, 3*pm*c+4*Em+4*Ec, 16*Er*mm-9*pm^2}, {Em+Er+Ec, mr-mm, 4*mm*c-3*pc, 16*Er*mm-9*pm^2}, {Em+Er+Ec, 3*pm*c+4*Em+4*Ec, 4*mm*c-3*pc, 16*Er*mm-9*pm^2}, {pc-pm, 5*vm-4*c, mr-mm, 3*pm*c+4*Em+4*Ec}, {pc-pm, 5*vm-4*c, mr-mm, 4*mm*c-3*pc}, {pc-pm, 5*vm-4*c, mr-mm, 16*Er*mm-9*pm^2}, {pc-pm, 5*vm-4*c, 3*pm*c+4*Em+4*Ec, 4*mm*c-3*pc}, {pc-pm, 5*vm-4*c, 3*pm*c+4*Em+4*Ec, 16*Er*mm-9*pm^2}, {pc-pm, 5*vm-4*c, 4*mm*c-3*pc, 16*Er*mm-9*pm^2}, {pc-pm, mr-mm, 3*pm*c+4*Em+4*Ec, 4*mm*c-3*pc}, {pc-pm, mr-mm, 3*pm*c+4*Em+4*Ec, 16*Er*mm-9*pm^2}, {pc-pm, mr-mm, 4*mm*c-3*pc, 16*Er*mm-9*pm^2}, {pc-pm, 3*pm*c+4*Em+4*Ec, 4*mm*c-3*pc, 16*Er*mm-9*pm^2}, {5*vm-4*c, mr-mm, 3*pm*c+4*Em+4*Ec, 4*mm*c-3*pc}, {5*vm-4*c, mr-mm, 3*pm*c+4*Em+4*Ec, 16*Er*mm-9*pm^2}, {5*vm-4*c, mr-mm, 4*mm*c-3*pc, 16*Er*mm-9*pm^2}, {5*vm-4*c, 3*pm*c+4*Em+4*Ec, 4*mm*c-3*pc, 16*Er*mm-9*pm^2}, {mr-mm, 3*pm*c+4*Em+4*Ec, 4*mm*c-3*pc, 16*Er*mm-9*pm^2}, {Em+Er-Ec}, {pc-pm}, {5*vm-4*c}, {mr-mm}, {3*pm*c-4*Em+4*Ec}, {4*mm*c+3*pc}, {16*Er*mm-9*pm^2}, {Em+Er-Ec, pc-pm}, {Em+Er-Ec, 5*vm-4*c}, {Em+Er-Ec, mr-mm}, {Em+Er-Ec, 3*pm*c-4*Em+4*Ec}, {Em+Er-Ec, 4*mm*c+3*pc}, {Em+Er-Ec, 16*Er*mm-9*pm^2}, {pc-pm, 5*vm-4*c}, {pc-pm, mr-mm}, {pc-pm, 3*pm*c-4*Em+4*Ec}, {pc-pm, 4*mm*c+3*pc}, {pc-pm, 16*Er*mm-9*pm^2}, {5*vm-4*c, mr-mm}, {5*vm-4*c, 3*pm*c-4*Em+4*Ec}, {5*vm-4*c, 4*mm*c+3*pc}, {5*vm-4*c, 16*Er*mm-9*pm^2}, {mr-mm, 3*pm*c-4*Em+4*Ec}, {mr-mm, 4*mm*c+3*pc}, {mr-mm, 16*Er*mm-9*pm^2}, {3*pm*c-4*Em+4*Ec, 4*mm*c+3*pc}, {3*pm*c-4*Em+4*Ec, 16*Er*mm-9*pm^2}, {4*mm*c+3*pc, 16*Er*mm-9*pm^2}, {Em+Er-Ec, pc-pm, 5*vm-4*c}, {Em+Er-Ec, pc-pm, mr-mm}, {Em+Er-Ec, pc-pm, 3*pm*c-4*Em+4*Ec}, {Em+Er-Ec, pc-pm, 4*mm*c+3*pc}, {Em+Er-Ec, pc-pm, 16*Er*mm-9*pm^2}, {Em+Er-Ec, 5*vm-4*c, mr-mm}, {Em+Er-Ec, 5*vm-4*c, 3*pm*c-4*Em+4*Ec}, {Em+Er-Ec, 5*vm-4*c, 4*mm*c+3*pc}, {Em+Er-Ec, 5*vm-4*c, 16*Er*mm-9*pm^2}, {Em+Er-Ec, mr-mm, 3*pm*c-4*Em+4*Ec}, {Em+Er-Ec, mr-mm, 4*mm*c+3*pc}, {Em+Er-Ec, mr-mm, 16*Er*mm-9*pm^2}, {Em+Er-Ec, 3*pm*c-4*Em+4*Ec, 4*mm*c+3*pc}, {Em+Er-Ec, 3*pm*c-4*Em+4*Ec, 16*Er*mm-9*pm^2}, {Em+Er-Ec, 4*mm*c+3*pc, 16*Er*mm-9*pm^2}, {pc-pm, 5*vm-4*c, mr-mm}, {pc-pm, 5*vm-4*c, 3*pm*c-4*Em+4*Ec}, {pc-pm, 5*vm-4*c, 4*mm*c+3*pc}, {pc-pm, 5*vm-4*c, 16*Er*mm-9*pm^2}, {pc-pm, mr-mm, 3*pm*c-4*Em+4*Ec}, {pc-pm, mr-mm, 4*mm*c+3*pc}, {pc-pm, mr-mm, 16*Er*mm-9*pm^2}, {pc-pm, 3*pm*c-4*Em+4*Ec, 4*mm*c+3*pc}, {pc-pm, 3*pm*c-4*Em+4*Ec, 16*Er*mm-9*pm^2}, {pc-pm, 4*mm*c+3*pc, 16*Er*mm-9*pm^2}, {5*vm-4*c, mr-mm, 3*pm*c-4*Em+4*Ec}, {5*vm-4*c, mr-mm, 4*mm*c+3*pc}, {5*vm-4*c, mr-mm, 16*Er*mm-9*pm^2}, {5*vm-4*c, 3*pm*c-4*Em+4*Ec, 4*mm*c+3*pc}, {5*vm-4*c, 3*pm*c-4*Em+4*Ec, 16*Er*mm-9*pm^2}, {5*vm-4*c, 4*mm*c+3*pc, 16*Er*mm-9*pm^2}, {mr-mm, 3*pm*c-4*Em+4*Ec, 4*mm*c+3*pc}, {mr-mm, 3*pm*c-4*Em+4*Ec, 16*Er*mm-9*pm^2}, {mr-mm, 4*mm*c+3*pc, 16*Er*mm-9*pm^2}, {3*pm*c-4*Em+4*Ec, 4*mm*c+3*pc, 16*Er*mm-9*pm^2}, {Em+Er-Ec, pc-pm, 5*vm-4*c, mr-mm}, {Em+Er-Ec, pc-pm, 5*vm-4*c, 3*pm*c-4*Em+4*Ec}, {Em+Er-Ec, pc-pm, 5*vm-4*c, 4*mm*c+3*pc}, {Em+Er-Ec, pc-pm, 5*vm-4*c, 16*Er*mm-9*pm^2}, {Em+Er-Ec, pc-pm, mr-mm, 3*pm*c-4*Em+4*Ec}, {Em+Er-Ec, pc-pm, mr-mm, 4*mm*c+3*pc}, {Em+Er-Ec, pc-pm, mr-mm, 16*Er*mm-9*pm^2}, {Em+Er-Ec, pc-pm, 3*pm*c-4*Em+4*Ec, 4*mm*c+3*pc}, {Em+Er-Ec, pc-pm, 3*pm*c-4*Em+4*Ec, 16*Er*mm-9*pm^2}, {Em+Er-Ec, pc-pm, 4*mm*c+3*pc, 16*Er*mm-9*pm^2}, {Em+Er-Ec, 5*vm-4*c, mr-mm, 3*pm*c-4*Em+4*Ec}, {Em+Er-Ec, 5*vm-4*c, mr-mm, 4*mm*c+3*pc}, {Em+Er-Ec, 5*vm-4*c, mr-mm, 16*Er*mm-9*pm^2}, {Em+Er-Ec, 5*vm-4*c, 3*pm*c-4*Em+4*Ec, 4*mm*c+3*pc}, {Em+Er-Ec, 5*vm-4*c, 3*pm*c-4*Em+4*Ec, 16*Er*mm-9*pm^2}, {Em+Er-Ec, 5*vm-4*c, 4*mm*c+3*pc, 16*Er*mm-9*pm^2}, {Em+Er-Ec, mr-mm, 3*pm*c-4*Em+4*Ec, 4*mm*c+3*pc}, {Em+Er-Ec, mr-mm, 3*pm*c-4*Em+4*Ec, 16*Er*mm-9*pm^2}, {Em+Er-Ec, mr-mm, 4*mm*c+3*pc, 16*Er*mm-9*pm^2}, {Em+Er-Ec, 3*pm*c-4*Em+4*Ec, 4*mm*c+3*pc, 16*Er*mm-9*pm^2}, {pc-pm, 5*vm-4*c, mr-mm, 3*pm*c-4*Em+4*Ec}, {pc-pm, 5*vm-4*c, mr-mm, 4*mm*c+3*pc}, {pc-pm, 5*vm-4*c, mr-mm, 16*Er*mm-9*pm^2}, {pc-pm, 5*vm-4*c, 3*pm*c-4*Em+4*Ec, 4*mm*c+3*pc}, {pc-pm, 5*vm-4*c, 3*pm*c-4*Em+4*Ec, 16*Er*mm-9*pm^2}, {pc-pm, 5*vm-4*c, 4*mm*c+3*pc, 16*Er*mm-9*pm^2}, {pc-pm, mr-mm, 3*pm*c-4*Em+4*Ec, 4*mm*c+3*pc}, {pc-pm, mr-mm, 3*pm*c-4*Em+4*Ec, 16*Er*mm-9*pm^2}, {pc-pm, mr-mm, 4*mm*c+3*pc, 16*Er*mm-9*pm^2}, {pc-pm, 3*pm*c-4*Em+4*Ec, 4*mm*c+3*pc, 16*Er*mm-9*pm^2}, {5*vm-4*c, mr-mm, 3*pm*c-4*Em+4*Ec, 4*mm*c+3*pc}, {5*vm-4*c, mr-mm, 3*pm*c-4*Em+4*Ec, 16*Er*mm-9*pm^2}, {5*vm-4*c, mr-mm, 4*mm*c+3*pc, 16*Er*mm-9*pm^2}, {5*vm-4*c, 3*pm*c-4*Em+4*Ec, 4*mm*c+3*pc, 16*Er*mm-9*pm^2}, {mr-mm, 3*pm*c-4*Em+4*Ec, 4*mm*c+3*pc, 16*Er*mm-9*pm^2}, {Em+Er+Ec}, {pc-pm}, {5*vm-4*c}, {mr-mm}, {3*pm*c-4*Em-4*Ec}, {4*mm*c+3*pc}, {16*Er*mm-9*pm^2}, {Em+Er+Ec, pc-pm}, {Em+Er+Ec, 5*vm-4*c}, {Em+Er+Ec, mr-mm}, {Em+Er+Ec, 3*pm*c-4*Em-4*Ec}, {Em+Er+Ec, 4*mm*c+3*pc}, {Em+Er+Ec, 16*Er*mm-9*pm^2}, {pc-pm, 5*vm-4*c}, {pc-pm, mr-mm}, {pc-pm, 3*pm*c-4*Em-4*Ec}, {pc-pm, 4*mm*c+3*pc}, {pc-pm, 16*Er*mm-9*pm^2}, {5*vm-4*c, mr-mm}, {5*vm-4*c, 3*pm*c-4*Em-4*Ec}, {5*vm-4*c, 4*mm*c+3*pc}, {5*vm-4*c, 16*Er*mm-9*pm^2}, {mr-mm, 3*pm*c-4*Em-4*Ec}, {mr-mm, 4*mm*c+3*pc}, {mr-mm, 16*Er*mm-9*pm^2}, {3*pm*c-4*Em-4*Ec, 4*mm*c+3*pc}, {3*pm*c-4*Em-4*Ec, 16*Er*mm-9*pm^2}, {4*mm*c+3*pc, 16*Er*mm-9*pm^2}, {Em+Er+Ec, pc-pm, 5*vm-4*c}, {Em+Er+Ec, pc-pm, mr-mm}, {Em+Er+Ec, pc-pm, 3*pm*c-4*Em-4*Ec}, {Em+Er+Ec, pc-pm, 4*mm*c+3*pc}, {Em+Er+Ec, pc-pm, 16*Er*mm-9*pm^2}, {Em+Er+Ec, 5*vm-4*c, mr-mm}, {Em+Er+Ec, 5*vm-4*c, 3*pm*c-4*Em-4*Ec}, {Em+Er+Ec, 5*vm-4*c, 4*mm*c+3*pc}, {Em+Er+Ec, 5*vm-4*c, 16*Er*mm-9*pm^2}, {Em+Er+Ec, mr-mm, 3*pm*c-4*Em-4*Ec}, {Em+Er+Ec, mr-mm, 4*mm*c+3*pc}, {Em+Er+Ec, mr-mm, 16*Er*mm-9*pm^2}, {Em+Er+Ec, 3*pm*c-4*Em-4*Ec, 4*mm*c+3*pc}, {Em+Er+Ec, 3*pm*c-4*Em-4*Ec, 16*Er*mm-9*pm^2}, {Em+Er+Ec, 4*mm*c+3*pc, 16*Er*mm-9*pm^2}, {pc-pm, 5*vm-4*c, mr-mm}, {pc-pm, 5*vm-4*c, 3*pm*c-4*Em-4*Ec}, {pc-pm, 5*vm-4*c, 4*mm*c+3*pc}, {pc-pm, 5*vm-4*c, 16*Er*mm-9*pm^2}, {pc-pm, mr-mm, 3*pm*c-4*Em-4*Ec}, {pc-pm, mr-mm, 4*mm*c+3*pc}, {pc-pm, mr-mm, 16*Er*mm-9*pm^2}, {pc-pm, 3*pm*c-4*Em-4*Ec, 4*mm*c+3*pc}, {pc-pm, 3*pm*c-4*Em-4*Ec, 16*Er*mm-9*pm^2}, {pc-pm, 4*mm*c+3*pc, 16*Er*mm-9*pm^2}, {5*vm-4*c, mr-mm, 3*pm*c-4*Em-4*Ec}, {5*vm-4*c, mr-mm, 4*mm*c+3*pc}, {5*vm-4*c, mr-mm, 16*Er*mm-9*pm^2}, {5*vm-4*c, 3*pm*c-4*Em-4*Ec, 4*mm*c+3*pc}, {5*vm-4*c, 3*pm*c-4*Em-4*Ec, 16*Er*mm-9*pm^2}, {5*vm-4*c, 4*mm*c+3*pc, 16*Er*mm-9*pm^2}, {mr-mm, 3*pm*c-4*Em-4*Ec, 4*mm*c+3*pc}, {mr-mm, 3*pm*c-4*Em-4*Ec, 16*Er*mm-9*pm^2}, {mr-mm, 4*mm*c+3*pc, 16*Er*mm-9*pm^2}, {3*pm*c-4*Em-4*Ec, 4*mm*c+3*pc, 16*Er*mm-9*pm^2}, {Em+Er+Ec, pc-pm, 5*vm-4*c, mr-mm}, {Em+Er+Ec, pc-pm, 5*vm-4*c, 3*pm*c-4*Em-4*Ec}, {Em+Er+Ec, pc-pm, 5*vm-4*c, 4*mm*c+3*pc}, {Em+Er+Ec, pc-pm, 5*vm-4*c, 16*Er*mm-9*pm^2}, {Em+Er+Ec, pc-pm, mr-mm, 3*pm*c-4*Em-4*Ec}, {Em+Er+Ec, pc-pm, mr-mm, 4*mm*c+3*pc}, {Em+Er+Ec, pc-pm, mr-mm, 16*Er*mm-9*pm^2}, {Em+Er+Ec, pc-pm, 3*pm*c-4*Em-4*Ec, 4*mm*c+3*pc}, {Em+Er+Ec, pc-pm, 3*pm*c-4*Em-4*Ec, 16*Er*mm-9*pm^2}, {Em+Er+Ec, pc-pm, 4*mm*c+3*pc, 16*Er*mm-9*pm^2}, {Em+Er+Ec, 5*vm-4*c, mr-mm, 3*pm*c-4*Em-4*Ec}, {Em+Er+Ec, 5*vm-4*c, mr-mm, 4*mm*c+3*pc}, {Em+Er+Ec, 5*vm-4*c, mr-mm, 16*Er*mm-9*pm^2}, {Em+Er+Ec, 5*vm-4*c, 3*pm*c-4*Em-4*Ec, 4*mm*c+3*pc}, {Em+Er+Ec, 5*vm-4*c, 3*pm*c-4*Em-4*Ec, 16*Er*mm-9*pm^2}, {Em+Er+Ec, 5*vm-4*c, 4*mm*c+3*pc, 16*Er*mm-9*pm^2}, {Em+Er+Ec, mr-mm, 3*pm*c-4*Em-4*Ec, 4*mm*c+3*pc}, {Em+Er+Ec, mr-mm, 3*pm*c-4*Em-4*Ec, 16*Er*mm-9*pm^2}, {Em+Er+Ec, mr-mm, 4*mm*c+3*pc, 16*Er*mm-9*pm^2}, {Em+Er+Ec, 3*pm*c-4*Em-4*Ec, 4*mm*c+3*pc, 16*Er*mm-9*pm^2}, {pc-pm, 5*vm-4*c, mr-mm, 3*pm*c-4*Em-4*Ec}, {pc-pm, 5*vm-4*c, mr-mm, 4*mm*c+3*pc}, {pc-pm, 5*vm-4*c, mr-mm, 16*Er*mm-9*pm^2}, {pc-pm, 5*vm-4*c, 3*pm*c-4*Em-4*Ec, 4*mm*c+3*pc}, {pc-pm, 5*vm-4*c, 3*pm*c-4*Em-4*Ec, 16*Er*mm-9*pm^2}, {pc-pm, 5*vm-4*c, 4*mm*c+3*pc, 16*Er*mm-9*pm^2}, {pc-pm, mr-mm, 3*pm*c-4*Em-4*Ec, 4*mm*c+3*pc}, {pc-pm, mr-mm, 3*pm*c-4*Em-4*Ec, 16*Er*mm-9*pm^2}, {pc-pm, mr-mm, 4*mm*c+3*pc, 16*Er*mm-9*pm^2}, {pc-pm, 3*pm*c-4*Em-4*Ec, 4*mm*c+3*pc, 16*Er*mm-9*pm^2}, {5*vm-4*c, mr-mm, 3*pm*c-4*Em-4*Ec, 4*mm*c+3*pc}, {5*vm-4*c, mr-mm, 3*pm*c-4*Em-4*Ec, 16*Er*mm-9*pm^2}, {5*vm-4*c, mr-mm, 4*mm*c+3*pc, 16*Er*mm-9*pm^2}, {5*vm-4*c, 3*pm*c-4*Em-4*Ec, 4*mm*c+3*pc, 16*Er*mm-9*pm^2}, {mr-mm, 3*pm*c-4*Em-4*Ec, 4*mm*c+3*pc, 16*Er*mm-9*pm^2}};

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
f = openOut "results/inelastic_collision/abduction/noiseless/3_axiom(s)_removed/combo_2_4_9/reasoning/reasoning_output.txt";
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

print("Reasoning complete. Output written to results/inelastic_collision/abduction/noiseless/3_axiom(s)_removed/combo_2_4_9/reasoning/reasoning_output.txt");
