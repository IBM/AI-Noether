-- AI-Noether: Reasoning Template (Noiseless)
-- Tests if candidate axiom sets, when added to remaining axioms, prove targets

needsPackage("PrimaryDecomposition", Reload => true)

-- Ring definition
R = QQ[mr, vm, vc, pc, Em, Er, Ec, mc, mm, pm, c, MonomialOrder => Lex];

-- Input data
remainingAxioms = toList([pm^2*(c^2 - vm^2) - mm^2*vm^2*c^2, Em^2 - (mm*c^2)^2 - (pm*c)^2, Ec^2 - (mc*c)^2 - (pc*c)^2, 2*Em*Er - Ec^2 + Em^2 + Er^2, pc - pm, vm - 4/5*c, mr - mm, pc^2*(c^2 - vc^2) - mc^2*vc^2*c^2]);
qList = toList([16*mm^2*c^4 - 9*pm^2*c^2]);
k = #qList;

-- Per-target variable partitions
measuredPerTarget = {{mm, pm, c}};
nonMeasuredPerTarget = {{mr, vm, vc, pc, Em, Er, Ec, mc}};

-- Candidate axiom sets to test (list of lists)
candidateSets = {{}, {c}, {pm}, {Ec}, {Er}, {Em}, {pc-pm}, {vm-4/5*c}, {mr-mm}, {c, pm}, {c, Ec}, {c, Er}, {c, Em}, {c, pc-pm}, {c, vm-4/5*c}, {c, mr-mm}, {pm, Ec}, {pm, Er}, {pm, Em}, {pm, pc-pm}, {pm, vm-4/5*c}, {pm, mr-mm}, {Ec, Er}, {Ec, Em}, {Ec, pc-pm}, {Ec, vm-4/5*c}, {Ec, mr-mm}, {Er, Em}, {Er, pc-pm}, {Er, vm-4/5*c}, {Er, mr-mm}, {Em, pc-pm}, {Em, vm-4/5*c}, {Em, mr-mm}, {pc-pm, vm-4/5*c}, {pc-pm, mr-mm}, {vm-4/5*c, mr-mm}, {4*mm*c-3*pm}, {-mc^2*c^2-pm^2*c^2+Ec^2}, {9*vc^2*mc^2+16*vc^2*mm^2-9*pm^2}, {5*pm*c+4*Er+4*Ec}, {-5*pm*c+4*Em}, {pc-pm}, {vm-4/5*c}, {mr-mm}, {4*mm*c-3*pm, -mc^2*c^2-pm^2*c^2+Ec^2}, {4*mm*c-3*pm, 9*vc^2*mc^2+16*vc^2*mm^2-9*pm^2}, {4*mm*c-3*pm, 5*pm*c+4*Er+4*Ec}, {4*mm*c-3*pm, -5*pm*c+4*Em}, {4*mm*c-3*pm, pc-pm}, {4*mm*c-3*pm, vm-4/5*c}, {4*mm*c-3*pm, mr-mm}, {-mc^2*c^2-pm^2*c^2+Ec^2, 9*vc^2*mc^2+16*vc^2*mm^2-9*pm^2}, {-mc^2*c^2-pm^2*c^2+Ec^2, 5*pm*c+4*Er+4*Ec}, {-mc^2*c^2-pm^2*c^2+Ec^2, -5*pm*c+4*Em}, {-mc^2*c^2-pm^2*c^2+Ec^2, pc-pm}, {-mc^2*c^2-pm^2*c^2+Ec^2, vm-4/5*c}, {-mc^2*c^2-pm^2*c^2+Ec^2, mr-mm}, {9*vc^2*mc^2+16*vc^2*mm^2-9*pm^2, 5*pm*c+4*Er+4*Ec}, {9*vc^2*mc^2+16*vc^2*mm^2-9*pm^2, -5*pm*c+4*Em}, {9*vc^2*mc^2+16*vc^2*mm^2-9*pm^2, pc-pm}, {9*vc^2*mc^2+16*vc^2*mm^2-9*pm^2, vm-4/5*c}, {9*vc^2*mc^2+16*vc^2*mm^2-9*pm^2, mr-mm}, {5*pm*c+4*Er+4*Ec, -5*pm*c+4*Em}, {5*pm*c+4*Er+4*Ec, pc-pm}, {5*pm*c+4*Er+4*Ec, vm-4/5*c}, {5*pm*c+4*Er+4*Ec, mr-mm}, {-5*pm*c+4*Em, pc-pm}, {-5*pm*c+4*Em, vm-4/5*c}, {-5*pm*c+4*Em, mr-mm}, {pc-pm, vm-4/5*c}, {pc-pm, mr-mm}, {vm-4/5*c, mr-mm}, {c}, {Ec}, {Er}, {Em}, {pc-pm}, {vc}, {vm-4/5*c}, {mr-mm}, {c, Ec}, {c, Er}, {c, Em}, {c, pc-pm}, {c, vc}, {c, vm-4/5*c}, {c, mr-mm}, {Ec, Er}, {Ec, Em}, {Ec, pc-pm}, {Ec, vc}, {Ec, vm-4/5*c}, {Ec, mr-mm}, {Er, Em}, {Er, pc-pm}, {Er, vc}, {Er, vm-4/5*c}, {Er, mr-mm}, {Em, pc-pm}, {Em, vc}, {Em, vm-4/5*c}, {Em, mr-mm}, {pc-pm, vc}, {pc-pm, vm-4/5*c}, {pc-pm, mr-mm}, {vc, vm-4/5*c}, {vc, mr-mm}, {vm-4/5*c, mr-mm}, {4*mm*c+3*pm}, {-mc^2*c^2-pm^2*c^2+Ec^2}, {9*vc^2*mc^2+16*vc^2*mm^2-9*pm^2}, {5*pm*c+4*Er+4*Ec}, {-5*pm*c+4*Em}, {pc-pm}, {vm-4/5*c}, {mr-mm}, {4*mm*c+3*pm, -mc^2*c^2-pm^2*c^2+Ec^2}, {4*mm*c+3*pm, 9*vc^2*mc^2+16*vc^2*mm^2-9*pm^2}, {4*mm*c+3*pm, 5*pm*c+4*Er+4*Ec}, {4*mm*c+3*pm, -5*pm*c+4*Em}, {4*mm*c+3*pm, pc-pm}, {4*mm*c+3*pm, vm-4/5*c}, {4*mm*c+3*pm, mr-mm}, {-mc^2*c^2-pm^2*c^2+Ec^2, 9*vc^2*mc^2+16*vc^2*mm^2-9*pm^2}, {-mc^2*c^2-pm^2*c^2+Ec^2, 5*pm*c+4*Er+4*Ec}, {-mc^2*c^2-pm^2*c^2+Ec^2, -5*pm*c+4*Em}, {-mc^2*c^2-pm^2*c^2+Ec^2, pc-pm}, {-mc^2*c^2-pm^2*c^2+Ec^2, vm-4/5*c}, {-mc^2*c^2-pm^2*c^2+Ec^2, mr-mm}, {9*vc^2*mc^2+16*vc^2*mm^2-9*pm^2, 5*pm*c+4*Er+4*Ec}, {9*vc^2*mc^2+16*vc^2*mm^2-9*pm^2, -5*pm*c+4*Em}, {9*vc^2*mc^2+16*vc^2*mm^2-9*pm^2, pc-pm}, {9*vc^2*mc^2+16*vc^2*mm^2-9*pm^2, vm-4/5*c}, {9*vc^2*mc^2+16*vc^2*mm^2-9*pm^2, mr-mm}, {5*pm*c+4*Er+4*Ec, -5*pm*c+4*Em}, {5*pm*c+4*Er+4*Ec, pc-pm}, {5*pm*c+4*Er+4*Ec, vm-4/5*c}, {5*pm*c+4*Er+4*Ec, mr-mm}, {-5*pm*c+4*Em, pc-pm}, {-5*pm*c+4*Em, vm-4/5*c}, {-5*pm*c+4*Em, mr-mm}, {pc-pm, vm-4/5*c}, {pc-pm, mr-mm}, {vm-4/5*c, mr-mm}, {4*mm*c+3*pm}, {-mc^2*c^2-pm^2*c^2+Ec^2}, {9*vc^2*mc^2+16*vc^2*mm^2-9*pm^2}, {-5*pm*c+4*Er+4*Ec}, {5*pm*c+4*Em}, {pc-pm}, {vm-4/5*c}, {mr-mm}, {4*mm*c+3*pm, -mc^2*c^2-pm^2*c^2+Ec^2}, {4*mm*c+3*pm, 9*vc^2*mc^2+16*vc^2*mm^2-9*pm^2}, {4*mm*c+3*pm, -5*pm*c+4*Er+4*Ec}, {4*mm*c+3*pm, 5*pm*c+4*Em}, {4*mm*c+3*pm, pc-pm}, {4*mm*c+3*pm, vm-4/5*c}, {4*mm*c+3*pm, mr-mm}, {-mc^2*c^2-pm^2*c^2+Ec^2, 9*vc^2*mc^2+16*vc^2*mm^2-9*pm^2}, {-mc^2*c^2-pm^2*c^2+Ec^2, -5*pm*c+4*Er+4*Ec}, {-mc^2*c^2-pm^2*c^2+Ec^2, 5*pm*c+4*Em}, {-mc^2*c^2-pm^2*c^2+Ec^2, pc-pm}, {-mc^2*c^2-pm^2*c^2+Ec^2, vm-4/5*c}, {-mc^2*c^2-pm^2*c^2+Ec^2, mr-mm}, {9*vc^2*mc^2+16*vc^2*mm^2-9*pm^2, -5*pm*c+4*Er+4*Ec}, {9*vc^2*mc^2+16*vc^2*mm^2-9*pm^2, 5*pm*c+4*Em}, {9*vc^2*mc^2+16*vc^2*mm^2-9*pm^2, pc-pm}, {9*vc^2*mc^2+16*vc^2*mm^2-9*pm^2, vm-4/5*c}, {9*vc^2*mc^2+16*vc^2*mm^2-9*pm^2, mr-mm}, {-5*pm*c+4*Er+4*Ec, 5*pm*c+4*Em}, {-5*pm*c+4*Er+4*Ec, pc-pm}, {-5*pm*c+4*Er+4*Ec, vm-4/5*c}, {-5*pm*c+4*Er+4*Ec, mr-mm}, {5*pm*c+4*Em, pc-pm}, {5*pm*c+4*Em, vm-4/5*c}, {5*pm*c+4*Em, mr-mm}, {pc-pm, vm-4/5*c}, {pc-pm, mr-mm}, {vm-4/5*c, mr-mm}, {4*mm*c-3*pm}, {-mc^2*c^2-pm^2*c^2+Ec^2}, {9*vc^2*mc^2+16*vc^2*mm^2-9*pm^2}, {-5*pm*c+4*Er+4*Ec}, {5*pm*c+4*Em}, {pc-pm}, {vm-4/5*c}, {mr-mm}, {4*mm*c-3*pm, -mc^2*c^2-pm^2*c^2+Ec^2}, {4*mm*c-3*pm, 9*vc^2*mc^2+16*vc^2*mm^2-9*pm^2}, {4*mm*c-3*pm, -5*pm*c+4*Er+4*Ec}, {4*mm*c-3*pm, 5*pm*c+4*Em}, {4*mm*c-3*pm, pc-pm}, {4*mm*c-3*pm, vm-4/5*c}, {4*mm*c-3*pm, mr-mm}, {-mc^2*c^2-pm^2*c^2+Ec^2, 9*vc^2*mc^2+16*vc^2*mm^2-9*pm^2}, {-mc^2*c^2-pm^2*c^2+Ec^2, -5*pm*c+4*Er+4*Ec}, {-mc^2*c^2-pm^2*c^2+Ec^2, 5*pm*c+4*Em}, {-mc^2*c^2-pm^2*c^2+Ec^2, pc-pm}, {-mc^2*c^2-pm^2*c^2+Ec^2, vm-4/5*c}, {-mc^2*c^2-pm^2*c^2+Ec^2, mr-mm}, {9*vc^2*mc^2+16*vc^2*mm^2-9*pm^2, -5*pm*c+4*Er+4*Ec}, {9*vc^2*mc^2+16*vc^2*mm^2-9*pm^2, 5*pm*c+4*Em}, {9*vc^2*mc^2+16*vc^2*mm^2-9*pm^2, pc-pm}, {9*vc^2*mc^2+16*vc^2*mm^2-9*pm^2, vm-4/5*c}, {9*vc^2*mc^2+16*vc^2*mm^2-9*pm^2, mr-mm}, {-5*pm*c+4*Er+4*Ec, 5*pm*c+4*Em}, {-5*pm*c+4*Er+4*Ec, pc-pm}, {-5*pm*c+4*Er+4*Ec, vm-4/5*c}, {-5*pm*c+4*Er+4*Ec, mr-mm}, {5*pm*c+4*Em, pc-pm}, {5*pm*c+4*Em, vm-4/5*c}, {5*pm*c+4*Em, mr-mm}, {pc-pm, vm-4/5*c}, {pc-pm, mr-mm}, {vm-4/5*c, mr-mm}, {4*mm*c-3*pm}, {-mc^2*c^2-pm^2*c^2+Ec^2}, {9*vc^2*mc^2+16*vc^2*mm^2-9*pm^2}, {-5*pm*c+4*Er-4*Ec}, {5*pm*c+4*Em}, {pc-pm}, {vm-4/5*c}, {mr-mm}, {4*mm*c-3*pm, -mc^2*c^2-pm^2*c^2+Ec^2}, {4*mm*c-3*pm, 9*vc^2*mc^2+16*vc^2*mm^2-9*pm^2}, {4*mm*c-3*pm, -5*pm*c+4*Er-4*Ec}, {4*mm*c-3*pm, 5*pm*c+4*Em}, {4*mm*c-3*pm, pc-pm}, {4*mm*c-3*pm, vm-4/5*c}, {4*mm*c-3*pm, mr-mm}, {-mc^2*c^2-pm^2*c^2+Ec^2, 9*vc^2*mc^2+16*vc^2*mm^2-9*pm^2}, {-mc^2*c^2-pm^2*c^2+Ec^2, -5*pm*c+4*Er-4*Ec}, {-mc^2*c^2-pm^2*c^2+Ec^2, 5*pm*c+4*Em}, {-mc^2*c^2-pm^2*c^2+Ec^2, pc-pm}, {-mc^2*c^2-pm^2*c^2+Ec^2, vm-4/5*c}, {-mc^2*c^2-pm^2*c^2+Ec^2, mr-mm}, {9*vc^2*mc^2+16*vc^2*mm^2-9*pm^2, -5*pm*c+4*Er-4*Ec}, {9*vc^2*mc^2+16*vc^2*mm^2-9*pm^2, 5*pm*c+4*Em}, {9*vc^2*mc^2+16*vc^2*mm^2-9*pm^2, pc-pm}, {9*vc^2*mc^2+16*vc^2*mm^2-9*pm^2, vm-4/5*c}, {9*vc^2*mc^2+16*vc^2*mm^2-9*pm^2, mr-mm}, {-5*pm*c+4*Er-4*Ec, 5*pm*c+4*Em}, {-5*pm*c+4*Er-4*Ec, pc-pm}, {-5*pm*c+4*Er-4*Ec, vm-4/5*c}, {-5*pm*c+4*Er-4*Ec, mr-mm}, {5*pm*c+4*Em, pc-pm}, {5*pm*c+4*Em, vm-4/5*c}, {5*pm*c+4*Em, mr-mm}, {pc-pm, vm-4/5*c}, {pc-pm, mr-mm}, {vm-4/5*c, mr-mm}, {4*mm*c+3*pm}, {-mc^2*c^2-pm^2*c^2+Ec^2}, {9*vc^2*mc^2+16*vc^2*mm^2-9*pm^2}, {-5*pm*c+4*Er-4*Ec}, {5*pm*c+4*Em}, {pc-pm}, {vm-4/5*c}, {mr-mm}, {4*mm*c+3*pm, -mc^2*c^2-pm^2*c^2+Ec^2}, {4*mm*c+3*pm, 9*vc^2*mc^2+16*vc^2*mm^2-9*pm^2}, {4*mm*c+3*pm, -5*pm*c+4*Er-4*Ec}, {4*mm*c+3*pm, 5*pm*c+4*Em}, {4*mm*c+3*pm, pc-pm}, {4*mm*c+3*pm, vm-4/5*c}, {4*mm*c+3*pm, mr-mm}, {-mc^2*c^2-pm^2*c^2+Ec^2, 9*vc^2*mc^2+16*vc^2*mm^2-9*pm^2}, {-mc^2*c^2-pm^2*c^2+Ec^2, -5*pm*c+4*Er-4*Ec}, {-mc^2*c^2-pm^2*c^2+Ec^2, 5*pm*c+4*Em}, {-mc^2*c^2-pm^2*c^2+Ec^2, pc-pm}, {-mc^2*c^2-pm^2*c^2+Ec^2, vm-4/5*c}, {-mc^2*c^2-pm^2*c^2+Ec^2, mr-mm}, {9*vc^2*mc^2+16*vc^2*mm^2-9*pm^2, -5*pm*c+4*Er-4*Ec}, {9*vc^2*mc^2+16*vc^2*mm^2-9*pm^2, 5*pm*c+4*Em}, {9*vc^2*mc^2+16*vc^2*mm^2-9*pm^2, pc-pm}, {9*vc^2*mc^2+16*vc^2*mm^2-9*pm^2, vm-4/5*c}, {9*vc^2*mc^2+16*vc^2*mm^2-9*pm^2, mr-mm}, {-5*pm*c+4*Er-4*Ec, 5*pm*c+4*Em}, {-5*pm*c+4*Er-4*Ec, pc-pm}, {-5*pm*c+4*Er-4*Ec, vm-4/5*c}, {-5*pm*c+4*Er-4*Ec, mr-mm}, {5*pm*c+4*Em, pc-pm}, {5*pm*c+4*Em, vm-4/5*c}, {5*pm*c+4*Em, mr-mm}, {pc-pm, vm-4/5*c}, {pc-pm, mr-mm}, {vm-4/5*c, mr-mm}, {4*mm*c+3*pm}, {-mc^2*c^2-pm^2*c^2+Ec^2}, {9*vc^2*mc^2+16*vc^2*mm^2-9*pm^2}, {5*pm*c+4*Er-4*Ec}, {-5*pm*c+4*Em}, {pc-pm}, {vm-4/5*c}, {mr-mm}, {4*mm*c+3*pm, -mc^2*c^2-pm^2*c^2+Ec^2}, {4*mm*c+3*pm, 9*vc^2*mc^2+16*vc^2*mm^2-9*pm^2}, {4*mm*c+3*pm, 5*pm*c+4*Er-4*Ec}, {4*mm*c+3*pm, -5*pm*c+4*Em}, {4*mm*c+3*pm, pc-pm}, {4*mm*c+3*pm, vm-4/5*c}, {4*mm*c+3*pm, mr-mm}, {-mc^2*c^2-pm^2*c^2+Ec^2, 9*vc^2*mc^2+16*vc^2*mm^2-9*pm^2}, {-mc^2*c^2-pm^2*c^2+Ec^2, 5*pm*c+4*Er-4*Ec}, {-mc^2*c^2-pm^2*c^2+Ec^2, -5*pm*c+4*Em}, {-mc^2*c^2-pm^2*c^2+Ec^2, pc-pm}, {-mc^2*c^2-pm^2*c^2+Ec^2, vm-4/5*c}, {-mc^2*c^2-pm^2*c^2+Ec^2, mr-mm}, {9*vc^2*mc^2+16*vc^2*mm^2-9*pm^2, 5*pm*c+4*Er-4*Ec}, {9*vc^2*mc^2+16*vc^2*mm^2-9*pm^2, -5*pm*c+4*Em}, {9*vc^2*mc^2+16*vc^2*mm^2-9*pm^2, pc-pm}, {9*vc^2*mc^2+16*vc^2*mm^2-9*pm^2, vm-4/5*c}, {9*vc^2*mc^2+16*vc^2*mm^2-9*pm^2, mr-mm}, {5*pm*c+4*Er-4*Ec, -5*pm*c+4*Em}, {5*pm*c+4*Er-4*Ec, pc-pm}, {5*pm*c+4*Er-4*Ec, vm-4/5*c}, {5*pm*c+4*Er-4*Ec, mr-mm}, {-5*pm*c+4*Em, pc-pm}, {-5*pm*c+4*Em, vm-4/5*c}, {-5*pm*c+4*Em, mr-mm}, {pc-pm, vm-4/5*c}, {pc-pm, mr-mm}, {vm-4/5*c, mr-mm}, {4*mm*c-3*pm}, {-mc^2*c^2-pm^2*c^2+Ec^2}, {9*vc^2*mc^2+16*vc^2*mm^2-9*pm^2}, {5*pm*c+4*Er-4*Ec}, {-5*pm*c+4*Em}, {pc-pm}, {vm-4/5*c}, {mr-mm}, {4*mm*c-3*pm, -mc^2*c^2-pm^2*c^2+Ec^2}, {4*mm*c-3*pm, 9*vc^2*mc^2+16*vc^2*mm^2-9*pm^2}, {4*mm*c-3*pm, 5*pm*c+4*Er-4*Ec}, {4*mm*c-3*pm, -5*pm*c+4*Em}, {4*mm*c-3*pm, pc-pm}, {4*mm*c-3*pm, vm-4/5*c}, {4*mm*c-3*pm, mr-mm}, {-mc^2*c^2-pm^2*c^2+Ec^2, 9*vc^2*mc^2+16*vc^2*mm^2-9*pm^2}, {-mc^2*c^2-pm^2*c^2+Ec^2, 5*pm*c+4*Er-4*Ec}, {-mc^2*c^2-pm^2*c^2+Ec^2, -5*pm*c+4*Em}, {-mc^2*c^2-pm^2*c^2+Ec^2, pc-pm}, {-mc^2*c^2-pm^2*c^2+Ec^2, vm-4/5*c}, {-mc^2*c^2-pm^2*c^2+Ec^2, mr-mm}, {9*vc^2*mc^2+16*vc^2*mm^2-9*pm^2, 5*pm*c+4*Er-4*Ec}, {9*vc^2*mc^2+16*vc^2*mm^2-9*pm^2, -5*pm*c+4*Em}, {9*vc^2*mc^2+16*vc^2*mm^2-9*pm^2, pc-pm}, {9*vc^2*mc^2+16*vc^2*mm^2-9*pm^2, vm-4/5*c}, {9*vc^2*mc^2+16*vc^2*mm^2-9*pm^2, mr-mm}, {5*pm*c+4*Er-4*Ec, -5*pm*c+4*Em}, {5*pm*c+4*Er-4*Ec, pc-pm}, {5*pm*c+4*Er-4*Ec, vm-4/5*c}, {5*pm*c+4*Er-4*Ec, mr-mm}, {-5*pm*c+4*Em, pc-pm}, {-5*pm*c+4*Em, vm-4/5*c}, {-5*pm*c+4*Em, mr-mm}, {pc-pm, vm-4/5*c}, {pc-pm, mr-mm}, {vm-4/5*c, mr-mm}};

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
f = openOut "results/inelastic_collision/abduction/noiseless/1_axiom(s)_removed/combo_3/reasoning/reasoning_output.txt";
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

print("Reasoning complete. Output written to results/inelastic_collision/abduction/noiseless/1_axiom(s)_removed/combo_3/reasoning/reasoning_output.txt");
