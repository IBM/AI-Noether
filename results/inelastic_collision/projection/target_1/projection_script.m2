-- AI-Noether: Projection Template
-- Computes Groebner basis and eliminates non-measured variables

R = QQ[mr, vm, vc, pc, Em, Er, Ec, mc, mm, pm, c, MonomialOrder => Lex];

axioms = toList([pm^2*(c^2 - vm^2) - mm^2*vm^2*c^2, Em^2 - (mm*c^2)^2 - (pm*c)^2, Er - mr*c^2, Ec^2 - (mc*c)^2 - (pc*c)^2, 2*Em*Er - Ec^2 + Em^2 + Er^2, pc - pm, vm - 4/5*c, mr - mm, pc^2*(c^2 - vc^2) - mc^2*vc^2*c^2]);
measuredVariables = toList([mm, pm, c]);
nonMeasuredVariables = toList([mr, vm, vc, pc, Em, Er, Ec, mc]);

I = ideal(axioms);
GB = gens gb I;

eliminatedIdeal = eliminate(nonMeasuredVariables, I);
GBproj = gens gb eliminatedIdeal;

f = openOut "results/inelastic_collision/projection/target_1/projection_output.txt";
f << "Groebner basis of the ideal:" << endl;
f << toString GB << endl << endl;
f << "Groebner basis of the eliminated ideal:" << endl;
f << toString GBproj << endl << endl;

f << "Polynomials of the eliminated GB (flattened):" << endl;
scan(flatten entries GBproj, g -> f << toString g << endl);
f << endl;

-- Target checks

qList = toList([16*mm^2*c^4 - 9*pm^2*c^2]);
f << "Target checks in eliminated ideal (membership & literal appearance):" << endl;
scan(qList, q -> (
    remZero = (q % ideal(GBproj) == 0);
    appears = member(true, toList apply(flatten entries GBproj, g -> g == q));
    f << "q = " << toString q << endl;
    f << "  remainderZero: " << toString remZero << endl;
    f << "  appearsLiterallyInGB: " << toString appears << endl;
));


close f;
