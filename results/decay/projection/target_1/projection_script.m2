-- AI-Noether: Projection Template
-- Computes Groebner basis and eliminates non-measured variables

R = QQ[pp, pmu, Ev, Emu, Ep, pv, mp, mmu, MonomialOrder => Lex];

axioms = toList([pv - pmu, Ep - mp, Ev - pv, Ep - Emu - Ev, Emu^2 - pmu^2 - mmu^2]);
measuredVariables = toList([pv, mp, mmu]);
nonMeasuredVariables = toList([pp, pmu, Ev, Emu, Ep]);

I = ideal(axioms);
GB = gens gb I;

eliminatedIdeal = eliminate(nonMeasuredVariables, I);
GBproj = gens gb eliminatedIdeal;

f = openOut "results/decay/projection/target_1/projection_output.txt";
f << "Groebner basis of the ideal:" << endl;
f << toString GB << endl << endl;
f << "Groebner basis of the eliminated ideal:" << endl;
f << toString GBproj << endl << endl;

f << "Polynomials of the eliminated GB (flattened):" << endl;
scan(flatten entries GBproj, g -> f << toString g << endl);
f << endl;

-- Target checks

qList = toList([2*pv*mp - mp^2 + mmu^2]);
f << "Target checks in eliminated ideal (membership & literal appearance):" << endl;
scan(qList, q -> (
    remZero = (q % ideal(GBproj) == 0);
    appears = member(true, toList apply(flatten entries GBproj, g -> g == q));
    f << "q = " << toString q << endl;
    f << "  remainderZero: " << toString remZero << endl;
    f << "  appearsLiterallyInGB: " << toString appears << endl;
));


close f;
