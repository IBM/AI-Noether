-- AI-Noether: Projection Template
-- Computes Groebner basis and eliminates non-measured variables

R = QQ[Fc, Fg, w, m1, d1, m2, d2, p, MonomialOrder => Lex];

axioms = toList([m1*d1-m2*d2, Fg*(d1+d2)^2 - m1*m2, Fc - m2*d2*w^2, Fc - Fg, w*p - 1]);
measuredVariables = toList([m1, d1, m2, d2, p]);
nonMeasuredVariables = toList([Fc, Fg, w]);

axiomIdeal = ideal(axioms);
GB = gens gb axiomIdeal;

eliminatedIdeal = eliminate(nonMeasuredVariables, axiomIdeal);
GBproj = gens gb eliminatedIdeal;

f = openOut "results/kepler/projection/target_1/projection_output.txt";
f << "Groebner basis of the ideal:" << endl;
f << toString GB << endl << endl;
f << "Groebner basis of the eliminated ideal:" << endl;
f << toString GBproj << endl << endl;

f << "Polynomials of the eliminated GB (flattened):" << endl;
scan(flatten entries GBproj, g -> f << toString g << endl);
f << endl;

-- Target checks

qList = toList([m1*m2*p^2-m1*d1*d2^2-m2*d1^2*d2-2*m2*d1*d2^2]);
elimIdeal = ideal(flatten entries GBproj);
f << "Target checks in eliminated ideal (membership & literal appearance):" << endl;
scan(qList, q -> (
    rem = q % elimIdeal;
    remZero = (rem == 0);
    appears = member(true, toList apply(flatten entries GBproj, g -> g == q));
    f << "q = " << toString q << endl;
    f << "  remainderZero: " << toString remZero << endl;
    f << "  appearsLiterallyInGB: " << toString appears << endl;
));


close f;
