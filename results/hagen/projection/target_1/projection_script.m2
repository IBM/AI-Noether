-- AI-Noether: Projection Template
-- Computes Groebner basis and eliminates non-measured variables

R = QQ[c0, c2, dp, r, Rad, u, L, mu, delP, MonomialOrder => Lex];

axioms = toList([4*r*c2*mu - r*dp, delP + L*dp, c0 + c2*Rad^2, u - c0 - r^2*c2]);
measuredVariables = toList([r, Rad, u, L, mu, delP]);
nonMeasuredVariables = toList([c0, c2, dp]);

axiomIdeal = ideal(axioms);
GB = gens gb axiomIdeal;

eliminatedIdeal = eliminate(nonMeasuredVariables, axiomIdeal);
GBproj = gens gb eliminatedIdeal;

f = openOut "results/hagen/projection/target_1/projection_output.txt";
f << "Groebner basis of the ideal:" << endl;
f << toString GB << endl << endl;
f << "Groebner basis of the eliminated ideal:" << endl;
f << toString GBproj << endl << endl;

f << "Polynomials of the eliminated GB (flattened):" << endl;
scan(flatten entries GBproj, g -> f << toString g << endl);
f << endl;

-- Target checks

qList = toList([r^3*delP - r*Rad^2*delP + 4*r*u*L*mu]);
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
