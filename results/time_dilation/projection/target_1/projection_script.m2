-- AI-Noether: Projection Template
-- Computes Groebner basis and eliminates non-measured variables

R = QQ[d, dt, dt0, L, c, F0, F, v, MonomialOrder => Lex];

axioms = toList([c*dt0 - 2*d, 4*L^2 - 4*d^2 - v^2*dt^2, F0*dt0 - 1, F*dt - 1, c*dt - 2*L]);
measuredVariables = toList([c, F0, F, v]);
nonMeasuredVariables = toList([d, dt, dt0, L]);

I = ideal(axioms);
GB = gens gb I;

eliminatedIdeal = eliminate(nonMeasuredVariables, I);
GBproj = gens gb eliminatedIdeal;

f = openOut "results/time_dilation/projection/target_1/projection_output.txt";
f << "Groebner basis of the ideal:" << endl;
f << toString GB << endl << endl;
f << "Groebner basis of the eliminated ideal:" << endl;
f << toString GBproj << endl << endl;

f << "Polynomials of the eliminated GB (flattened):" << endl;
scan(flatten entries GBproj, g -> f << toString g << endl);
f << endl;

-- Target checks

qList = toList([c^2*F0^2-c^2*F^2-F0^2*v^2]);
f << "Target checks in eliminated ideal (membership & literal appearance):" << endl;
scan(qList, q -> (
    remZero = (q % ideal(GBproj) == 0);
    appears = member(true, toList apply(flatten entries GBproj, g -> g == q));
    f << "q = " << toString q << endl;
    f << "  remainderZero: " << toString remZero << endl;
    f << "  appearsLiterallyInGB: " << toString appears << endl;
));


close f;
