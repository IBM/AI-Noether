-- AI-Noether: Projection Template
-- Computes Groebner basis and eliminates non-measured variables

R = QQ[c, dt, v, F0, F, dt0, L0, L, m0, u0, m, u, MonomialOrder => Lex];

axioms = toList([F0*dt0 - 1, F*dt - 1, c*dt0 - 2*L0, c^2*dt^2 - 4*L0^2 - v^2*dt^2, m0*u0 - m*u, u0*dt0 - u*dt, dt*(c^2 - v^2) - 2*L*c]);
measuredVariables = toList([L, L0, v, c]);
nonMeasuredVariables = toList([dt, F0, F, dt0, m0, u0, m, u]);

axiomIdeal = ideal(axioms);
GB = gens gb axiomIdeal;

eliminatedIdeal = eliminate(nonMeasuredVariables, axiomIdeal);
GBproj = gens gb eliminatedIdeal;

f = openOut "results/relativistic_laws_updated/projection/target_3/projection_output.txt";
f << "Groebner basis of the ideal:" << endl;
f << toString GB << endl << endl;
f << "Groebner basis of the eliminated ideal:" << endl;
f << toString GBproj << endl << endl;

f << "Polynomials of the eliminated GB (flattened):" << endl;
scan(flatten entries GBproj, g -> f << toString g << endl);
f << endl;

-- Target checks

qList = toList([c^2*L0^2-c^2*L^2-v^2*L0^2]);
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
