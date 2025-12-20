-- AI-Noether: Projection Template
-- Computes Groebner basis and eliminates non-measured variables

R = QQ[F, ad, T, Fd, omega, theta, sintheta, m, d, g, L, j, Pi, Tj, MonomialOrder => Lex];

axioms = toList([ad-g*sintheta, d-L*theta, T*omega-2*Pi, d*omega^2-ad, Tj-j*T, sintheta - theta]);
measuredVariables = toList([d, g, L, j, Pi, Tj]);
nonMeasuredVariables = toList([F, ad, T, Fd, omega, theta, sintheta, m]);

axiomIdeal = ideal(axioms);
GB = gens gb axiomIdeal;

eliminatedIdeal = eliminate(nonMeasuredVariables, axiomIdeal);
GBproj = gens gb eliminatedIdeal;

f = openOut "results/pendulum/projection/target_1/projection_output.txt";
f << "Groebner basis of the ideal:" << endl;
f << toString GB << endl << endl;
f << "Groebner basis of the eliminated ideal:" << endl;
f << toString GBproj << endl << endl;

f << "Polynomials of the eliminated GB (flattened):" << endl;
scan(flatten entries GBproj, g -> f << toString g << endl);
f << endl;

-- Target checks

qList = toList([d*g*Tj^2-4*d*L*j^2*Pi^2]);
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
