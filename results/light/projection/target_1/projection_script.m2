-- AI-Noether: Projection Template
-- Computes Groebner basis and eliminates non-measured variables

R = QQ[S, ap, sintheta, dA, dtheta, r, P, qc, x0, w, MonomialOrder => Lex];

axioms = toList([S * r^2 - qc^2 * ap^2 * sintheta^2, 100*dA - 2*(314)*(r^2)*sintheta*dtheta, P - S * dA, 4 - 3*sintheta^3 * dtheta, 2*ap^2 - w^4 * x0^2]);
measuredVariables = toList([P, qc, x0, w]);
nonMeasuredVariables = toList([S, ap, sintheta, dA, dtheta, r]);

axiomIdeal = ideal(axioms);
GB = gens gb axiomIdeal;

eliminatedIdeal = eliminate(nonMeasuredVariables, axiomIdeal);
GBproj = gens gb eliminatedIdeal;

f = openOut "results/light/projection/target_1/projection_output.txt";
f << "Groebner basis of the ideal:" << endl;
f << toString GB << endl << endl;
f << "Groebner basis of the eliminated ideal:" << endl;
f << toString GBproj << endl << endl;

f << "Polynomials of the eliminated GB (flattened):" << endl;
scan(flatten entries GBproj, g -> f << toString g << endl);
f << endl;

-- Target checks

qList = toList([75*P - 314*qc^2*w^4*x0^2]);
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
