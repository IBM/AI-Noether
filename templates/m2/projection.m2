-- AI-Noether: Projection Template
-- Computes Groebner basis and eliminates non-measured variables

R = QQ[{variables}, MonomialOrder => Lex];

axioms = toList([{axioms}]);
measuredVariables = toList([{measured_variables}]);
nonMeasuredVariables = toList([{non_measured_variables}]);

axiomIdeal = ideal(axioms);
GB = gens gb axiomIdeal;

eliminatedIdeal = eliminate(nonMeasuredVariables, axiomIdeal);
GBproj = gens gb eliminatedIdeal;

f = openOut "{output_file}";
f << "Groebner basis of the ideal:" << endl;
f << toString GB << endl << endl;
f << "Groebner basis of the eliminated ideal:" << endl;
f << toString GBproj << endl << endl;

f << "Polynomials of the eliminated GB (flattened):" << endl;
scan(flatten entries GBproj, g -> f << toString g << endl);
f << endl;

-- Target checks
{targets_check_code}

close f;
