thf(sortdecl_nat, type, s_nat: $tType).

thf(fact0, axiom, (! [X0 : s_nat] : (((=) @ X0) @ X0))).
thf(fact1, axiom, ((~) @ (? [X0 : s_nat] : (((=) @ X0) @ X0)))).