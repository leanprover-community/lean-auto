thf(sortdecl_0, type, s_a0: $tType).

thf(typedecl_t_a0, type, t_a0: (s_a0 > $o)).
thf(typedecl_t_e0, type, t_e0: s_a0).

thf(fact0, axiom, (t_a0 @ t_e0)).
thf(fact1, axiom, ((~) @ (?? @ (^ [X1 : s_a0] : (t_a0 @ X1))))).
% thf(fact1, axiom, ((~) @ ((^ [TX : s_a0 > $o] : (? [VX : s_a0] : (TX @ VX))) @ (^ [X1 : s_a0] : (t_a0 @ X1))))).