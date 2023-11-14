thf(sortdecl_nat, type, s_nat: $tType).
thf(sortdecl_int, type, s_int: $tType).
thf(sortdecl_string, type, s_string: $tType).
thf(sortdecl_empty, type, s_empty: $tType).

thf(typedecl_t_a0, type, t_a0: (((s_empty > $o) > $o) > $o)).
thf(fact0, axiom, ((~) @ (((^ [L : $o, R : $o] : L = R) @ (t_a0 @ (^ [X0 : (s_empty > $o)] : $true))) @ (t_a0 @ (^ [X0 : (s_empty > $o)] : $true))))). 