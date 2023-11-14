thf(sortdecl_nat, type, s_nat: $tType).
thf(sortdecl_int, type, s_int: $tType).
thf(sortdecl_string, type, s_string: $tType).
thf(sortdecl_empty, type, s_empty: $tType).
thf(sortdecl_0, type, s_a0: $tType).
    
thf(typedecl_t_a1, type, t_a1: $o).
thf(typedecl_t_a0, type, t_a0: (s_a0 > $o)).
    
thf(fact0, axiom, ((~) @ (((^ [L : $o, R : $o] : L = R) @ (? [X0 : s_a0] : (((=>) @ (t_a0 @ X0)) @ t_a1))) @ (((=>) @ (! [X0 : s_a0] : (t_a0 @ X0))) @ t_a1)))). 