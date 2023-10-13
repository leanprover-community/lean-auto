__Auto Issues:__
* HOL to FOL. Do this in the verified checker. Introduce new etoms to represent instancecs of higher-order functions.
* When we matched against ``Eq`` in monomorphization, we found that some type arguments of other constants got unified with ``Prop``, which created a bunch of junk lemma. Find out whether something similar happened in Duper.
* Implement native interpretation and native proof reconstruction
* Improve portfolio mode script. Download E and zipperposition from the web.
* SMT translation of integer div/mod. Current translation is not correct.

__Lean Issues:__
* ``cases`` fails on some simple examples. E.g, ``cases h : a.beq b`` fails if the goal contains term
  ```
  match h : a.beq b with
  | true => .... (h) ...
  | false => .... (h) ...
  ```
* Slow reduction: Using the interpreter to evaluate checker table is significantly faster than using reduction.
* Slow compilation: Compiling [ChkSteps]/[Checker table] sometimes exhibits superlinear behaviour.
* Pretty printer: **TODO**