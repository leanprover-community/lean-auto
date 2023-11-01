__Auto Issues:__
* HOL to FOL. Do this in the verified checker. Introduce new etoms to represent instancecs of higher-order functions.
* When we matched against ``Eq`` in monomorphization, we found that some type arguments of other constants got unified with ``Prop``, which created a bunch of junk lemma. Find out whether something similar happened in Duper.
* Implement native interpretation and native proof reconstruction
* Improve portfolio mode script. Download E and zipperposition from the web.
* Floating point numbers
* String: Some string operations missing in Lean
* UnfoldProj does not work with non-struct inductive types. For example, suppose we have
  ```lean
  inductive Nonstruct where
    | mk : Nat → Bool → Nonstruct
  ```
  we can still do projection:
  ```
  #check (fun (x : Nonstruct) => x.1)
  ```
* Bitwise operation for ``Nat``
* Add semantics check for ``BitVec`` operations
* Unsound translation for SMT: Although we have the option ``auto.smt.trust``, the translation is unsound since types in Lean might be inhabited while SMT-LIB assumes that all types are inhabited.
* ``autoSMTSorry`` warning?
* TPTP interpreted polymorphic logical constants type inference.
* Strange performance issues on Windows

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

__Solver Issues:__
* It seems that Z3 does not recognize ``https://smtlib.cs.uiowa.edu/theories-UnicodeStrings.shtml`` unicode escape sequences, and prints ``sat`` on ``Test/Smt/String_Escape.smt``