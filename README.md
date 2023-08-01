# lean-auto
Experiments in automation for Lean

## Coding Style
* ``Array``/``List``: In computational code, we only use ``Array``, functions whose signature contains ``List`` should be declared as ``private``. In verification code, we only use ```List```?
* IR: Logic-oriented IR can be found in ```TRanslation/ReifTerm.lean```, and Solver-oriented IR can be found in ```Auto/IR/..```. Each IR should be equipped with its ``TransM``.
* Translation: Translation code from ``A`` to ``B`` should be written in ```Translation/A2B.lean```

## Utilities
* Command ```#getExprAndApply [ <term> | <ident> ]```: Defined in ```ExprExtra.lean```. This command first elaborates the ```<term>``` into a lean ```Expr```, then applies function ```<ident>``` to ```Expr```. The constant ```ident``` must be already declared and be of type ```Expr → TermElabM Unit```
* Command ```#genMonadState <term>, #genMonadContext <term>```: Defined in ```MonadUtils.lean```. Refer to the comment at the beginning of ```MonadUtils.lean```.
* Command ```#fromMetaTactic [<ident>]```: Calls ```Tactic.liftMetaTactic``` on ```<ident>```. The constant ```<ident>``` must be already declared and be of type ```MVarId → MetaM (List MVarId)```
* Lexical Analyzer Generator: ```Parser/LeanLex.lean```. The frontend is not yet implemented. The backend can be found in ```NDFA.lean```.

## Translation Workflow (Tentative)
* Collecting assumptions from local context and user-provided facts
* $CIC \to COC$: Collecting constructors and recursors for inductive types (effectively, not directly)
  * e.g collecting equational theorem for *match* constructs
  * e.g collect fields of typeclasses (we probably won't do so because typeclass can get very complicated and there are simply too many fields)
  * e.g collect constructors for inductively defined propositions
* $COC \to COC^{p.i}$: Erase proofs
  * $p.i.$ stands for "proof irrelevance"
* $COC^{p.i.} \to COC^{c.u.}$: Instantiating universe levels
  * $c.u.$ stands for "constant universe level"
* $COC^{c.u.} \to COC^{c.u.}$: Instantiating typeclasse arguments
  * **This is probably the most difficult part of translation.**
* $COC^{c.u.} \to COC(\lambda^{c.u.})$: Instantiating (types depending on types), (types depending on terms) and (terms depending on types)
  * Note that at this stage, all the facts we've obtained are still valid $CIC$ expressions and are directly provable from the assumptions.
* $COC(\lambda^{c.u.}) \to COC(\lambda)$
  * We want all types $α$ occuring in the signature of constants and variables to be of sort ```Type (u + 1)```, i.e., $α : Type \ (u + 1)$. This is necessary because we want to write a checker (instead of directly reconstructing proof in DTT) and the valuation function from less expressive logic to dependent type theory requires [the elements in the range of the valuation function] to be [of the same sort].
  * To do this, we use ```GLift```. For example, ```Nat.add``` is transformed into ```Nat.addLift```
    ```lean
    structure GLift.{u, v} (α : Sort u) : Sort (max u (v + 1)) where
      /-- Lift a value into `GLift α` -/    up ::
      /-- Extract a value from `GLift α` -/ down : α

    def Nat.addLift.{u} (x y : GLift.{1, u} Nat) :=
      GLift.up (Nat.add (GLift.down x) (GLift.down y))
    ```
  * We only transfer these "lifted" terms to the less expressive $\lambda_2$, and $\lambda_2$ is unaware of the universe levels wrapped inside ```GLift.up```.
  * Lifted constantes should be introduced into the local context. Theorems corresponding to the original one but using only lifted constants and with uniform universe levels, should also be introduced into the local context. Later translations should only use theorems and constants with uniform universe levels.
* $COC(\lambda) \to COC(\text{TPTP TF0})$: Instantiating function arguments
* **There should also be a process similar to ULifting that "lifts" Bool into Prop**

## Reification
* $CIC \to \text{Propositional}$
  * ```Auto/IR/D2P.lean```
* $COC(\lambda) \to \lambda(\text{TPTP\ TH0})$
* $COC(\text{TPTP TF0}) \to \text{TPTP TF0}$