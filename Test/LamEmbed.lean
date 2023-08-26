import Auto.Embedding.LamConv
import Auto.Lib.ExprExtra

open Auto.Embedding.Lam

#print LamTerm.headBeta

-- (.atom k) → (.atom k) → ⋯ → (.atom k) → (.atom k)
def manyArgFuncTy (n : Nat) (k : Nat) : LamSort :=
  match n with
  | 0 => .atom k
  | n' + 1 => .func (.atom k) (manyArgFuncTy n' k)

-- **Succeeds in a reasonable amount of time**
set_option maxRecDepth 4000 in
set_option lazyReduce.logInfo false in
#lazyReduce manyArgFuncTy 3000 0
set_option maxRecDepth 2000 in
#reduce LamSort.beq_eq (manyArgFuncTy 100 40) (manyArgFuncTy 100 40)

-- λ (x₁ x₂ ... xₙ : (.atom 0)) . (.atom 0) x₁ x₂ ... xₙ
-- Note that the first `.atom 0` is a type atom, while the
--   second `.atom 0` is a term atom
def manyBinders (n : Nat) : LamTerm :=
  manyBindersAux n 0
where
  manyBindersAux (n : Nat) (idx : Nat) :=
    match n with
    | 0 => manyApp (.atom 0) idx
    | n' + 1 => .lam (.atom 0) (manyBindersAux n' (Nat.succ idx))
  manyApp (t : LamTerm) : (idx : Nat) → LamTerm
  | 0 => t
  | n' + 1 => .app (.atom 0) (manyApp t n') (.bvar n')

-- **Succeeds in a reasonable amount of time**
set_option maxRecDepth 10000 in
set_option lazyReduce.logInfo false in
#lazyReduce manyBinders 3000

def wfManyBinders (narg : Nat) := @LamWF.ofLamCheck?
  (ltv := {(Inhabited.default : LamTyVal) with
    lamVarTy := fun n => if n == 0 then manyArgFuncTy narg 0 else .atom 0})
  (lctx := fun _ => .atom 0)
  (t := manyBinders narg)
  (ty := manyArgFuncTy narg 0)

def wfManyBinders' (narg : Nat) := LamWF.ofLamTerm
  (ltv := {(Inhabited.default : LamTyVal) with
    lamVarTy := fun n => if n == 0 then manyArgFuncTy narg 0 else .atom 0})
  (lctx := fun _ => .atom 0) (manyBinders narg)

-- **Succeeds in a reasonable amount of time**
#lazyReduce wfManyBinders' 20
set_option lazyReduce.logInfo false in
set_option lazyReduce.printTime true in
set_option maxRecDepth 4000 in
#lazyReduce wfManyBinders' 200

def wfManyBindersRfl (narg : Nat) H :=
  Option.some ⟨manyArgFuncTy narg 0, wfManyBinders narg H⟩ =
    wfManyBinders' narg

-- **Does not succeed in a reasonable amount of time**
set_option lazyReduce.logInfo false in
set_option lazyReduce.printTime true in
set_option maxRecDepth 2000 in
set_option maxHeartbeats 20000000 in
#reduce (wfManyBinders 50 rfl)
-- #eval (wfManyBinders 20 rfl)
-- Reduce 50  => 3369 ms
-- Reduce 100 => 17426 ms
-- Reduce 200 => 116007 ms

#check LamWF.ofLamTerm

set_option lazyReduce.printTime true
set_option maxRecDepth 50000 in
#lazyReduce List.map (fun n => (List.range (1000 + n)).length) (List.range 10)

set_option maxRecDepth 50000 in
#lazyReduce (List.range 10000).length