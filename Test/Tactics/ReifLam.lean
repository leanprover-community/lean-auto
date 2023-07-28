import Auto.Translation.ReifLam
import Auto.Util.ExprExtra

open Auto.ReifLam

#print LamWF.subst

-- (.atom k) → (.atom k) → ⋯ → (.atom k) → (.atom k)
def manyArgFuncTy (n : Nat) (k : Nat) : LamSort :=
  match n with
  | 0 => .atom k
  | n' + 1 => .func (.atom k) (manyArgFuncTy n' k)

-- **Succeeds in a reasonable amount of time**
-- #reduce manyArgFuncTy 300 0
-- set_option maxRecDepth 2000 in
-- #reduce LamSort.beq_eq (manyArgFuncTy 100 40) (manyArgFuncTy 100 40)

-- λ (x₁ x₂ ... xₙ : (.atom 0)) . (.atom 0) x₁ x₂ ... xₙ
-- Note that the first `.atom 0` is a sort atom, while the
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
  | n' + 1 => .app (manyApp t n') (.bvar n')

-- **Succeeds in a reasonable amount of time**
-- #reduce manyBinders 20

def wfManyBinders (narg : Nat) := @LamTerm.lamWF_of_check
  (lamVarTy := fun n => if n == 0 then manyArgFuncTy narg 0 else .atom 0)
  (lctx := fun _ => .atom 0)
  (t := manyBinders narg)
  (ty := manyArgFuncTy narg 0)

-- **Does not succeed in a reasonable amount of time**
-- set_option lazyReduce.logInfo false in
-- set_option lazyReduce.printTime true in
-- set_option maxRecDepth 2000 in
-- set_option maxHeartbeats 20000000 in
-- #lazyReduce wfManyBinders 2 rfl
-- 50  => 3369 ms
-- 100 => 17426 ms
-- 200 => 116007 ms
#eval LamTerm.check (fun n => if (n == 0) = true then manyArgFuncTy 1 0 else LamSort.atom 0) (fun x => LamSort.atom 0)
      (manyBinders 1)

-- #reduce @LamTerm.lamWF_of_check
--   (lamVarTy := fun n => if n == 0 then )
--   (lctx := fun _ => .atom 0)
--   (t := .atom 0)
--   (ty := .atom 0)
--   rfl