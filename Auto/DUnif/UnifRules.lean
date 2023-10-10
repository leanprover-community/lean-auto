import Lean
import Auto.DUnif.UnifProblem
import Auto.DUnif.Bindings
import Auto.DUnif.Oracles
import Auto.Lib.ExprExtra
import Auto.Lib.MetaExtra
open Lean

-- TODO
-- 1: How to deal with `mdata`?
-- 2: Find out whether we need to consider metavariables of
--    different depth to be rigid. (Anyway, we need to prevent
--    us from assigning the metavariables that are assumed to
--    be synthesized by typeclass resolution)
-- 3: Propositional extensionality
-- 4: Whether to use `headBeta` or `whnf`

namespace Auto.DUnif

structure Config where
  contains    : Nat
  iterationOn : Bool

-- Given expression `e = λ [x]. ∀ [y], body`, return
-- 1. An expression, `λ [x] [y]. body`
-- 2. An option expression, the sort of `body`, if `body` is not `forall ...`
-- 3. An array
--    `λ [x]. λ y₁ y₂ ⋯ yₖ. type(yₖ₊₁)` for `k = 0, 1, ⋯, n-1`
def exprForallToLambda (e : Expr) (n : Nat) : MetaM (Expr × (Option Expr) × Array Expr) :=
  Meta.lambdaTelescope e fun xs e' => Meta.forallBoundedTelescope e' n fun ys body => do
    -- Do not unify sort if `body` begins with `forallE`
    -- This is because that `forall` will later be transformed to
    -- `lambda` and the binder's type and sort will be unified. Finally
    -- when the body does not begin with `lambda`, it's sort will be
    -- unified.
    let sort :=
      if let .forallE _ _ _ _ := body then
        none
      else
        some (← Meta.inferType body)
    let mut retarr := #[]
    let mut prev := #[]
    for y in ys do
      let yty ← Meta.inferType y
      retarr := retarr.push (← Meta.inferType yty)
      retarr := retarr.push (← Meta.mkLambdaFVars (xs ++ prev) yty)
      prev := prev.push y
    let e' ← Meta.mkLambdaFVars (xs ++ prev) body
    return (e', sort, retarr)

def exprPairForallToLambda (e₁ : Expr) (e₂ : Expr) (n : Nat) : MetaM (Option UnifEq × Array UnifEq) :=
  Meta.lambdaTelescope e₁ fun xs₁ e₁' => Meta.forallBoundedTelescope e₁' n fun ys₁ body₁ =>
    Meta.lambdaTelescope e₂ fun xs₂ e₂' => Meta.forallBoundedTelescope e₂' n fun ys₂ body₂ => do
      if ys₁.size != n || ys₂.size != n then
        throwError "exprPairForallToLambda :: Incorrect number of foralls"
      let sort₁ ← Meta.inferType body₁
      let sort₂ ← Meta.inferType body₂
      let mut retarr : Array UnifEq := #[]
      let mut prev₁ := #[]
      let mut prev₂ := #[]
      for i in [0:n] do
        let y₁ := ys₁[i]!
        let y₂ := ys₂[i]!
        let yty₁ ← Meta.inferType y₁
        let yty₂ ← Meta.inferType y₂
        let ysort₁ ← Meta.inferType yty₁
        let ysort₂ ← Meta.inferType yty₂
        if ysort₁ != ysort₂ then
          retarr := retarr.push (.fromExprPair ysort₁ ysort₂)
        if yty₁ != yty₂ then
          let absty₁ ← Meta.mkLambdaFVars (xs₁ ++ prev₁) yty₁
          let absty₂ ← Meta.mkLambdaFVars (xs₂ ++ prev₂) yty₂
          retarr := retarr.push (.fromExprPair absty₁ absty₂)
        prev₁ := prev₁.push y₁
        prev₂ := prev₂.push y₂
      if body₁ != body₂ then
        let abstb₁ ← Meta.mkLambdaFVars (xs₁ ++ prev₁) body₁
        let abstb₂ ← Meta.mkLambdaFVars (xs₂ ++ prev₂) body₂
        retarr := retarr.push (.fromExprPair abstb₁ abstb₂)
      let sorteq :=
        if let .forallE _ _ _ _ := body₁ then
          none
        else
          if let .forallE _ _ _ _ := body₂ then
            none
          else
            UnifEq.fromExprPair sort₁ sort₂
      return (sorteq, retarr)

@[inline] partial def derefNormType (e : Expr) : MetaM (Expr × Bool) :=
  Meta.forallTelescope e fun xs' body => do
    let body ← Meta.whnf body
    let fn := Expr.getAppFn body
    let e' ← Meta.mkForallFVars xs' body
    if let .mvar _ := fn then
      return (e', true)
    else
      return (e', false)

-- Dereference head and normalize, assuming that `e` has been eta expanded
-- Return: (processed expression, is_flex)
@[inline] partial def derefNormTerm (e : Expr) : MetaM (Expr × Bool) :=
  Meta.lambdaTelescope e fun xs' body => do
    let body ← Meta.whnf body
    let fn := Expr.getAppFn body
    match fn with
    | .mvar _ => do
      let e' ← Meta.mkLambdaFVars xs' body
      return (e', true)
    | .forallE _ _ _ _  => do
      -- type can't be applied
      if body.getAppNumArgs != 0 then
        trace[auto.dunif.debug] "Type {fn} is applied to arguments in {body}"
      let (body, flex) ← derefNormType fn
      let e' ← Meta.mkLambdaFVars xs' body
      return (e', flex)
    | _ => do
      let e' ← Meta.mkLambdaFVars xs' body
      return (e', false)

def derefNormEq (u : UnifEq) : MetaM UnifEq := do
  let mut lhs' := u.lhs
  let mut lflex' := u.lflex
  if u.lflex then
    let n ← derefNormTerm (← Meta.etaExpand u.lhs)
    lhs' := n.fst
    lflex' := n.snd
  let mut rhs' := u.rhs
  let mut rflex' := u.rflex
  if u.rflex then
    let n ← derefNormTerm (← Meta.etaExpand u.rhs)
    rhs' := n.fst
    rflex' := n.snd
  -- avoid left-rigid right-flex
  if ¬ lflex' ∧ rflex' then
    return {lhs := rhs', lflex := rflex', rhs := lhs', rflex := lflex'}
  else 
    return {lhs := lhs', lflex := lflex', rhs := rhs', rflex := rflex'}

def derefNormProblem (p : UnifProblem) : MetaM UnifProblem := do
  setMCtx p.mctx
  let mut p := p
  if ¬ p.prioritized.isEmpty then
    let top := p.prioritized.back
    let pr' := p.prioritized.pop
    let checked ← derefNormEq top
    return {p with prioritized := pr'.push checked, mctx := ← getMCtx, checked := false}
  if p.checked then
    return p
  let mut rigidrigid' := p.rigidrigid
  let checked ← (p.flexrigid ++ p.flexflex).mapM derefNormEq
  let mut flexrigid' := #[]
  let mut flexflex' := #[]
  for c in checked do
    if ¬ c.lflex ∧ ¬ c.rflex then
      rigidrigid' := rigidrigid'.push c
    else if c.lflex ∧ ¬ c.rflex then
      flexrigid' := flexrigid'.push c
    else
      flexflex' := flexflex'.push c
  return {p with rigidrigid := rigidrigid', flexrigid := flexrigid', flexflex := flexflex',
                 checked := true, mctx := ← getMCtx}

-- This function turns `forall` into `lambda`
-- If there is `forall`, then this is a type unification problem,
--   and it's supposed to be prioritized
def forallToLambda (p : UnifProblem) (eq : UnifEq) (n : Nat) : MetaM (Array UnifProblem) := do
  setMCtx p.mctx
  let (sorteq, arreq) ← exprPairForallToLambda eq.lhs eq.rhs n
  if let some sorteq := sorteq then
    if ¬ (← Meta.isDefEq sorteq.lhs sorteq.rhs) then
      return #[]
  -- Later types depend on previous, so we push in reverse order
  let p := p.appendPrioritized arreq.reverse
  return #[{(← p.pushParentRuleIfDbgOn (.ForallToLambda eq n)) with checked := false, mctx := ← getMCtx}]

-- This function takes care of `Fail` and `Decompose`, and `Delete` of constant pair with level mvars
-- Assumming both sides of `eq` are rigid, or both sides of `eq` are flex
-- If the head is unequal and number of arguments are equal, return `none`
-- If the head is equal and number of arguments are equal, return `none`
def failDecompose (is_prio : Bool) (p : UnifProblem) (eq : UnifEq) : MetaM (Array UnifProblem) := do
  setMCtx p.mctx
  Meta.lambdaTelescope eq.lhs fun xs t => Meta.forallTelescope t fun ts lhs' => do
    -- apply the right-hand-side to `xs`
    let mut p := p
    let n_lam := (Expr.lambdaBinders eq.rhs).size
    let n_red := Nat.min n_lam xs.size
    let rhs_red ← Meta.instantiateLambda eq.rhs (xs.extract 0 n_red)
    let mut rhs' := mkAppN rhs_red (xs.extract n_red xs.size)
    if ts.size != 0 then
      if n_lam != xs.size then
        return #[]
      let n_forall := (Expr.forallBinders rhs').size
      if n_forall != ts.size then
        return #[]
      rhs' ← Meta.instantiateForall rhs' ts
    -- Rule: Fail
    if lhs'.isApp != rhs'.isApp then
      return #[]
    let fl := lhs'.getAppFn
    let fr := rhs'.getAppFn
    -- Rule: Fail
    if fl.isConst ∧ fr.isConst then
      if fl.constName! != fr.constName! then
        return #[]
      -- Unify the levels of the head
      let lfl := (fl.constLevels!).toArray
      let lfr := (fr.constLevels!).toArray
      if lfl.size != lfr.size then
        return #[]
      for i in List.range lfl.size do
        if ¬ (← Meta.isLevelDefEq lfl[i]! lfr[i]!) then
          return #[]
    else if fl.isSort ∧ fr.isSort then
      -- Unify levels
      let lfl := fl.sortLevel!
      let lfr := fr.sortLevel!
      if ¬ (← Meta.isLevelDefEq lfl lfr) then
        return #[]
    else if fl.isProj ∧ fr.isProj then
      if fl.projIdx! != fr.projIdx! then
        return #[]
      let el ← Meta.mkLambdaFVars xs (← Meta.mkForallFVars ts fl.projExpr!)
      let er ← Meta.mkLambdaFVars xs (← Meta.mkForallFVars ts fr.projExpr!)
      p := p.pushUnchecked (UnifEq.fromExprPair el er) is_prio
    else
      if fl != fr then
        return #[]
    let argsl := lhs'.getAppArgs
    let argsr := rhs'.getAppArgs
    -- This can happen in, for example,
    -- U : ∀ α, α → α
    -- U Nat 1
    -- U (Nat → Nat) (fun x => x) 1
    if argsl.size != argsr.size then
      return #[]
    let argsl ← (← argsl.mapM (Meta.mkForallFVars ts)).mapM (Meta.mkLambdaFVars xs)
    let argsr ← (← argsr.mapM (Meta.mkForallFVars ts)).mapM (Meta.mkLambdaFVars xs)
    -- Later args may depend on previous args, so we push in
    --   the reverse order.
    let neweqs := (argsl.zip argsr).reverse.map (fun (a, b) => UnifEq.fromExprPair a b)
    p ← (p.appendUnchecked neweqs is_prio).pushParentRuleIfDbgOn (.Decompose eq)
    -- Does not assign ExprMVars, so no need to set `Checked = False`
    return #[{p with mctx := ← getMCtx}]

-- All rules set the `mctx` as the `mctx` of problem `p` upon entry, and
--   might modify the `mctx`. So, `applyRules` should be run with
--   `withoutModifyingMCtx`
-- The argument "print" is for debugging. Only problems whose parentClause
--   contains "print" will be printed
def applyRules (p : UnifProblem) (config : Config) : MetaM UnifRuleResult := do
  let mut p := p
  if ¬ p.checked ∨ ¬ p.prioritized.isEmpty then
    p ← derefNormProblem p
  -- debug
  -- To make messages print, we set `mctx` to that of `p`'s
  setMCtx p.mctx
  -- If `dUnifDbg` is off, then we can't check `contains` because we don't push parent clause
  if ¬ (← getDUnifDbgOn) ∨ p.parentClauses.toList.contains config.contains then
    Meta.withoutMVarAssignments <| do trace[auto.dunif.debug] m!"{(← p.instantiateTrackedExpr).dropParentRulesButLast 8}"
  let is_prio : Bool := ¬ p.prioritized.isEmpty
  if let some (eq, p') := p.pop? then
    let (lh, lhtype) ← structInfo p eq.lhs
    let (rh, rhtype) ← structInfo p eq.rhs
    if let .Other _ _ _ := lhtype then
      trace[auto.dunif.debug] m!"applyRule :: Type of head is `Other`"
    if let .Other _ _ _ := rhtype then
      trace[auto.dunif.debug] m!"applyRule :: Type of head is `Other`"
    if eq.lflex != lhtype.isFlex then
      trace[auto.dunif.debug] m!"applyRule :: Flex-rigid-cache mismatch in lhs of {eq}"
      return .NewArray #[]
    if eq.rflex != rhtype.isFlex then
      trace[auto.dunif.debug] m!"applyRule :: Flex-rigid-cache mismatch in rhs of {eq}"
      return .NewArray #[]
    -- Delete, except for term pairs containing constants with
    --   unifiable but unequal level mvars
    if eq.lhs == eq.rhs then
      let p' ← p'.pushParentRuleIfDbgOn (.Delete eq)
      return .NewArray #[p']
    -- If both sides have `forall`, then turn `forall` into `lambda`
    let (ll, lf) := lhtype.getLambdaForall
    let (rl, rf) := rhtype.getLambdaForall
    if lf != 0 ∧ rf != 0 then
      if ll != rl then
        return .NewArray #[]
      -- Same number of lambdas
      let f2l ← forallToLambda p' eq (Nat.min lf rf)
      return .NewArray f2l
    -- Fail, Decompose
    -- If head type are both rigid
    if ¬ eq.lflex ∧ ¬ eq.rflex then
      let urr ← failDecompose is_prio p' eq
      return .NewArray urr
    -- Following: OracleSucc
    -- Instantiation oracle: One of `lhs` or `rhs` is a metavariable
    if let some up ← oracleInst p' eq then
      return .NewArray #[up]
    -- OccursCheck oracle: One of `lhs` or `rhs` is a metavariable
    if (← oracleOccurs p' eq) then
      return .NewArray #[]
    -- Following: Bind
    -- Left flex, Right rigid
    if eq.lflex ∧ ¬ eq.rflex then
      -- Imitation of `forall`. We imitate `forall` one at a time
      if lf != 0 then
        -- rf must be `0`, otherwise we would have returned
        --   in `if lf != 0 ∧ rf != 0 then`.
        -- So it's too much `forall` on the `flex` side.
        return .NewArray #[]
      let mut ret := #[]
      if rf != 0 then
        -- lf must be `0`
        ret := ret.append (← DUnif.imitForall lh p eq)
      if let .Proj nLam _ _ iTy oTy name idx := rhtype then
        ret := ret.append (← DUnif.imitProj lh nLam iTy oTy name idx p eq)
      if let .Const _ _ _ := rhtype then
        ret := ret.append (← DUnif.imitation lh rh p eq)
      if ¬ p.identVar.contains lh then
        ret := ret.append (← DUnif.huetProjection lh p eq)
      return .NewArray ret
    -- Left flex, Right flex
    -- Heads are different
    if lh != rh then
      -- Iteration for both lhs and rhs
      let mut ll ← (do
        if config.iterationOn then
          let liter ← DUnif.iteration lh p eq false
          let riter ← DUnif.iteration rh p eq false
          return LazyList.interleave liter riter
        else
          return LazyList.nil)
      -- Identification
      let mut arr := #[]
      match (← DUnif.identification lh rh p eq) with
      | .NewArray a => arr := arr.append a
      | .NewLazyList l => ll := LazyList.interleave l ll
      | .Succeed => throwError "applyRules :: identification never succeeds"
      -- JP style projection
      if ¬ p.identVar.contains lh then
        arr := arr.append (← DUnif.jpProjection lh p eq)
      if ¬ p.identVar.contains rh then
        arr := arr.append (← DUnif.jpProjection rh p eq)
      return .NewLazyList (.cons (pure arr) ll)
    -- Left flex, Right flex
    -- Heads are the same
    else
      let decomp ← failDecompose is_prio p' eq
      if p.elimVar.contains lh then
        return .NewArray decomp
      -- Iteration at arguments of functional type
      let iters ← (do
        if config.iterationOn then
          DUnif.iteration lh p eq true
        else
          return LazyList.nil)
      -- Eliminations
      let elims ← DUnif.elimination lh p eq
      return .NewLazyList (LazyList.cons (pure decomp) (LazyList.interleave elims iters))
  else
    -- No equations left
    return .Succeed



-- Unifier Generator

inductive QueueElement
| Problem : UnifProblem → QueueElement
| LazyListOfProblem : LazyList (MetaM (Array UnifProblem)) → QueueElement
deriving Inhabited

structure UnifierGenerator where
  q   : Std.Queue QueueElement
  -- Total number of problems generated
  -- This will be used to assign ids to clauses
  N   : Nat
  cfg : Config

-- mctx is not modified. Refer to `UnifProblem.fromExprPairs`
def UnifierGenerator.fromExprPairs (l : Array (Expr × Expr)) (cfg : Config := ⟨0, false⟩) : MetaM UnifierGenerator := do
  let q := Std.Queue.empty
  let unifPrb ← UnifProblem.fromExprPairs l
  if let some prb := unifPrb then
    let prb ← (← prb.pushParentClauseIfDbgOn 0).pushTrackedExprIfDbgOn (l.concatMap (fun (e1, e2) => #[e1, e2]))
    return ⟨q.enqueue (.Problem prb), 1, cfg⟩
  else
    return ⟨q, 0, cfg⟩

-- If the original unifiergenerator represents a unification
-- problem `u`, then after accepting `l = eq₁, eq₂, ..., eqₖ` it becomes
-- the unification problem `u ∨ (eq₁ ∧ eq₂ ∧ ⋯ ∧ eqₖ)`
def UnifierGenerator.acceptExprPairs (l : Array (Expr × Expr)) (ug : UnifierGenerator) : MetaM UnifierGenerator := do
  let unifPrb ← UnifProblem.fromExprPairs l
  if let some prb := unifPrb then
    let prb ← (← prb.pushParentClauseIfDbgOn 0).pushTrackedExprIfDbgOn (l.concatMap (fun (e1, e2) => #[e1, e2]))
    return {ug with q := ug.q.enqueue (.Problem prb)}
  else
    return ug

def UnifierGenerator.isEmpty : UnifierGenerator → Bool
| .mk q _ _ => q.isEmpty

-- The argument "print" is for debugging. Only problems whose parentClause
-- contains "print" will be printed
def UnifierGenerator.take (ug : UnifierGenerator) :
  MetaM (Option UnifProblem × UnifierGenerator) := Meta.withTransparency .reducible do
  let q := ug.q
  let dq := q.dequeue?
  if dq.isNone then
    return (none, ug)
  let (top, q') := dq.get!
  match top with
  | .Problem up => do
    let urr ← withoutModifyingMCtx <| applyRules up ug.cfg
    match urr with
    -- arr : Array UnifProblem
    | .NewArray arr => do
      let mut q' := q'
      let mut cnt := 0
      for a in arr do
        q' := q'.enqueue (.Problem (← a.pushParentClauseIfDbgOn (ug.N + cnt)))
        cnt := cnt + 1
      return (none, ⟨q', ug.N + arr.size, ug.cfg⟩)
    -- ls : LazyList (MetaM (Array UnifProblem))
    | .NewLazyList ls => pure (none, ⟨q'.enqueue (.LazyListOfProblem ls), ug.N, ug.cfg⟩)
    -- b : Bool
    | .Succeed => return (some up, ⟨q', ug.N, ug.cfg⟩)
  | .LazyListOfProblem ls =>
    match ls with
    | .cons arr ls' => do
      let mut q' := q'
      q' := q'.enqueue (.LazyListOfProblem ls')
      let arr ← withoutModifyingMCtx arr
      let mut cnt := 0
      for a in arr do
        q' := q'.enqueue (.Problem (← a.pushParentClauseIfDbgOn (ug.N + cnt)))
        cnt := cnt + 1
      return (none, ⟨q', ug.N + arr.size, ug.cfg⟩)
    | .nil => pure (none, ⟨q', ug.N, ug.cfg⟩)
    | .delayed t => pure (none, ⟨q'.enqueue (.LazyListOfProblem t.get), ug.N, ug.cfg⟩)

def UnifierGenerator.takeWithRetry (ug : UnifierGenerator) (nRetry : Nat) :
  MetaM (Option UnifProblem × UnifierGenerator) := do
  let mut ug := ug
  for _ in List.range nRetry do
    let (ou, ug') ← ug.take
    if let some ou := ou then
      withoutModifyingMCtx <| do
        setMCtx ou.mctx
        trace[auto.dunif.result] "Produced unifier: {ou}"
      return (ou, ug')
    else
      ug := ug'
  return (none, ug)

-- Turning unification procedures (like `isDefEq`) that runs locally in
-- MetaM and that produces at most one unifier into a unifier generator
def UnifierGenerator.fromMetaMProcedure (unif : MetaM Bool) : MetaM UnifierGenerator := withoutModifyingMCtx <| do
  let unifiable ← unif
  if unifiable then
    UnifierGenerator.fromExprPairs #[]
  else
    return ⟨Std.Queue.empty, 0, ⟨0, false⟩⟩

-- For testing
def hounif (e1 e2 : Expr) (nAttempt : Nat) (nUnif : Nat) (ncont : Nat) (iterOn : Bool) : MetaM Bool := do
  let mut ug ← UnifierGenerator.fromExprPairs #[(e1, e2)] ⟨ncont, iterOn⟩
  let mut cnt := 0
  for i in List.range nAttempt do
    if ug.isEmpty then
      trace[Meta.Tactic] "Failed with empty queue after {i} attempts"
      return false
    let (up, ug') ← ug.take
    ug := ug'
    if let some up := up then
      -- if `dUnifDbg` is off, then we do not push
      -- parent clause, and we can't check `contains`
      if (← getDUnifDbgOn) ∧ ¬ up.parentClauses.toList.contains ncont then
        continue
      let mctx := up.mctx
      if cnt == nUnif then
        setMCtx mctx
        trace[Meta.Tactic] "Succeed {up}"
        trace[Meta.Tactic] "Final: {← instantiateMVars e1}, {← instantiateMVars e2}"
        return true
      else
        cnt := cnt + 1
  trace[Meta.Tactic] "Failed because attempt limit has been reached, printing queue elements"
  let mut q := ug.q
  while true do
    match q.dequeue? with
    | some (elem, q') =>
      q := q'
      match elem with
      | .Problem up =>
        Meta.withMCtx up.mctx <| do
          Meta.withoutMVarAssignments <| do trace[Meta.Tactic] "Queue Element: {up}"
          Meta.inspectMVarAssignments
      | .LazyListOfProblem _ => trace[Meta.Tactic] "Lazy List"
    | none => break
  return false

end Auto.DUnif