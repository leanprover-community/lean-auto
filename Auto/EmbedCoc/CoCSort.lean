module

public import Lean
public meta import Lean

public meta section

/-!
# Generating the sorts of the embedded system

The single source of truth for the sorts is a list of universe levels (`CoCLevel`).
The commands below generate the enumeration type of the sorts from it, one
constructor per level, and the functions on sorts, so that adding a sort only means
adding a level. Each command takes the name of the constant it defines.

The constructor of a level is named after it: `prop` for `0`, and otherwise the level
as Lean writes it, but without spaces around `+` and with every argument of `max` and
`imax` that is not a constant or a parameter in parentheses, e.g. `«2»`, `«u»`, `«u+1»`,
`«max (v+1) 2»`, `«imax u (max v 1)»` and `«(max u v)+1»`. Distinct levels get distinct
names. A level must not contain metavariables.

Levels are compared with `Lean.Level.isEquiv`, the check the kernel uses, so the
generated functions agree with Lean's universe arithmetic.

Usage, where the levels must be a `meta def` of type `List Lean.Level`, and each doc
comment is optional and is attached to the generated declaration:
```
meta def CoCLevel : List Lean.Level := [0, 1, .param `u]
/-- ... -/
mkSortType CoCSort from CoCLevel deriving DecidableEq
/-- ... -/
mkSortSucc CoCSort.succ for CoCSort from CoCLevel
/-- ... -/
mkSortJoin CoCSort.join for CoCSort from CoCLevel
/-- ... -/
mkSortMax CoCSortMax from CoCLevel
/-- ... -/
mkSortTy CoCSort.Ty for CoCSort from CoCLevel CoCSortMax
```
-/

namespace Auto.Embedding.CoC

open Lean Elab Command

/--
  `l` as in the name of its constructor, see the module doc, or `none` if `l` contains a
  metavariable. `paren` puts `l` in parentheses unless it is a constant or a parameter,
  as for an argument of `max` and `imax`
-/
private partial def renderLevel (paren : Bool) (l : Level) : Option String := do
  let k := l.getOffset
  -- `s` with the offset `k`, where `atomic` tells whether `s` is a parameter
  let wrap (s : String) (atomic : Bool) :=
    let s := if k == 0 then s else if atomic then s!"{s}+{k}" else s!"({s})+{k}"
    if paren && !(atomic && k == 0) then s!"({s})" else s
  match l.getLevelOffset with
  | .zero     => return toString k
  | .param p  => return wrap p.toString true
  | .max a b  => return wrap s!"max {← renderLevel true a} {← renderLevel true b}" false
  | .imax a b => return wrap s!"imax {← renderLevel true a} {← renderLevel true b}" false
  | _         => none

/-- The name of the constructor of the sort at level `l`, see the module doc -/
def sortCtorName (l : Level) : Option Name :=
  if l.isZero then some `prop else (renderLevel false l).map .mkSimple

private unsafe def evalLevelsUnsafe (levels : Name) : CommandElabM (List Level) := do
  let env ← getEnv
  let some info := env.find? levels
    | throwError "mkSort: unknown constant `{levels}`"
  unless info.type == mkApp (mkConst ``List [.zero]) (mkConst ``Level) do
    throwError "mkSort: `{levels}` has type `{info.type}`, but should be a `List Lean.Level`"
  ofExcept <| env.evalConst (List Level) (← getOptions) levels

/-- The value of the `meta def` `levels : List Lean.Level` -/
@[implemented_by evalLevelsUnsafe]
opaque evalLevels (levels : Name) : CommandElabM (List Level)

/--
  The levels of the `meta def` `levels`, with the names of their constructors. Fails if
  a level has no constructor name, or if two levels are the same
-/
def sortLevels (levels : Name) : CommandElabM (Array (Level × Name)) := do
  let ls := (← evalLevels levels).toArray
  for h : i in [0:ls.size] do
    for h' : j in [i+1:ls.size] do
      if ls[i].isEquiv ls[j] then
        throwError "mkSort: `{levels}` contains the level `{ls[i]}` twice"
  ls.mapM fun l => do
    let some n := sortCtorName l
      | throwError "mkSort: the level `{l}` of `{levels}` contains a metavariable"
    pure (l, n)

/--
  The constructors of the sort type `ind`, paired with the levels of `levels`. Fails
  unless `ind` is the enumeration type that `mkSortType` generates from `levels`
-/
def sortCtors (ind levels : Name) : CommandElabM (Array (Level × Name)) := do
  let ls ← sortLevels levels
  let some (.inductInfo info) := (← getEnv).find? ind
    | throwError "mkSort: `{ind}` is not an inductive type"
  let expected := ls.map fun (_, n) => ind ++ n
  unless info.ctors.toArray == expected do
    throwError "mkSort: the constructors of `{ind}` are {info.ctors}, but `{levels}` asks \
      for {expected.toList}. Generate `{ind}` with `mkSortType {ind} from {levels}`"
  return ls.map fun (l, n) => (l, ind ++ n)

/-- Resolve the sort type `ind` and the levels `levels` of a command, see `sortCtors` -/
def elabSortArgs (ind levels : Ident) : CommandElabM (Array (Level × Name)) := do
  let indName ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo ind
  let levelsName ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo levels
  sortCtors indName levelsName

/-- The constructor among `ctors` of the sort at level `l`, if any -/
def findSortCtor (ctors : Array (Level × Name)) (l : Level) : Option Name :=
  (ctors.find? fun (l', _) => l'.isEquiv l).map (·.2)

/-! ## Closing a set of levels under `max` and `imax` -/

/-- The number of nodes of `l`, which measures how simple it is -/
def levelSize : Level → Nat
  | .succ l              => levelSize l + 1
  | .max a b | .imax a b => levelSize a + levelSize b + 1
  | .zero | .param _ | .mvar _ => 1

/-- The parameters and metavariables of `l`, added to `acc` -/
private def levelAtoms : Level → List Name → List Name
  | .zero,     acc => acc
  | .succ l,   acc => levelAtoms l acc
  | .max a b,  acc | .imax a b, acc => levelAtoms b (levelAtoms a acc)
  | .param p,  acc => if acc.contains p then acc else p :: acc
  | .mvar m,   acc => if acc.contains m.name then acc else m.name :: acc

/--
  The normal form `max c (p₁ + k₁) ... (pₙ + kₙ)` of an `imax`-free level: the
  constant `c`, which is `0` when an offset subsumes it, and the offset of each
  atom, sorted by atom. Two such levels are equal for all values of their atoms iff
  their normal forms are equal.

  `nform` builds the normal form of a level in one case of which atoms are `0`, where
  each other atom `p` stands for `p + 1`. So every offset is at least `1`, which
  `NForm.succ`, `NForm.max` and `NForm.imax` preserve and `NForm.isZero` relies on
-/
private abbrev NForm := Nat × List (Name × Nat)

/-- Merge offsets sorted by atom, keeping the larger offset of an atom in both -/
private def mergeOffsets : List (Name × Nat) → List (Name × Nat) → List (Name × Nat)
  | [], ks' => ks'
  | ks, []  => ks
  | (p, k) :: ks, (p', k') :: ks' =>
    match Name.cmp p p' with
    | .lt => (p, k) :: mergeOffsets ks ((p', k') :: ks')
    | .gt => (p', k') :: mergeOffsets ((p, k) :: ks) ks'
    | .eq => (p, Nat.max k k') :: mergeOffsets ks ks'

private def NForm.norm (nf : NForm) : NForm :=
  if nf.2.any (nf.1 ≤ ·.2) then (0, nf.2) else nf

private def NForm.succ (nf : NForm) : NForm :=
  NForm.norm (nf.1 + 1, nf.2.map fun (p, k) => (p, k + 1))

private def NForm.max (a b : NForm) : NForm :=
  NForm.norm (Nat.max a.1 b.1, mergeOffsets a.2 b.2)

/--
  Whether `nf` is `0`. Every offset is at least `1`, see `NForm`, so a normal form
  with an atom is at least `1` for all values of its atoms, and one without atoms is
  its constant. Hence `nf` is `0` either for all values of its atoms or for none,
  and it is `0` iff it is `(0, [])`
-/
private def NForm.isZero (nf : NForm) : Bool := nf == (0, [])

/-- `imax a b`, which is `0` when `b` is `0` and `max a b` otherwise -/
private def NForm.imax (a b : NForm) : NForm :=
  if b.isZero then (0, []) else a.max b

/--
  The normal form of `l` in the case where the atoms in `zero` are `0` and each
  other atom `p` is `p + 1`. In that case every level is `0` either for all values of
  its atoms or for none, see `NForm.isZero`, so that `imax` reduces to `0` or `max`
-/
private def nform (zero : List Name) : Level → NForm
  | .zero     => (0, [])
  | .succ l   => (nform zero l).succ
  | .max a b  => (nform zero a).max (nform zero b)
  | .imax a b => (nform zero a).imax (nform zero b)
  | .param p  => if zero.contains p then (0, []) else (0, [(p, 1)])
  | .mvar m   => if zero.contains m.name then (0, []) else (0, [(m.name, 1)])

/-- The normal forms of a level in each case of which atoms are `0` -/
private abbrev LevelKey := List NForm

/-- The key of `l` over `atoms`, which determines `l` up to `levelEquiv` -/
private def levelKey (atoms : List Name) (l : Level) : LevelKey :=
  let cases := atoms.foldr (fun p acc => acc ++ acc.map (p :: ·)) [[]]
  cases.map (nform · l)

/--
  Whether `a` and `b` are equal for all values of their parameters. Unlike
  `Lean.Level.isEquiv` this is complete, e.g. `imax u (imax u v)` and `imax u v` are
  equivalent, but the kernel cannot see it
-/
def levelEquiv (a b : Level) : Bool :=
  let atoms := levelAtoms b (levelAtoms a [])
  levelKey atoms a == levelKey atoms b

private structure ClosureState where
  /-- The simplest level found of each class, with its size and key -/
  reps  : Array (Level × Nat × LevelKey) := #[]
  /-- Whether the representative of each class is known to be the simplest -/
  final : Array Bool := #[]
  /-- The class of each key -/
  index : Std.HashMap LevelKey Nat := {}

/--
  Add `l`, of size `size` and key `key`, to its class, as the representative if it
  is the first or the simplest of the class
-/
private def ClosureState.insert (st : ClosureState) (l : Level) (size : Nat) (key : LevelKey) :
    ClosureState :=
  match st.index[key]? with
  | some i =>
    if !st.final[i]! && size < st.reps[i]!.2.1 then
      { st with reps := st.reps.set! i (l, size, key) }
    else st
  | none =>
    { st with reps := st.reps.push (l, size, key), final := st.final.push false,
              index := st.index.insert key st.reps.size }

/-- The class with the simplest representative that is not final yet, the earliest on ties -/
private def ClosureState.next? (st : ClosureState) : Option Nat := Id.run do
  let mut best : Option Nat := none
  for h : i in [0:st.reps.size] do
    if !st.final[i]! then
      if best.all (st.reps[i].2.1 < st.reps[·]!.2.1) then best := some i
  return best

/--
  The closure of `ls` under `max` and `imax`, up to `levelEquiv`, with the simplest
  level (by `levelSize`) of each class, the earliest found on ties. The levels of
  `ls` come first, and the result is finite: in each case of which parameters are
  `0`, a level of the closure is `0` or the `max` of some levels of `ls`.

  The representative of a class is the simplest level of the class that `max` and
  `imax` build from `ls`. A combination is larger than its arguments, so the classes
  are finalized in order of size, as in Knuth's generalization of Dijkstra's
  algorithm: when the simplest class that is not final is finalized, no simpler
  level of it remains to be found, and it is combined with the final classes
-/
partial def maxesClosure (ls : List Level) : List Level :=
  let atoms := ls.foldl (fun acc l => levelAtoms l acc) []
  let rec loop (st : ClosureState) : ClosureState :=
    match st.next? with
    | none   => st
    | some i => Id.run do
      let mut st := { st with final := st.final.set! i true }
      let (a, sa, ka) := st.reps[i]!
      -- The keys of `max` and `imax` are computed from the keys of their arguments.
      -- `b` was finalized before `a`, and comes first, so that on ties the arguments
      -- follow the order of `ls`
      for j in [0:st.reps.size] do
        if st.final[j]! then
          let (b, sb, kb) := st.reps[j]!
          st := st.insert (mkLevelMax b a) (sb + sa + 1) (List.zipWith NForm.max kb ka)
          st := st.insert (mkLevelIMax b a) (sb + sa + 1) (List.zipWith NForm.imax kb ka)
          st := st.insert (mkLevelIMax a b) (sa + sb + 1) (List.zipWith NForm.imax ka kb)
      return loop st
  let st := ls.foldl (init := {}) fun st l => st.insert l (levelSize l) (levelKey atoms l)
  (loop st).reps.toList.map (·.1)

/--
  The levels `ls`, followed by the successors of `ls` that are not among them up to
  `Lean.Level.isEquiv`, e.g. the levels of some sorts and of their types
-/
def withSuccLevels (ls : List Level) : List Level :=
  ls.foldl (init := ls) fun acc l =>
    let l' := mkLevelSucc l
    if acc.any (·.isEquiv l') then acc else acc ++ [l']

/-- The `n` simplest levels of `ls` by `levelSize`, sorted by size, the earliest first on ties -/
def simplestLevels (ls : List Level) (n : Nat) : List Level :=
  (ls.mergeSort fun a b => levelSize a ≤ levelSize b).take n

syntax (name := mkSortTypeCmd)
  (docComment)? "mkSortType " ident " from " ident Lean.Parser.Command.optDeriving : command

/-- Generate the enumeration type `name` with one constructor per level of `levels` -/
elab_rules : command
  | `(command| $[$doc:docComment]? mkSortType $name:ident from $levels:ident
      $deriv:optDeriving) => do
    let levelsName ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo levels
    let ctors ← (← sortLevels levelsName).mapM fun (_, n) =>
      `(Lean.Parser.Command.ctor| | $(mkIdent n):ident)
    elabCommand <| ← `(
      $[$doc:docComment]?
      inductive $name:ident
        $ctors:ctor*
      $deriv:optDeriving)

syntax (name := mkSortSuccCmd)
  (docComment)? "mkSortSucc " ident " for " ident " from " ident : command

/--
  Generate `name : ind → Option ind`, which maps the sort `Sort s` to the sort
  `Sort (s + 1)` of its type, or to `none` when `s + 1` is not a level of `levels`
-/
elab_rules : command
  | `(command| $[$doc:docComment]? mkSortSucc $name:ident for $ind:ident from $levels:ident) => do
    let ctors ← elabSortArgs ind levels
    let pats ← ctors.mapM fun (_, c) => `($(mkIdent c):ident)
    let rhss ← ctors.mapM fun (l, _) =>
      match findSortCtor ctors (mkLevelSucc l) with
      | some c' => `(some $(mkIdent c'))
      | none    => `(none)
    elabCommand <| ← `(
      $[$doc:docComment]?
      def $name : $ind → Option $ind
        $[| $pats:term => $rhss:term]*)

syntax (name := mkSortJoinCmd)
  (docComment)? "mkSortJoin " ident " for " ident " from " ident : command

/--
  Generate `name : ind → ind → Option ind`, which maps the sorts `Sort s` and `Sort s'`
  to `Sort (imax s s')`, the sort of `∀ x : A, B` where `A : Sort s` and `B : Sort s'`,
  or to `none` when `imax s s'` is not a level of `levels`. Every pair of sorts gets its
  own row, so that the patterns do not overlap
-/
elab_rules : command
  | `(command| $[$doc:docComment]? mkSortJoin $name:ident for $ind:ident from $levels:ident) => do
    let ctors ← elabSortArgs ind levels
    let mut pats := #[]
    let mut pats' := #[]
    let mut rhss := #[]
    for (l, c) in ctors do
      for (l', c') in ctors do
        pats := pats.push (← `($(mkIdent c):ident))
        pats' := pats'.push (← `($(mkIdent c'):ident))
        rhss := rhss.push (← match findSortCtor ctors (mkLevelIMax l l') with
          | some r => `(some $(mkIdent r))
          | none   => `(none))
    elabCommand <| ← `(
      $[$doc:docComment]?
      def $name : $ind → $ind → Option $ind
        $[| $pats:term, $pats':term => $rhss:term]*)

/-- `l` as syntax, in parentheses where needed -/
private def quoteLevel (l : Level) : Syntax.Level :=
  l.quote Parser.maxPrec false fun _ => none

/--
  Elaborate `cmd`, after declaring those of the universe parameters `params` that the
  current scope does not declare yet
-/
private def elabWithUniverses (params : List Name) (cmd : TSyntax `command) :
    CommandElabM Unit := do
  let declared := (← getScope).levelNames
  let fresh := (params.filter (!declared.contains ·)).toArray.map mkIdent
  if fresh.isEmpty then elabCommand cmd
  else elabCommand <| ← `(universe $fresh* in $cmd)

syntax (name := mkSortMaxCmd) (docComment)? "mkSortMax " ident " from " ident : command

/--
  Generate the reducible `name : Type (w + 1) := Type w`, the universe that `mkSortTy`
  lifts the types at the levels of `levels` into. `w` is the normalized `max` of the
  levels, so that the kernel sees that it subsumes each of them, and it lists every
  `imax` among them, since the kernel never removes an `imax` from a `max`. The level
  parameters of `levels` become universe parameters, unless the current scope already
  declares them. They occur only in `max`es, so `linter.checkUnivs` warns, and should
  be disabled at the call site
-/
elab_rules : command
  | `(command| $[$doc:docComment]? mkSortMax $name:ident from $levels:ident) => do
    let levelsName ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo levels
    let ls := (← sortLevels levelsName).map (·.1)
    let w := (ls.foldl (init := Level.zero) mkLevelMax').normalize
    let params := (ls.foldl (fun acc l => levelAtoms l acc) []).reverse
    elabWithUniverses params <| ← `(
      $[$doc:docComment]?
      @[reducible] def $name : Type $(quoteLevel (mkLevelSucc w)) := Type $(quoteLevel w))

/--
  The universe `w` that the reducible `max : Type (w + 1) := Type w` records, see
  `mkSortMax`, together with the universe parameters of `max`
-/
private def sortMaxLevel (max : Ident) : CommandElabM (Level × List Name) := do
  let maxName ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo max
  let some (.defnInfo info) := (← getEnv).find? maxName
    | throwError "mkSort: `{maxName}` is not a definition"
  let .sort (.succ w) := info.value
    | throwError "mkSort: `{maxName}` is `{info.value}`, but should be `Type w` for a level `w`"
  return (w, info.levelParams)

syntax (name := mkSortTyCmd)
  (docComment)? "mkSortTy " ident " for " ident " from " ident ident : command

/--
  Generate `name : ind → max`, which maps the sort `Sort l` to `ULift.{w} (Sort l)`, the
  types at level `l` lifted into the universe `Type w` that `max` records, see
  `mkSortMax`. Fails unless `w` subsumes every level of `levels`
-/
elab_rules : command
  | `(command| $[$doc:docComment]? mkSortTy $name:ident for $ind:ident from $levels:ident
      $max:ident) => do
    let ctors ← elabSortArgs ind levels
    let (w, params) ← sortMaxLevel max
    for (l, _) in ctors do
      unless (mkLevelMax w l).isEquiv w do
        throwError "mkSortTy: the universe `{w}` of `{max}` does not subsume the level `{l}`"
    let pats ← ctors.mapM fun (_, c) => `($(mkIdent c):ident)
    let rhss ← ctors.mapM fun (l, _) => `(ULift.{$(quoteLevel w)} (Sort $(quoteLevel l)))
    let us := params.toArray.map fun p => quoteLevel (mkLevelParam p)
    elabWithUniverses params <| ← `(
      $[$doc:docComment]?
      def $name : $ind → $max:ident.{$us,*}
        $[| $pats:term => $rhss:term]*)

syntax (name := mkSortElCmd)
  (docComment)? "mkSortEl " ident " for " ident " from " ident ident ident : command

/--
  `mkSortEl name for ind from levels ty max` generates `name : (s : ind) → ty s → max`,
  which maps a type `A : ty s` at level `l` to the type of its elements,
  `GLift.{l, w} A.down`, lifted into the universe `Type w` that `max` records, see
  `mkSortMax` and `mkSortTy`. Fails unless `w + 1` subsumes every level of `levels`
-/
elab_rules : command
  | `(command| $[$doc:docComment]? mkSortEl $name:ident for $ind:ident from $levels:ident
      $ty:ident $max:ident) => do
    let ctors ← elabSortArgs ind levels
    let (w, params) ← sortMaxLevel max
    for (l, _) in ctors do
      unless (mkLevelMax (mkLevelSucc w) l).isEquiv (mkLevelSucc w) do
        throwError "mkSortEl: the universe `{w}` of `{max}` does not subsume the level `{l}`"
    let glift := mkIdent `Auto.Embedding.GLift
    let pats ← ctors.mapM fun (_, c) => `($(mkIdent c):ident)
    let rhss ← ctors.mapM fun _ => `(fun A => $glift:ident.{_, $(quoteLevel w)} (ULift.down A))
    let us := params.toArray.map fun p => quoteLevel (mkLevelParam p)
    elabWithUniverses params <| ← `(
      $[$doc:docComment]?
      def $name : (s : $ind) → $ty:ident.{$us,*} s → $max:ident.{$us,*}
        $[| $pats:term => $rhss:term]*)

syntax (name := mkSortCodeCmd)
  (docComment)? "mkSortCode " ident " for " ident " from " ident " : " term : command

/--
  `mkSortCode name for ind from levels : type` generates `name : type`, which maps the
  sort `Sort l` to `⟨Sort l⟩`, i.e. to `Sort l` as an element of its type, e.g. for
  `type := (s : ind) → ty s.sortOf`
-/
elab_rules : command
  | `(command| $[$doc:docComment]? mkSortCode $name:ident for $ind:ident from $levels:ident :
      $type:term) => do
    let ctors ← elabSortArgs ind levels
    let pats ← ctors.mapM fun (_, c) => `($(mkIdent c):ident)
    let rhss ← ctors.mapM fun (l, _) => `(⟨Sort $(quoteLevel l)⟩)
    elabCommand <| ← `(
      $[$doc:docComment]?
      def $name : $type
        $[| $pats:term => $rhss:term]*)

/-- `l + k` -/
private def levelAddOffset (l : Level) (k : Nat) : Level := k.repeat mkLevelSucc l

/-- The offset of `mkSortMap`: the target level is the source level plus or minus `k` -/
syntax sortOffset := (" + " num) <|> (" - " num)

syntax (name := mkSortMapCmd)
  (docComment)? "mkSortMap " ident " : " term " from " ident ident (sortOffset)? : command

/--
  `mkSortMap name : A → B from levelsA levelsB` generates `name : A → B`, which maps the
  sort at level `l` to the sort of `B` at level `l`, where `A` and `B` are the sort types
  generated from `levelsA` and `levelsB`. With `+ k`, the image is at level `l + k`, and
  with `- k`, it is at the level whose `+ k` is `l`. A map `A → Option B` sends a sort
  without an image to `none`, and a map `A → B` fails on it
-/
elab_rules : command
  | `(command| $[$doc:docComment]? mkSortMap $name:ident : $type:term from $la:ident
      $lb:ident $[$off:sortOffset]?) => do
    let (a, b, isPartial) ← match type with
      | `($a:ident → Option $b:ident) => pure (a, b, true)
      | `($a:ident → $b:ident)        => pure (a, b, false)
      | _ => throwErrorAt type "mkSortMap: the type should be `A → B` or `A → Option B`"
    -- Quotation patterns do not tell atoms apart, so the sign is read off the syntax,
    -- a `group` of the sign and the number
    let (k, up) := match off with
      | none     => (0, true)
      | some off => (off.raw[0][1].toNat, off.raw[0][0].getAtomVal == "+")
    let src ← elabSortArgs a la
    let tgt ← elabSortArgs b lb
    let pats ← src.mapM fun (_, c) => `($(mkIdent c):ident)
    let rhss ← src.mapM fun (l, c) => do
      let image := if up then findSortCtor tgt (levelAddOffset l k)
        else (tgt.find? fun (t, _) => (levelAddOffset t k).isEquiv l).map (·.2)
      match image, isPartial with
      | some c', false => `($(mkIdent c'):ident)
      | some c', true  => `(some $(mkIdent c'))
      | none,    true  => `(none)
      | none,    false => throwError "mkSortMap: `{c}` has no image in `{b}`"
    elabCommand <| ← `(
      $[$doc:docComment]?
      def $name : $type
        $[| $pats:term => $rhss:term]*)

end Auto.Embedding.CoC
