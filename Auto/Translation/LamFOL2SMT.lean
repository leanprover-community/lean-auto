import Lean
import Auto.Embedding.LamChecker
import Auto.IR.SMT
import Auto.Solver.SMT
import Auto.Translation.LamUtils
open Lean

initialize
  registerTraceClass `auto.lamFOL2SMT
  registerTraceClass `auto.lamFOL2SMT.nameSuggestion

-- LamFOL2SMT : First-order fragment of simply-typed lambda calculus to SMT IR

namespace Auto

-- Open `Lam`
open Embedding.Lam
-- Open `SMT`
open IR.SMT

namespace SMT

/-- High-level construct -/
private inductive LamAtomic where
  /- Sort atom -/
  | sort     : Nat → LamAtomic
  /- Term atom -/
  | term     : Nat → LamAtomic
  | etom     : Nat → LamAtomic
  /-
    · To SMT solvers `.bvofNat` is the same as `.bvofInt`
    · `.bvtoInt` can be defined using `.bvtoNat`
  -/
  | bvOfNat  : Nat → LamAtomic
  | bvToNat  : Nat → LamAtomic
  | compCtor : LamTerm → LamAtomic
  | compProj : LamTerm → LamAtomic
deriving Inhabited, Hashable, BEq

private def LamAtomic.toString : LamAtomic → String
| .sort n     => s!"sort {n}"
| .term n     => s!"term {n}"
| .etom n     => s!"etom {n}"
| .bvOfNat n  => s!"bvOfNat {n}"
| .bvToNat n  => s!"bvToNat {n}"
| .compCtor t => s!"compCtor {t}"
| .compProj t => s!"compProj {t}"

instance : ToString LamAtomic where
  toString := LamAtomic.toString

instance : Ord LamAtomic where
  compare := fun x y => instOrdString.compare s!"{x}" s!"{y}"

/-- selectorInfo contains:
    - The name of the selector
    - Whether the selector is a projection
    - The constructor that the selector is for
    - The index of the argument that it is selecting
    - The name of the SMT datatype that the selector is for (i.e. the name of the input type)
    - The LamSort of the SMT datatype that the selector is for (i.e. the input type)
    - The output type of the selector (full type is an arrow type that takes in
      a datatype and returns the output type) -/
abbrev SelectorInfo := String × Bool × LamAtomic × Nat × String × LamSort × LamSort

def LamAtomic.toLeanExpr
  (tyValMap varValMap etomValMap : Std.HashMap Nat Expr)
  (atomic : LamAtomic) : MetaM Expr:=
  match atomic with
  | .sort n => do
    let .some e := tyValMap.get? n
      | throwError "{decl_name%} :: Unknown sort atom {n}"
    return e
  | .term n => do
    let .some e := varValMap.get? n
      | throwError "{decl_name%} :: Unknown term atom {n}"
    return e
  | .etom n => do
    let .some e := etomValMap.get? n
      | throwError "{decl_name%} :: Unknown etom {n}"
    return e
  | .bvOfNat n => do
    let e := Expr.app (.const ``BitVec.ofNat []) (.lit (.natVal n))
    return e
  | .bvToNat n => do
    let e := Expr.app (.const ``BitVec.toNat []) (.lit (.natVal n))
    return e
  | .compCtor t => do
    let e ← Lam2D.interpLamTermAsUnlifted tyValMap varValMap etomValMap 0 t
    return e
  | .compProj t => do
    let e ← Lam2D.interpLamTermAsUnlifted tyValMap varValMap etomValMap 0 t
    return e

structure SMTNamingInfo where
  tyVal     : Array (Expr × Level)
  varVal    : Array (Expr × LamSort)
  lamEVarTy : Array LamSort

def SMTNamingInfo.exprToSuggestion (e : Expr) : MetaM String := do
    let ppSyntax := (← PrettyPrinter.delab e).raw
    return toString (← PrettyPrinter.formatTerm ppSyntax)

def SMTNamingInfo.suggestNameForSort (sni : SMTNamingInfo) (s : LamSort) := do
  let suggestion := ((← go s).take 1).toLower
  trace[auto.lamFOL2SMT.nameSuggestion] "`{suggestion}` for LamSort `{s}`"
  return suggestion
where
  go : LamSort → MetaM String
  | .atom n => do
    let .some (e, _) := sni.tyVal[n]?
      | throwError "{decl_name%} :: Unexpected sort atom {repr (LamSort.atom n)}"
    exprToSuggestion e
  | .base b => return b.toString
  -- Suggest name based on return type
  | .func _ argTy => go argTy

def SMTNamingInfo.suggestNameForAtomic (sni : SMTNamingInfo) (a : LamAtomic) : MetaM String := do
  let suggestion ← go a
  trace[auto.lamFOL2SMT.nameSuggestion] "`{suggestion}` for LamAtomic `{a}`"
  return suggestion
where
  go : LamAtomic → MetaM String
  | .sort n => do
    let .some (e, _) := sni.tyVal[n]?
      | throwError "{decl_name%} :: Unexpected sort atom {repr (LamSort.atom n)}"
    exprToSuggestion e
  | .term n => do
    let .some (e, _) := sni.varVal[n]?
      | throwError "{decl_name%} :: Unexpected term atom {repr (LamTerm.atom n)}"
    exprToSuggestion e
  | .etom n => return s!"sk{n}"
  | .bvOfNat n => exprToSuggestion (Expr.app (.const ``BitVec.ofNat []) (.lit (.natVal n)))
  | .bvToNat n => exprToSuggestion (Expr.app (.const ``BitVec.toNat []) (.lit (.natVal n)))
  -- **TODO**
  | .compCtor _ => return "cC"
  -- **TODO**
  | .compProj _ => return "cP"

private def lamBaseSort2SSort : LamBaseSort → SSort
| .prop   => .app (.symb "Bool") #[]
| .bool   => .app (.symb "Bool") #[]
-- `Nat ≅ {x : Int | x ≥ 0}`
| .nat    => .app (.symb "Int") #[]
| .int    => .app (.symb "Int") #[]
| .isto0 p =>
  match p with
  | .xH => .app (.symb "String") #[]
  | .xO .xH => .app (.symb "Empty") #[]
  | _   => .app (.symb "Empty") #[]
| .bv n   => .app (.indexed "BitVec" #[.inr n]) #[]

private def lamSortAtom2String (sni : SMTNamingInfo) (n : Nat) : TransM LamAtomic LamSort String := do
  if !(← hIn (.sort n)) then
    let name ← h2Symb (.sort n) (← sni.suggestNameForAtomic (.sort n))
    addCommand (.declSort name 0)
  return ← h2Symb (.sort n) .none

private def lamSort2SSortAux (sni : SMTNamingInfo) : LamSort → TransM LamAtomic LamSort SSort
| .atom n => do return .app (.symb (← lamSortAtom2String sni n)) #[]
| .base b => return lamBaseSort2SSort b
| .func _ _ => throwError "{decl_name%} :: Unexpected error. Higher order input?"

/-- Only translates first-order types -/
private def lamSort2SSort (sni : SMTNamingInfo) : LamSort → TransM LamAtomic LamSort (List SSort × SSort)
| .func argTy resTy => do
  let (smargs, smres) ← lamSort2SSort sni resTy
  let smarg ← lamSort2SSortAux sni argTy
  return (smarg :: smargs, smres)
| s => return ([], ← lamSort2SSortAux sni s)

mutual
  /-- Assuming `s` either has the form `.atom n` or `.base b`, checks whether `s` has a well-formed constraint
      equivalent to `True`. If it does, then returns `none`. If it doesn't then `defineWfConstraint` creates
      and defines the well-formed constraints corresponding to `s` and all of the types that are mutually inductive
      with it and returns the String name of that `s`'s well-formed constraint.

      If `s` corresponds to a structure or inductive datatype that has been translated to an SMT datatype, then the
      `selInfos?` field is populated and contains the selector information corresponding to the constructors of all
      datatypes that are mutually inductive with `s`.

      If `s` does not correspond to a structure or inductive datatype that has been translated to an SMT datatype, then
      the `selInfos?` field should be `none`. -/
  private partial def defineWfConstraint (sni : SMTNamingInfo) (s : LamSort) (selInfos? : Option (Array SelectorInfo))
    : TransM LamAtomic LamSort (Option String) := do
    trace[auto.lamFOL2SMT] "Calling defineWfConstraint on {s}"
    match s, selInfos? with
    | .atom n, none => return none -- The well-formed predicate for every atom that doesn't correspond to a datatype is `True`
    | .atom _, some selInfos =>
      match h : selInfos.size with
      | 0 => return none -- Datatypes with no selectors are guaranteed to be well-formed
      | _ =>
        -- `wfDatatypeTerms` maps datatype names to their LamSorts and well-formed constraints (each has the form `(x is ctor) => all of ctor's selectors are well-formed`)
        let mut wfDatatypeTerms : Std.HashMap String (LamSort × Array STerm) := Std.HashMap.empty
        -- Gather a list of selector infos for each constructor (organized by datatype)
        let mut ctorInfos : Std.HashMap String (Std.HashMap LamAtomic (List SelectorInfo)) := Std.HashMap.empty
        for selInfo@(selName, selIsProjection, ctor, argIdx, selDatatypeName, selInputType, selOutputType) in selInfos do
          if ctorInfos.contains selDatatypeName then
            if ctorInfos[selDatatypeName]!.contains ctor then
              ctorInfos := ctorInfos.modify selDatatypeName (fun map => map.modify ctor (fun acc => selInfo :: acc))
            else
              ctorInfos := ctorInfos.modify selDatatypeName (fun map => map.insert ctor [selInfo])
          else
            ctorInfos := ctorInfos.insert selDatatypeName (Std.HashMap.empty.insert ctor [selInfo])
        -- Iterate through each constructor to build `wfDatatypeTerms`
        for (selDatatypeName, ctorMap) in ctorInfos do
          for (ctor, ctorSelInfos) in ctorMap do
            let ctorName ← h2Symb ctor none -- `none` should never cause an error since `ctor` should have been given a symbol when the datatype was defined
            let ctorTester : STerm := .testerApp ctorName (.bvar 0) -- `.bvar 0` refers to the element of sort `s` being tested
            let mut wfSelectorTerms : Array STerm := #[]
            let mut ctorDatatypeOpt := none
            for (selName, selIsProjection, _, argIdx, _, selInputType, selOutputType) in ctorSelInfos do
              trace[auto.lamFOL2SMT] "defineWfConstraint :: Examining selector {selName} for datatype {selDatatypeName} which has output type {selOutputType}"
              -- Update `ctorDatatype` (and sanity check to confirm that all selectors connected to ctor have the same datatype)
              match ctorDatatypeOpt with
              | none =>
                ctorDatatypeOpt := some selInputType
              | some ctorDatatype =>
                if ctorDatatype != selInputType then
                  throwError "{decl_name%} :: Constructor {ctor} has selectors for distinct datatypes {ctorDatatype} and {selInputType}"
              -- Check whether `selOutputType` has a nontrivial well-formed constraint
              match ← getWfConstraint sni selOutputType none with
              | some selOutputTypeWfConstraint =>
                wfSelectorTerms := wfSelectorTerms.push $ .qStrApp selOutputTypeWfConstraint #[.qStrApp selName #[.bvar 0]]
              | none => -- `selOutputType` either has a well-formed constraint that is equivalent to `True` or has a constraint that is currently being defined
                match selOutputType with
                | .atom n =>
                  let selOutputTypeName ← h2Symb (.sort n) none
                  -- Check whether `selOutputType` is one of the datatypes whose well-formed constraint is currently being defined
                  if ctorInfos.contains selOutputTypeName then
                    let some selOutputTypeWfConstraint ← h2SymbWf selOutputType $ some ("wf" ++ selOutputTypeName.capitalize)
                      | throwError "{decl_name%} :: h2SymbWf returned none given {s} even though {s} has a nontrivial well-formed predicate"
                    wfSelectorTerms := wfSelectorTerms.push $ .qStrApp selOutputTypeWfConstraint #[.qStrApp selName #[.bvar 0]]
                  else -- `selOutputType` does not correspond to one of the datatypes whose well-formed constraint is being defined, so we can ignore it
                    continue
                | _ => -- `selOutputType` does not correspond to one of the datatypes whose well-formed constraint is being defined, so we can ignore it
                  continue
            let some ctorDatatype := ctorDatatypeOpt
              | throwError "{decl_name%} :: Constructor {ctor} has no selectors but was added to {selDatatypeName}'s ctorMap"
            match h' : wfSelectorTerms.size with
            | 0 =>
              /- For now, we add to `wfDatatypeTerms` even though `(_ is ctor) x => True` is equivalent to `True` to ensure that `wfCstrConjunctions` (which
                  is defined later) contains `selDatatypeName` and `selInputType`. I might refactor in the future to avoid unnecessary vacuous assertions. -/
              if wfDatatypeTerms.contains selDatatypeName then continue -- Don't need to add anything because the only thing we would add is `True`
              else wfDatatypeTerms := wfDatatypeTerms.insert selDatatypeName (ctorDatatype, #[.qStrApp "=>" #[ctorTester, .qStrApp "true" #[]]])
            | 1 =>
              let allSelectorsWf := wfSelectorTerms[0]'(by rw [h']; exact Nat.zero_lt_one)
              if wfDatatypeTerms.contains selDatatypeName then
                wfDatatypeTerms := wfDatatypeTerms.modify selDatatypeName (fun acc => (acc.1, acc.2.push $ .qStrApp "=>" #[ctorTester, allSelectorsWf]))
              else
                wfDatatypeTerms := wfDatatypeTerms.insert selDatatypeName (ctorDatatype, #[.qStrApp "=>" #[ctorTester, allSelectorsWf]])
            | _ =>
              let allSelectorsWf : STerm := .qStrApp "and" wfSelectorTerms
              if wfDatatypeTerms.contains selDatatypeName then
                wfDatatypeTerms := wfDatatypeTerms.modify selDatatypeName (fun acc => (acc.1, acc.2.push $ .qStrApp "=>" #[ctorTester, allSelectorsWf]))
              else
                wfDatatypeTerms := wfDatatypeTerms.insert selDatatypeName (ctorDatatype, #[.qStrApp "=>" #[ctorTester, allSelectorsWf]])
        -- Create `wfCstrConjunctions` from `wfDatatypeTerms`
        let mut wfCstrConjunctions : Array (LamSort × String × STerm) := #[] -- Datatype, datatype name, conjunction of its constructors' well-formed constraints
        for (datatypeName, (datatype, wfTerms)) in wfDatatypeTerms do
          let wfCstrConjunction :=
            if wfTerms.size = 0 then .qStrApp "true" #[]
            else if h' : wfTerms.size = 1 then wfTerms[0]'(by rw [h']; exact Nat.zero_lt_one)
            else .qStrApp "and" wfTerms -- `wfTerms.size ≥ 2`
          wfCstrConjunctions := wfCstrConjunctions.push (datatype, datatypeName, wfCstrConjunction)
        /- Define the well-formed constraints for `s` in terms of `wfCstrConjunctions` (note we must do this even if they are equivalent to `True`)
           because `h2SymbWf` may have been called on the datatypes that appear in `selInfos`. -/
        let dnames ← wfCstrConjunctions.mapM (fun (datatype, _, _) => do disposableName (← sni.suggestNameForSort datatype))
        let wfConstraintNames ← wfCstrConjunctions.mapM (fun (datatype, datatypeName, _) => h2SymbWf datatype $ some ("wf" ++ datatypeName.capitalize))
        let wfConstraintNames ← wfConstraintNames.mapM
          (fun wfConstraintNameOpt =>
            match wfConstraintNameOpt with
            | some wfConstraintName => pure wfConstraintName
            | none => throwError "{decl_name%} :: h2SymbWf returned returned none for one of the datatypes in {selInfos}")
        let mut funDefs : Array (String × Array (String × SSort) × SSort × STerm) := #[]
        for (wfConstraintName, (datatype, datatypeName, wfCstrConjunction)) in wfConstraintNames.zip wfCstrConjunctions do
          funDefs := funDefs.push (wfConstraintName, #[(dnames[0]!, ← lamSort2SSortAux sni datatype)], lamBaseSort2SSort .bool, wfCstrConjunction)
        addCommand (.defFuns funDefs)
        -- Look up the well-formed constraint name corresponding to `s`
        for (wfConstraintName, (datatype, datatypeName, _)) in wfConstraintNames.zip wfCstrConjunctions do
          if datatype == s then
            return some wfConstraintName
        throwError "{decl_name%} :: After defining the well-formed constraints for {selInfos}, failed to find the well-formed constraint name corresponding to {s}"
    | .base .nat, none =>
      let some name ← h2SymbWf s (some "wfNat")
        | throwError "{decl_name%} :: h2SymbWf returned none given {s} even though {s} has a nontrivial well-formed predicate"
      let dname ← disposableName (← sni.suggestNameForSort s)
      addCommand (.defFun false name #[(dname, lamBaseSort2SSort .nat)] (lamBaseSort2SSort .bool) (.qStrApp ">=" #[.bvar 0, .sConst (.num 0)]))
      return some name
    | .base _b, none => return none -- `_b` is not `.nat`, so the well-formed predicate for `.base _b` is `True`
    | .base b, some _ => throwError "{decl_name%} :: Unexpected input for defineWfConstraint. {s} can't both be a base type and a datatype"
    | .func _ _, _ => throwError "{decl_name%} :: Unexpected error encountered: defineWfConstraint was given a .func LamSort"

  /-- Assuming `s` either has the form `.atom n` or `.base b`, returns the well-formed constraint corresponding to `s`.
      If the well-formed constraint corresponding to `s` hasn't been defined, then `getWfConstraint` also adds a command
      to ensure it is defined. If the well-formed constraint corresponding to `s` is equivalent to `True`, then returns `none`.

      If `s` corresponds to a structure or inductive datatype that has been translated to an SMT datatype, then the
      `datatypeSelInfos?` field is populated and contains the selector information corresponding to `s`'s constructors.
      If `s` does not correspond to a structure or inductive datatype that has been translated to an SMT datatype, then
      the `datatypeSelInfos?` field should be `none`. -/
  private partial def getWfConstraint (sni : SMTNamingInfo) (s : LamSort) (datatypeSelInfos? : Option (Array SelectorInfo))
    : TransM LamAtomic LamSort (Option String) := do
    match (← getWfPredicatesMap).get? s with
    | some (some wf_pred) => return some wf_pred
    | some none => return none -- The well-formed constraint corresponding to `s` is equivalent to `True`
    | none =>
      let some wf_pred ← defineWfConstraint sni s datatypeSelInfos?
        | return none -- The well-formed constraint corresponding to `s` is equivalent to `True`
      return some wf_pred

  /-- Adds a well-formed constraint asserting that `name` of sort `s` is well-formed. If `s`'s well-formed constraint is equivalent
      to `True`, then `addWfConstraint` doesn't assert anything. -/
  private partial def addWfConstraint (sni : SMTNamingInfo) (name : String) (s : LamSort) : TransM LamAtomic LamSort Unit := do
    let some resWfConstraint ← getWfConstraint sni s.getResTy none
      | pure () -- If `getWfConstraint` returns `none`, then `s`'s well-formed constraint is equivalent to `True`
    let args ← (Array.mk s.getArgTys).mapM (fun s => do return (s, ← IR.SMT.disposableName (← sni.suggestNameForSort s)))
    let fnApp := .qStrApp name (args.zipIdx.map (fun (_, n) => .bvar (args.size - 1 - n)))
    let mut fnConstr := .qStrApp resWfConstraint #[fnApp]
    for (argTy, argName) in args.reverse do
      match ← getWfConstraint sni argTy none with -- **TODO** Is it always correct to use `none` here?
      | some argWfConstraint =>
        let argWf := .qStrApp argWfConstraint #[.bvar 0]
        fnConstr := .forallE argName (← lamSort2SSortAux sni argTy) $ .qStrApp "=>" #[argWf, fnConstr]
      | none =>
        fnConstr := .forallE argName (← lamSort2SSortAux sni argTy) fnConstr
    addCommand (.assert fnConstr)
end

private def int2STerm : Int → STerm
| .ofNat n   => .sConst (.num n)
| .negSucc n => .qIdApp (QualIdent.ofString "-") #[.sConst (.num (Nat.succ n))]

private def lamBvOfNat2String (sni : SMTNamingInfo) (n : Nat) : TransM LamAtomic LamSort String := do
  if !(← hIn (.bvOfNat n)) then
    let name ← h2Symb (.bvOfNat n) (← sni.suggestNameForAtomic (.bvOfNat n))
    let (argSorts, resSort) ← lamSort2SSort sni (.func (.base .int) (.base (.bv n)))
    addCommand (.declFun name ⟨argSorts⟩ resSort)
  return ← h2Symb (.bvOfNat n) .none

private def lamBvToNat2String (sni : SMTNamingInfo) (n : Nat) : TransM LamAtomic LamSort String := do
  if !(← hIn (.bvToNat n)) then
    let name ← h2Symb (.bvToNat n) (← sni.suggestNameForAtomic (.bvToNat n))
    let (argSorts, resSort) ← lamSort2SSort sni (.func (.base (.bv n)) (.base .int))
    addCommand (.declFun name ⟨argSorts⟩ resSort)
  return ← h2Symb (.bvToNat n) .none

private def bitVec2STerm (n i : Nat) : STerm :=
  let digs := (Nat.toDigits 2 (i % (2^n))).map (fun c => c == '1')
  let digs := (List.range (n - digs.length)).map (fun _ => false) ++ digs
  .sConst (.binary digs)

private def lamBaseTerm2STerm_Arity3 (arg1 arg2 arg3 : STerm) : LamBaseTerm → TransM LamAtomic LamSort STerm
| .scst .srepall => return .qStrApp "str.replace_all" #[arg1, arg2, arg3]
| t              => throwError "{decl_name%} :: The arity of {repr t} is not 3"

private def lamBaseTerm2STerm_Arity2 (arg1 arg2 : STerm) : LamBaseTerm → TransM LamAtomic LamSort STerm
| .pcst .and  => return .qStrApp "and" #[arg1, arg2]
| .pcst .or   => return .qStrApp "or" #[arg1, arg2]
| .pcst .imp  => return .qStrApp "=>" #[arg1, arg2]
| .pcst .iff  => return .qStrApp "=" #[arg1, arg2]
| .bcst .andb => return .qStrApp "and" #[arg1, arg2]
| .bcst .orb  => return .qStrApp "or" #[arg1, arg2]
| .ncst .nadd => return .qStrApp "+" #[arg1, arg2]
| .ncst .nsub => return .qStrApp "nsub" #[arg1, arg2]
| .ncst .nmul => return .qStrApp "*" #[arg1, arg2]
| .ncst .ndiv => return .qStrApp "iediv" #[arg1, arg2]
| .ncst .nmod => return .qStrApp "iemod" #[arg1, arg2]
| .ncst .nle  => return .qStrApp "<=" #[arg1, arg2]
| .ncst .nlt  => return .qStrApp "<" #[arg1, arg2]
| .ncst .nmax => return .qStrApp "ite" #[.qStrApp "<=" #[arg1, arg2], arg2, arg1]
| .ncst .nmin => return .qStrApp "ite" #[.qStrApp "<=" #[arg1, arg2], arg1, arg2]
| .icst .iadd => return .qStrApp "+" #[arg1, arg2]
| .icst .isub => return .qStrApp "-" #[arg1, arg2]
| .icst .imul => return .qStrApp "*" #[arg1, arg2]
| .icst .idiv => return .qStrApp "itdiv" #[arg1, arg2]
| .icst .imod => return .qStrApp "itmod" #[arg1, arg2]
| .icst .iediv => return .qStrApp "iediv" #[arg1, arg2]
| .icst .iemod => return .qStrApp "iemod" #[arg1, arg2]
| .icst .ile  => return .qStrApp "<=" #[arg1, arg2]
| .icst .ilt  => return .qStrApp "<" #[arg1, arg2]
| .icst .imax => return .qStrApp "ite" #[.qStrApp "<=" #[arg1, arg2], arg2, arg1]
| .icst .imin => return .qStrApp "ite" #[.qStrApp "<=" #[arg1, arg2], arg1, arg2]
| .scst .sapp => return .qStrApp "str.++" #[arg1, arg2]
| .scst .sle  => return .qStrApp "str.<=" #[arg1, arg2]
| .scst .slt  => return .qStrApp "str.<" #[arg1, arg2]
| .scst .sprefixof => return .qStrApp "str.prefixof" #[arg1, arg2]
| .bvcst (.bvaOp _ op) =>
  match op with
  | .add => return .qStrApp "bvadd" #[arg1, arg2]
  | .sub => return .qStrApp "bvadd" #[arg1, .qStrApp "bvneg" #[arg2]]
  | .mul => return .qStrApp "bvmul" #[arg1, arg2]
  | .udiv => return .qStrApp "bvudiv" #[arg1, arg2]
  | .urem => return .qStrApp "bvurem" #[arg1, arg2]
  | .sdiv => return .qStrApp "bvsdiv" #[arg1, arg2]
  | .srem => return .qStrApp "bvsrem" #[arg1, arg2]
  | .smod => return .qStrApp "bvsmod" #[arg1, arg2]
| .bvcst (.bvcmp _ _ op) =>
  match op with
  | .ult => return .qStrApp "bvult" #[arg1, arg2]
  | .ule => return .qStrApp "bvule" #[arg1, arg2]
  | .slt => return .qStrApp "bvslt" #[arg1, arg2]
  | .sle => return .qStrApp "bvsle" #[arg1, arg2]
| .bvcst (.bvand _) => return .qStrApp "bvand" #[arg1, arg2]
| .bvcst (.bvor _) => return .qStrApp "bvor" #[arg1, arg2]
| .bvcst (.bvxor _) => return .qStrApp "bvxor" #[arg1, arg2]
| .bvcst (.bvshOp _ smt? op) =>
  match smt? with
  | false =>
    throwError "{decl_name%} :: Non-smt shift operations should not occur here"
  | true =>
    match op with
    | .shl => return .qStrApp "bvshl" #[arg1, arg2]
    | .lshr => return .qStrApp "bvlshr" #[arg1, arg2]
    | .ashr => return .qStrApp "bvashr" #[arg1, arg2]
| .bvcst (.bvappend _ _) => return .qStrApp "concat" #[arg1, arg2]
| .ocst (.smtAttr1T name _ _) => return .attrApp name arg1 arg2
| t           => throwError "{decl_name%} :: The arity of {repr t} is not 2"

private def lamBaseTerm2STerm_Arity1 (sni : SMTNamingInfo) (arg : STerm) : LamBaseTerm → TransM LamAtomic LamSort STerm
| .pcst .not             => return .qStrApp "not" #[arg]
| .bcst .ofProp          => return arg
| .bcst .notb            => return .qStrApp "not" #[arg]
| .icst .iofNat          => return arg
| .icst .inegSucc        => return .qStrApp "-" #[int2STerm (-1), arg]
| .icst .ineg            => return .qStrApp "-" #[int2STerm 0, arg]
| .icst .iabs            => return .qStrApp "abs" #[arg]
| .scst .slength         => return .qStrApp "str.len" #[arg]
-- To SMT solvers `.bvofNat` is the same as `.bvofInt`
| .bvcst (.bvofNat n)    => do
  let name ← solverName
  if name == .z3 || name == .cvc5 then
    return .qIdApp (.ident (.indexed "int2bv" #[.inr n])) #[arg]
  else
    return .qStrApp (← lamBvOfNat2String sni n) #[arg]
| .bvcst (.bvtoNat n)    => do
  let name ← solverName
  if name == .z3 || name == .cvc5 then
    return .qStrApp "bv2nat" #[arg]
  else
    return .qStrApp (← lamBvToNat2String sni n) #[arg]
| .bvcst (.bvofInt n)    => do
  let name ← solverName
  if name == .z3 || name == .cvc5 then
    return .qIdApp (.ident (.indexed "int2bv" #[.inr n])) #[arg]
  else
    return .qStrApp (← lamBvOfNat2String sni n) #[arg]
| .bvcst (.bvtoInt n)    => do
  let name ← solverName
  let msbExpr := mkSMTMsbExpr n arg
  if name == .z3 || name == .cvc5 then
    let arg1 := .qStrApp "-" #[.qStrApp "bv2nat" #[arg], .sConst (.num (2 ^ n))]
    let arg2 := .qStrApp "bv2nat" #[arg]
    return .qStrApp "ite" #[msbExpr, arg1, arg2]
  else
    let arg1 := .qStrApp "-" #[.qStrApp (← lamBvToNat2String sni n) #[arg], .sConst (.num (2 ^ n))]
    let arg2 := .qStrApp (← lamBvToNat2String sni n) #[arg]
    return .qStrApp "ite" #[msbExpr, arg1, arg2]
-- @BitVec.msb n a = not ((a &&& (1 <<< (n - 1))) = 0#n)
| .bvcst (.bvmsb n)      => return mkSMTMsbExpr n arg
| .bvcst (.bvneg _)      => return .qStrApp "bvneg" #[arg]
| .bvcst (.bvabs _)      => return .qStrApp "bvabs" #[arg]
| .bvcst (.bvnot _)      => return .qStrApp "bvnot" #[arg]
| .bvcst (.bvextract _ h l) => do
  let l := min h l
  return .qIdApp (.ident (.indexed "extract" #[.inr h, .inr l])) #[arg]
| .bvcst (.bvrepeat _ i) => return .qIdApp (.ident (.indexed "repeat" #[.inr i])) #[arg]
| .bvcst (.bvzeroExtend w v) =>
  if v ≥ w then
    return .qIdApp (.ident (.indexed "zero_extend" #[.inr (v - w)])) #[arg]
  else
    return .qIdApp (.ident (.indexed "extract" #[.inr (v - 1), .inr 0])) #[arg]
| .bvcst (.bvsignExtend w v) =>
  if v ≥ w then
    return .qIdApp (.ident (.indexed "sign_extend" #[.inr (v - w)])) #[arg]
  else
    return .qIdApp (.ident (.indexed "extract" #[.inr (v - 1), .inr 0])) #[arg]
| t               => throwError "{decl_name%} :: The arity of {repr t} is not 1"
where
  solverName : MetaM Solver.SMT.SolverName := do
    return auto.smt.solver.name.get (← getOptions)
  mkSMTMsbExpr (n : Nat) (arg : STerm) : STerm :=
    let andExpr := .qStrApp "bvand" #[arg, .qStrApp "bvshl" #[bitVec2STerm n 1, bitVec2STerm n (n - 1)]]
    .qStrApp "not" #[.qStrApp "=" #[andExpr, bitVec2STerm n 0]]

private def lamBaseTerm2STerm_Arity0 : LamBaseTerm → TransM LamAtomic LamSort STerm
| .pcst .trueE        => return .qStrApp "true" #[]
| .pcst .falseE       => return .qStrApp "false" #[]
| .bcst .trueb        => return .qStrApp "true" #[]
| .bcst .falseb       => return .qStrApp "false" #[]
| .ncst (.natVal n)   => return .sConst (.num n)
| .scst (.strVal s)   => return .sConst (.str s)
| .bvcst (.bvVal n i) => return bitVec2STerm n i
| t                   => throwError "{decl_name%} :: The arity of {repr t} is not 0"

def lamTermAtom2String (sni : SMTNamingInfo) (lamVarTy : Array LamSort) (n : Nat) : TransM LamAtomic LamSort (LamSort × String) := do
  let .some s := lamVarTy[n]?
    | throwError "{decl_name%} :: Unexpected term atom {repr (LamTerm.atom n)}"
  -- Empty type is not inhabited
  if s == .base .empty then
    addCommand (.assert (.qStrApp "false" #[]))
  if !(← hIn (.term n)) then
    let name ← h2Symb (.term n) (← sni.suggestNameForAtomic (.term n))
    let (argSorts, resSort) ← lamSort2SSort sni s
    addCommand (.declFun name ⟨argSorts⟩ resSort)
    addWfConstraint sni name s
  return (s, ← h2Symb (.term n) .none)

def lamTermEtom2String (sni : SMTNamingInfo) (lamEVarTy : Array LamSort) (n : Nat) : TransM LamAtomic LamSort (LamSort × String) := do
  let .some s := lamEVarTy[n]?
    | throwError "{decl_name%} :: Unexpected etom {repr (LamTerm.etom n)}"
  -- Empty type is not inhabited
  if s == .base .empty then
    addCommand (.assert (.qStrApp "false" #[]))
  if !(← hIn (.etom n)) then
    let name ← h2Symb (.etom n) (← sni.suggestNameForAtomic (.etom n))
    let (argSorts, resSort) ← lamSort2SSort sni s
    addCommand (.declFun name ⟨argSorts⟩ resSort)
    addWfConstraint sni name s
  return (s, ← h2Symb (.etom n) .none)

private def lamTerm2STermAux (sni : SMTNamingInfo) (lamVarTy lamEVarTy : Array LamSort) (args : Array STerm) :
  LamTerm → TransM LamAtomic LamSort STerm
| .atom n => do
  let (s, name) ← lamTermAtom2String sni lamVarTy n
  if args.size != s.getArgTys.length then
    throwError "{decl_name%} :: Argument number mismatch. Higher order input?"
  return .qIdApp (QualIdent.ofString name) args
| .etom n => do
  let (s, name) ← lamTermEtom2String sni lamEVarTy n
  if args.size != s.getArgTys.length then
    throwError "{decl_name%} :: Argument number mismatch. Higher order input?"
  return .qIdApp (QualIdent.ofString name) args
| .base b =>
  match args with
  | #[]           => lamBaseTerm2STerm_Arity0 b
  | #[u₁]         => lamBaseTerm2STerm_Arity1 sni u₁ b
  | #[u₁, u₂]     => lamBaseTerm2STerm_Arity2 u₁ u₂ b
  | #[u₁, u₂, u₃] => lamBaseTerm2STerm_Arity3 u₁ u₂ u₃ b
  | _         => throwError "{decl_name%} :: Argument number mismatch. Higher order input?"
| t => throwError "{decl_name%} :: Unexpected head term {repr t}"

def lamQuantified2STerm (sni : SMTNamingInfo) (forall? : Bool) (s : LamSort) (body : TransM LamAtomic LamSort STerm) : TransM LamAtomic LamSort STerm := do
  -- Empty type is not inhabited
  if s == .base .empty then
    return .qStrApp "true" #[]
  let dname ← disposableName (← sni.suggestNameForSort s)
  let s' ← lamSort2SSortAux sni s
  let mut body' ← body
  if s == .base .nat then
    let connective := if forall? then "=>" else "and"
    body' := .qStrApp connective #[.qStrApp ">=" #[.bvar 0, .sConst (.num 0)], body']
  match forall? with
  | true => return .forallE dname s' body'
  | false => return .existE dname s' body'

private partial def lamTerm2STerm (sni : SMTNamingInfo) (lamVarTy lamEVarTy : Array LamSort) :
  LamTerm → TransM LamAtomic LamSort STerm
| .base b => lamBaseTerm2STerm_Arity0 b
| .bvar n => return .bvar n
| .app _ (.app _ (.base (.eqI _)) _) _ =>
  throwError (decl_name% ++ " :: " ++ LamExportUtils.exportError.ImpPolyLog)
| .app _ (.base (.forallEI _)) (.lam _ _) =>
  throwError (decl_name% ++ " :: " ++ LamExportUtils.exportError.ImpPolyLog)
| .app _ (.base (.existEI _)) (.lam _ _) =>
  throwError (decl_name% ++ " :: " ++ LamExportUtils.exportError.ImpPolyLog)
| .app _ (.app _ (.app _ (.base (.iteI _)) _) _) _ =>
  throwError (decl_name% ++ " :: " ++ LamExportUtils.exportError.ImpPolyLog)
| .app _ (.app _ (.base (.eq _)) arg₁) arg₂ => do
  let arg₁' ← lamTerm2STerm sni lamVarTy lamEVarTy arg₁
  let arg₂' ← lamTerm2STerm sni lamVarTy lamEVarTy arg₂
  return .qIdApp (QualIdent.ofString "=") #[arg₁', arg₂']
| .app _ (.base (.forallE _)) (.lam s body) => do
  lamQuantified2STerm sni true s (lamTerm2STerm sni lamVarTy lamEVarTy body)
| .app _ (.base (.existE _)) (.lam s body) => do
  lamQuantified2STerm sni false s (lamTerm2STerm sni lamVarTy lamEVarTy body)
| .app _ (.app _ (.app _ (.base (.ite _)) cond) arg₁) arg₂ => do
  let cond' ← lamTerm2STerm sni lamVarTy lamEVarTy cond
  let arg₁' ← lamTerm2STerm sni lamVarTy lamEVarTy arg₁
  let arg₂' ← lamTerm2STerm sni lamVarTy lamEVarTy arg₂
  return .qStrApp "ite" #[cond', arg₁', arg₂']
| t => do
  let (ts, t) := splitApp t
  let ts' ← ts.mapM (lamTerm2STerm sni lamVarTy lamEVarTy)
  lamTerm2STermAux sni lamVarTy lamEVarTy ts' t
where
  splitApp : LamTerm → Array LamTerm × LamTerm
  | .app _ fn arg =>
    let (ts, t) := splitApp fn
    (ts.push arg, t)
  | t => (#[], t)

private def lamMutualIndInfo2STerm (sni : SMTNamingInfo) (mind : MutualIndInfo) :
  TransM LamAtomic LamSort (IR.SMT.Command ×
    Array (String × LamSort × LamTerm) ×
    Array (String × LamSort × LamTerm)) := do
  let mut infos := #[]
  let mut compCtors := #[]
  let mut compProjs := #[]
  -- Go through `type` and call `h2Symb` on all the atoms so that there won't
  --   be declared during the following `lamSort2SSort`
  for ⟨type, _, _⟩ in mind do
    let .atom sn := type
      | throwError "{decl_name%} :: Inductive type {type} is not a sort atom"
    -- Do not use `lamSortAtom2String` because we don't want to `declare-sort`
    let _ ← h2Symb (.sort sn) (← sni.suggestNameForAtomic (.sort sn))
  for ⟨type, ctors, projs⟩ in mind do
    let .atom sn := type
      | throwError "{decl_name%} :: Unexpected error"
    let mut projInfos : Array (LamSort × String) := #[]
    if let .some projs := projs then
      if ctors.length != 1 then
        throwError "{decl_name%} :: Unexpected error"
      for (s, t) in projs do
        let mut projname := ""
        match t with
        | .atom n => projname ← h2Symb (.term n) (← sni.suggestNameForAtomic (.term n))
        | .etom n => projname ← h2Symb (.etom n) (← sni.suggestNameForAtomic (.etom n))
        | t       =>
          projname ← h2Symb (.compProj t) (← sni.suggestNameForAtomic (.compProj t))
          compProjs := compProjs.push (projname, s, t)
        projInfos := projInfos.push (s, projname)
    let sname ← h2Symb (.sort sn) .none
    let mut cstrDecls : Array ConstrDecl := #[]
    for (s, t) in ctors do
      let mut ctorname := ""
      match t with
      -- Do not use `lamSortAtom2String` because we don't want to `declare-fun`
      | .atom n => ctorname ← h2Symb (.term n) (← sni.suggestNameForAtomic (.term n))
      -- Do not use `lamSortEtom2String` because we don't want to `declare-fun`
      | .etom n => ctorname ← h2Symb (.etom n) (← sni.suggestNameForAtomic (.etom n))
      | t       =>
        ctorname ← h2Symb (.compCtor t) (← sni.suggestNameForAtomic (.compCtor t))
        compCtors := compCtors.push (ctorname, s, t)
      let (argTys, _) ← lamSort2SSort sni s
      let mut selDecls := #[]
      if projs.isSome then
        if argTys.length != projInfos.size then
          throwError "{decl_name%} :: Unexpected error"
        selDecls := ((Array.mk argTys).zip projInfos).map (fun (argTy, _, name) => (name, argTy))
      else
        selDecls := (Array.mk argTys).zipIdx.map (fun (argTy, idx) =>
          (ctorname ++ s!"_sel{idx}", argTy))
      cstrDecls := cstrDecls.push ⟨ctorname, selDecls⟩
    infos := infos.push (sname, 0, ⟨#[], cstrDecls⟩)
  return (.declDtypes infos, compCtors, compProjs)

/-- Like `lamMutualIndInfo2STerm` but also returns the `infos` passed into the `declDtypes` command
    and a `SelectorInfo` array -/
private def lamMutualIndInfo2STermWithInfos (sni : SMTNamingInfo) (mind : MutualIndInfo) :
  TransM LamAtomic LamSort (IR.SMT.Command ×
    Array (String × LamSort × LamTerm) ×
    Array (String × LamSort × LamTerm) ×
    Array (String × Nat × DatatypeDecl) ×
    Array SelectorInfo) := do
  let mut infos := #[]
  let mut selInfos : Array SelectorInfo := #[]
  let mut compCtors := #[]
  let mut compProjs := #[]
  -- Go through `type` and call `h2Symb` on all the atoms so that there won't
  --   be declared during the following `lamSort2SSort`
  for ⟨type, _, _⟩ in mind do
    let .atom sn := type
      | throwError "lamMutualIndInfo2STerm :: Inductive type {type} is not a sort atom"
    -- Do not use `lamSortAtom2String` because we don't want to `declare-sort`
    let _ ← h2Symb (.sort sn) (← sni.suggestNameForAtomic (.sort sn))
  for ⟨type, ctors, projs⟩ in mind do
    let .atom sn := type
      | throwError "lamMutualIndInfo2STerm :: Unexpected error"
    let mut projInfos : Array (LamSort × String) := #[]
    if let .some projs := projs then
      if ctors.length != 1 then
        throwError "lamMutualIndInfo2STerm :: Unexpected error"
      for (s, t) in projs do
        let mut projname := ""
        match t with
        | .atom n => projname ← h2Symb (.term n) (← sni.suggestNameForAtomic (.term n))
        | .etom n => projname ← h2Symb (.etom n) (← sni.suggestNameForAtomic (.etom n))
        | t       =>
          projname ← h2Symb (.compProj t) (← sni.suggestNameForAtomic (.compProj t))
          compProjs := compProjs.push (projname, s, t)
        projInfos := projInfos.push (s, projname)
    let sname ← h2Symb (.sort sn) .none
    let mut cstrDecls : Array ConstrDecl := #[]
    for (s, t) in ctors do
      trace[auto.lamFOL2SMT] "lamMutualIndInfo2STermWithInfos :: Looking at {t} in ctors"
      trace[auto.lamFOL2SMT] "lamMutualIndInfo2STermWithInfos :: {t} is atom: {t.isAtom}, {t} is etom: {t.isEtom}"
      let mut ctorname := ""
      let mut tAtomic := .compCtor t -- `t` translated to `LamAtomic` (note if `t` is .atom or .etom this will be overwritten)
      match t with
      -- Do not use `lamSortAtom2String` because we don't want to `declare-fun`
      | .atom n =>
        tAtomic := .term n
        ctorname ← h2Symb tAtomic (← sni.suggestNameForAtomic tAtomic)
      -- Do not use `lamSortEtom2String` because we don't want to `declare-fun`
      | .etom n =>
        tAtomic := .etom n
        ctorname ← h2Symb tAtomic (← sni.suggestNameForAtomic tAtomic)
      | t       =>
        tAtomic := .compCtor t
        ctorname ← h2Symb tAtomic (← sni.suggestNameForAtomic tAtomic)
        compCtors := compCtors.push (ctorname, s, t)
      let (argTys, _) ← lamSort2SSort sni s
      let lamSortArgTys := s.getArgTys -- `argTys` as `LamSort` rather than `SSort`
      let mut selDecls := #[]
      if projs.isSome then
        if argTys.length != projInfos.size || lamSortArgTys.length != projInfos.size then
          throwError "lamMutualIndInfo2STerm :: Unexpected error"
        selDecls := ((Array.mk argTys).zip projInfos).map (fun (argTy, _, name) => (name, argTy))
        let selDeclsInfos :=
          ((Array.mk lamSortArgTys).zip projInfos).zipIdx.map
            (fun ((lamSortArgTy, _, name), idx) => (name, true, tAtomic, idx, sname, type, lamSortArgTy))
        selInfos := selInfos ++ selDeclsInfos
      else
        selDecls := (Array.mk argTys).zipIdx.map (fun (argTy, idx) =>
          (ctorname ++ s!"_sel{idx}", argTy))
        let selDeclsInfos :=
          (Array.mk lamSortArgTys).zipIdx.map
            (fun (lamSortArgTy, idx) => (ctorname ++ s!"_sel{idx}", false, tAtomic, idx, sname, type, lamSortArgTy))
        selInfos := selInfos ++ selDeclsInfos
      cstrDecls := cstrDecls.push ⟨ctorname, selDecls⟩
    infos := infos.push (sname, 0, ⟨#[], cstrDecls⟩)
  return (.declDtypes infos, compCtors, compProjs, infos, selInfos)

private def compEqn
  (sni : SMTNamingInfo) (lamVarTy lamEVarTy : Array LamSort)
  (compInfo : String × LamSort × LamTerm) : TransM LamAtomic LamSort IR.SMT.Command := do
  let (name, s, t) := compInfo
  let argTys := s.getArgTys
  let sbvars := (List.range argTys.length).map (fun n => .bvar (argTys.length - 1 - n))
  let slhs := .qStrApp name ⟨sbvars⟩
  let srhs := ← lamTerm2STerm sni lamVarTy lamEVarTy (LamTerm.bvarAppsRev t argTys).headBeta
  let mut eqn := pure (.qStrApp "=" #[slhs, srhs])
  for s in argTys.reverse do
    eqn := lamQuantified2STerm sni true s eqn
  return .assert (← eqn)

def sortAuxDecls : Array IR.SMT.Command :=
  #[.declSort "Empty" 0]

def termAuxDecls : Array IR.SMT.Command :=
  #[.defFun false "nsub" #[("x", .app (.symb "Int") #[]), ("y", .app (.symb "Int") #[])] (.app (.symb "Int") #[])
      (.qStrApp "ite" #[.qStrApp ">=" #[.qStrApp "x" #[], .qStrApp "y" #[]], .qStrApp "-" #[.qStrApp "x" #[], .qStrApp "y" #[]], .sConst (.num 0)]),
    .defFun false "itdiv" #[("x", .app (.symb "Int") #[]), ("y", .app (.symb "Int") #[])] (.app (.symb "Int") #[])
      (.qStrApp "ite" #[.qStrApp "=" #[.qStrApp "y" #[], .sConst (.num 0)], .qStrApp "x" #[],
        .qStrApp "ite" #[.qStrApp ">=" #[.qStrApp "x" #[], .sConst (.num 0)],
          .qStrApp "div" #[.qStrApp "x" #[], .qStrApp "y" #[]],
          .qStrApp "-" #[.qStrApp "div" #[.qStrApp "-" #[.qStrApp "x" #[]], .qStrApp "y" #[]]]]]),
    .defFun false "itmod" #[("x", .app (.symb "Int") #[]), ("y", .app (.symb "Int") #[])] (.app (.symb "Int") #[])
      (.qStrApp "ite" #[.qStrApp "=" #[.qStrApp "y" #[], .sConst (.num 0)], .qStrApp "x" #[],
        .qStrApp "ite" #[.qStrApp ">=" #[.qStrApp "x" #[], .sConst (.num 0)],
          .qStrApp "mod" #[.qStrApp "x" #[], .qStrApp "y" #[]],
          .qStrApp "-" #[.qStrApp "mod" #[.qStrApp "-" #[.qStrApp "x" #[]], .qStrApp "y" #[]]]]]),
    .defFun false "iediv" #[("x", .app (.symb "Int") #[]), ("y", .app (.symb "Int") #[])] (.app (.symb "Int") #[])
      (.qStrApp "ite" #[.qStrApp "=" #[.qStrApp "y" #[], .sConst (.num 0)], .sConst (.num 0), .qStrApp "div" #[.qStrApp "x" #[], .qStrApp "y" #[]]]),
    .defFun false "iemod" #[("x", .app (.symb "Int") #[]), ("y", .app (.symb "Int") #[])] (.app (.symb "Int") #[])
      (.qStrApp "ite" #[.qStrApp "=" #[.qStrApp "y" #[], .sConst (.num 0)], .qStrApp "x" #[], .qStrApp "mod" #[.qStrApp "x" #[], .qStrApp "y" #[]]])
   ]

/--
  `printFn : (tyValMap : _) → (varValMap : _) → (etomValMap : _) → MetaM α`
-/
def withExprValuation
  {α : Type} [Inhabited α] (sni : SMTNamingInfo) (h2lMap : Std.HashMap LamAtomic String)
  (printFn : Std.HashMap Nat Expr → Std.HashMap Nat Expr → Std.HashMap Nat Expr → MetaM α) :
  MetaM α := do
  let tyValMap := Std.HashMap.ofList (sni.tyVal.zipIdx.map (fun ((e, _), n) => (n, e))).toList
  let varValMap := Std.HashMap.ofList (sni.varVal.zipIdx.map (fun ((e, _), n) => (n, e))).toList
  let etomsWithName := h2lMap.toArray.filterMap (fun (atomic, name) =>
    match atomic with | .etom n => .some (n, name) | _ => .none)
  let declInfos ← etomsWithName.mapM (fun (n, name) => do
    let .some s := sni.lamEVarTy[n]?
      | throwError "{decl_name%} :: Unknown etom {n}"
    let type ← Lam2D.interpLamSortAsUnlifted tyValMap s
    return (Name.mkSimple name, .default, fun _ => pure type))
  Meta.withLocalDecls declInfos (fun etomFVars => do
    let etomValMap := Std.HashMap.ofList ((etomsWithName.zip etomFVars).map (fun ((n, _), e) => (n, e))).toList
    printFn tyValMap varValMap etomValMap)

end SMT

open SMT in
/--
  `facts` should not contain import versions of `eq, ∀` or `∃`
  `valid_fact_{i}` corresponds to the `i`-th entry in `facts`
-/
def lamFOL2SMT
  (sni : SMTNamingInfo) (lamVarTy lamEVarTy : Array LamSort)
  (facts : Array LamTerm) (minds : Array MutualIndInfo) :
  TransM LamAtomic LamSort (Array IR.SMT.Command × Array STerm) := do
  let _ ← sortAuxDecls.mapM addCommand
  let _ ← termAuxDecls.mapM addCommand
  for mind in minds do
    let (dsdecl, compCtors, compProjs) ← lamMutualIndInfo2STerm sni mind
    trace[auto.lamFOL2SMT] "MutualIndInfo translated to command {dsdecl}"
    addCommand dsdecl
    let compCtorEqns ← compCtors.mapM (compEqn sni lamVarTy lamEVarTy)
    let _ ← compCtorEqns.mapM addCommand
    let compProjEqns ← compProjs.mapM (compEqn sni lamVarTy lamEVarTy)
    let _ ← compProjEqns.mapM addCommand
  let mut validFacts := #[]
  for (t, idx) in facts.zipIdx do
    let sterm ← lamTerm2STerm sni lamVarTy lamEVarTy t
    validFacts := validFacts.push sterm
    trace[auto.lamFOL2SMT] "λ term {repr t} translated to SMT term {sterm}"
    addCommand (.assert (.attr sterm #[.symb "named" s!"valid_fact_{idx}"]))
  let commands ← getCommands
  return (commands, validFacts)

open SMT in
/-- Identical to `lamFOL2SMT` but it also outputs `Auto.IR.SMT.State.l2hMap`, `Auto.IR.SMT.getWfPredicatesInvMap`, and selector information -/
def lamFOL2SMTWithExtraInfo
  (sni : SMTNamingInfo) (lamVarTy lamEVarTy : Array LamSort)
  (facts : Array LamTerm) (minds : Array MutualIndInfo) :
  TransM LamAtomic LamSort (Array IR.SMT.Command × Array STerm × Std.HashMap String LamAtomic × Std.HashMap String LamSort × Array SelectorInfo) := do
  let _ ← sortAuxDecls.mapM addCommand
  let _ ← termAuxDecls.mapM addCommand
  let mut selInfos : Array SelectorInfo := #[]
  for mind in minds do
    let (dsdecl, compCtors, compProjs, mindInfos, mindSelInfos) ← lamMutualIndInfo2STermWithInfos sni mind
    trace[auto.lamFOL2SMT] "MutualIndInfo {mind} translated to command {dsdecl}"
    trace[auto.lamFOL2SMT] "mindInfos for {mind}: {mindInfos.map (fun x => (x.1, DatatypeDecl.toString x.2.2))}"
    trace[auto.lamFOL2SMT] "Selector infos for {mind}: {mindSelInfos}"
    addCommand dsdecl
    let compCtorEqns ← compCtors.mapM (compEqn sni lamVarTy lamEVarTy)
    let _ ← compCtorEqns.mapM addCommand
    let compProjEqns ← compProjs.mapM (compEqn sni lamVarTy lamEVarTy)
    let _ ← compProjEqns.mapM addCommand
    trace[auto.lamFOL2SMT] "compCtorEqns: {compCtorEqns}"
    trace[auto.lamFOL2SMT] "compProjEqns: {compProjEqns}"
    -- Define the well-formed constraint for all of the mutually inductive types (note that calling `defineWfConstraint` on just one of them is enough)
    let ⟨firstMindType, _, _⟩ :: _ := mind
      | throwError "{decl_name%} :: Mutually inductive types {mind} does not have a first entry"
    let .atom sn := firstMindType
      | throwError "{decl_name%} :: Mutually inductive types {mind} contains a type {firstMindType} which is not an atom"
    trace[auto.lamFOL2SMT] "About to call h2Symb on {LamAtomic.sort sn}"
    let datatypeName ← h2Symb (.sort sn) .none
    trace[auto.lamFOL2SMT] "Successfully called h2Symb on {LamAtomic.sort sn} (res: {datatypeName})"
    let nameOpt ← defineWfConstraint sni (.atom sn) (some mindSelInfos)
    trace[auto.lamFOL2SMT] "Successfully defined well-formed constraint for {datatypeName} (output : {nameOpt})"
    -- Update `selInfos`
    selInfos := selInfos ++ mindSelInfos
  let mut validFacts := #[]
  for (t, idx) in facts.zipIdx do
    let sterm ← lamTerm2STerm sni lamVarTy lamEVarTy t
    validFacts := validFacts.push sterm
    trace[auto.lamFOL2SMT] "λ term {repr t} translated to SMT term {sterm}"
    addCommand (.assert (.attr sterm #[.symb "named" s!"valid_fact_{idx}"]))
  let commands ← getCommands
  let l2hMap ← Auto.IR.SMT.getL2hMap
  let wfPredicatesInvMap ← Auto.IR.SMT.getWfPredicatesInvMap
  return (commands, validFacts, l2hMap, wfPredicatesInvMap, selInfos)

end Auto
