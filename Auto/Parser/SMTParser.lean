import Lean
import Auto.Parser.LexInit

namespace Auto
namespace Parser.SMTTerm
open Lexer
open Lean
open Meta

inductive LexVal
  | lparen
  | rparen
  | num (n : Nat)
  | rat (n : Nat) (m : Nat)
  | str (s : String)
  | symb (s : String)
  | kw (s : String)
  | reserved (s : String) -- e.g. "forall" and "exists"
  | comment (s : String)
  | underscore

deriving Inhabited, BEq, Hashable

open LexVal

def LexVal.toString : LexVal → String
| .lparen  => "("
| .rparen  => ")"
| .num n   => s!"{n}"
| .rat n m =>
  let pow := s!"{m}".length - 1
  if m != Nat.pow 10 pow then
    panic!"LexVal :: .rat {n} {m} is not yet supported, because {m} is not a power of 10"
  else
    let nint := n / m
    let nfrac := n % m
    let nfracs := s!"{nfrac}"
    let nfracs :=
      String.mk ((List.range (pow - nfracs.length)).map (fun _ => '0')) ++
      nfracs
    s!"{nint}." ++ nfracs
| .str s   => "\"" ++ String.intercalate "\"\"" (s.splitOn "\"") ++ "\""
| .symb s  => s!"|{s}|"
| .kw s    => s!":{s}"
| .reserved s => s
| .comment s => s!";{s}\n"
| underscore => "_"

instance : ToString LexVal where
  toString := LexVal.toString

private def hexDigitToNat (c : Char) : Nat :=
  if '0' ≤ c ∧ c ≤ '9' then c.toNat - '0'.toNat
  else if 'a' ≤ c ∧ c ≤ 'f' then c.toNat - 'a'.toNat + 10
  else c.toNat - 'A'.toNat + 10

def LexVal.ofString (s : String) (attr : String) : LexVal :=
  match attr with
  | "("           => .lparen
  | ")"           => .rparen
  | "numeral"     => .num s.toNat!
  | "decimal"     =>
    if let [a, b] := s.splitOn "." then
      let a := a.toNat!
      let fracDigits := b.length
      let fracPow := Nat.pow 10 fracDigits
      let b := b.toNat!
      .rat (a * fracPow + b) fracPow
    else
      panic! s!"LexVal.ofString :: {repr s} is not a valid decimal number"
  | "hexadecimal" =>
    let hdigs := s.drop 2
    .num (hdigs.foldl (fun x c => x * 16 + hexDigitToNat c) 0)
  | "binary" =>
    let bdigs := s.drop 2
    .num (bdigs.foldl (fun x c => x * 2 + c.toNat - '0'.toNat) 0)
  | "string" =>
    let subs := ((s.drop 1).take (s.length - 2)).splitOn "\"\""
    .str (String.intercalate "\"" subs)
  | "simplesymbol" => .symb s
  | "quotedsymbol" => .symb ((s.drop 1).take (s.length - 2))
  | "keyword"      => .kw (s.drop 1)
  | "comment"      =>
    let rn : Nat := if s.get (s.prev (s.prev s.endPos)) == '\r' then 1 else 0
    .comment ((s.drop 1).take (s.length - 2 - rn))
  | "reserved"     => .reserved s
  | "forall"       => .reserved "forall"
  | "exists"       => .reserved "exists"
  | "lambda"       => .reserved "lambda"
  | "let"          => .reserved "let"
  | "_"            => .underscore
  | _              => panic! s!"LexVal.ofString :: {repr attr} is not a valid attribute"

inductive Term where
  | atom : LexVal → Term
  | app  : Array Term → Term
deriving Inhabited, BEq, Hashable

open Term

partial def Term.toString : Term → String
| .atom l => ToString.toString l
| .app ls => "(" ++ String.intercalate " " (ls.map toString).toList ++ ")"

instance : ToString Term where
  toString e := Term.toString e

structure PartialResult where
  -- Lexer state
  lst     : Nat := 0
  -- Partially matched lexicon
  lexpart : String := ""
  -- Parser stack
  pstk    : Array (Array Term) := #[]
deriving Inhabited, BEq, Hashable

def PartialResult.toString : PartialResult → String := fun ⟨lst, lexpart, pstk⟩ =>
  s!"PartialResult \{ lst := {lst}, lexpart := {repr lexpart}, pstk := {pstk.toList.map (·.toList)}}"

instance : ToString PartialResult where
  toString := PartialResult.toString

inductive LexResult where
  -- SMTTerm: Result
  -- String.pos: The position of the next character
  | complete   : Term → String.Pos → LexResult
  -- Array (Array Sexp): Parser stack
  -- Nat: State of lexer
  -- String.pos: The position of the next character
  | incomplete : PartialResult → String.Pos → LexResult
  -- Malformed input
  | malformed  : LexResult
deriving Inhabited, BEq, Hashable

def LexResult.toString : LexResult → String
| .complete s p => s!"ParseResult.complete {s} {p}"
| .incomplete pr p => s!"ParseResult.incomplete {pr} {p}"
| .malformed => "ParseResult.malformed"

local instance : Hashable Char := ⟨fun c => hash c.val⟩

/--
  Note: Make sure that the next character of `s` is either `EOF` or white space
  This is because wee rely on the property that:
     For each lexicon `l` with a white space at position `p`, the
     part of `l` before `p` will always be identified as `incomplete`
     by `ERE.ADFALexEagerL SMTSexp.lexiconADFA`, and never as `done`.
-/
def lexTerm [Monad m] [Lean.MonadError m] (s : String) (p : String.Pos)
  (partialResult : PartialResult) : m LexResult := do
  if p == s.endPos then
    return .incomplete partialResult p
  let nextLexicon (p : String.Pos) (lst : Nat) :=
    Regex.ERE.ADFALexEagerL SMT.lexiconADFA ⟨s, p, s.endPos⟩
      {strict := true, initS := lst, prependBeginS := false, appendEndS := false}
  let mut lst := partialResult.lst
  let mut lexpart := partialResult.lexpart
  let mut pstk := partialResult.pstk
  let mut p := p
  let endPos := s.endPos
  while true do
    -- If we're not resuming from an incomplete
    --   match of lexicon, skip white space
    if lexpart == "" then
      -- Skip whitespace characters
      while p != endPos do
        let c := s.get! p
        if SMT.whitespace.contains c then
          p := p + c
        else
          break
    -- This indicates incomplete input
    if p == endPos then
      return .incomplete ⟨0, "", pstk⟩ p
    match nextLexicon p lst with
    | ⟨.complete, matched, _, state⟩ =>
      -- It is possible for there to be more than one attr if "forall", "exists", or "let" is interpreted
      -- both as a symbol and as a reserved word. If this happens, the reserved word should be prioritized
      let attr ←
        match (SMT.lexiconADFA.getAttrs state).toList with
        | [attr] => pure attr
        | [attr1, attr2] =>
          if attr1 == "forall" || attr1 == "exists" || attr1 == "lambda" || attr1 == "let" || attr1 == "_" then pure attr1
          else if attr2 == "forall" || attr2 == "exists" || attr2 == "lambda" || attr2 == "let" || attr2 == "_" then pure attr2
          else throwError "parseTerm :: Attribute conflict not caused by forall, exists, lambda, let, or _"
        | _ => throwError "parseTerm :: Invalid number of attributes"

      p := matched.stopPos
      let lexval := LexVal.ofString (lexpart ++ matched.toString) attr
      -- Restore lexer state
      lst := 0; lexpart := ""
      match lexval with
      | .lparen =>
        pstk := pstk.push #[]
      | .rparen =>
        if pstk.size == 0 then
          -- Too many right parentheses
          return .malformed
        else
          let final := pstk.back!
          pstk := pstk.pop
          if pstk.size == 0 then
            return .complete (.app final) p
          else
            pstk := pstk.modify (pstk.size - 1) (fun arr => arr.push (.app final))
      | .comment s => pstk := pstk.modify (pstk.size - 1) (fun arr => arr.push (.atom (.comment s)))
      | l       =>
        -- Ordinary lexicons must be separated by whitespace or parentheses
        match s.get? p with
        | some c =>
          if !SMT.whitespace.contains c ∧ c != ')' ∧ c != '(' then
            return .malformed
        | none => pure ()
        if pstk.size == 0 then
          -- An atom
          return .complete (.atom lexval) p
        pstk := pstk.modify (pstk.size - 1) (fun arr => arr.push (.atom l))
    | ⟨.incomplete, m, _, lst'⟩ => return .incomplete ⟨lst', lexpart ++ m.toString, pstk⟩ m.stopPos
    | ⟨.malformed, _, _, _⟩  => return .malformed
  throwError s!"parseSexp :: Unexpected error when parsing string {s}"

partial def lexAllTerms [Monad m] [Lean.MonadError m] (s : String) (p : String.Pos) (acc : List Term) : m (List Term) := do
  match ← lexTerm s p {} with
  | .complete e p =>
    let restTerms ← lexAllTerms s p acc
    return e :: restTerms
  | .malformed .. => throwError "lexAllTerms: malformed input {s} (lexing from position {p})"
  | .incomplete .. => return acc

inductive SymbolInput
| UnaryBool -- Used for symbols that take in exactly one Bool argument
| UnaryProp -- Used for symbols that input and output exactly one Prop argument
| LeftAssocNoConstraint-- Used for symbols like `+` or `*` that ideally take in two nonProp/nonBool symbols but can be chained if given more arguments
| LeftAssocAllProp -- Like LeftAssocNoConstraint but all input and output must be of type Prop
| LeftAssocAllBool -- Like LeftAssocNoConstraint but all input and output must be of type Bool
| TwoExactNoConstraint -- Used for symbols like `<` that take in exactly two nonProp/nonBool arguments
| TwoExactEq -- Specifically used for `=` which can invoke Prop typing constraints if a Prop and Bool are equated
| Minus -- Minus is left-associative when given ≥ 2 arguments but is also used for unary negation
| Ite -- Used for `ite` which takes in exactly three arguments

open SymbolInput

/-- If `s` is a theory symbol that we have a hardcoded interpretation for, then return a list of the possible corresponding
    constants in Lean. When there are no typing constraints to determine which item in the list is to be chosen, earlier items
    in the list are preferred over later items in the list. -/
def smtSymbolToLeanName (s : String) : List (Name × SymbolInput) :=
  match s with
  | "<" => [(``LT.lt, TwoExactNoConstraint)]
  | "<=" => [(``LE.le, TwoExactNoConstraint)]
  | ">" => [(``GT.gt, TwoExactNoConstraint)]
  | ">=" => [(``GE.ge, TwoExactNoConstraint)]
  | "+" => [(``HAdd.hAdd, LeftAssocNoConstraint)]
  | "-" => [(``HSub.hSub, Minus)] -- Minus is left-associative when given ≥ 2 arguments but is also used for unary negation
  | "nsub" => [(``Nat.sub, Minus)]
  | "*" => [(``HMul.hMul, LeftAssocNoConstraint)]
  | "/" => [(``HDiv.hDiv, LeftAssocNoConstraint)]
  | "or" => [(``Or, LeftAssocAllProp), (``or, LeftAssocAllBool)]
  | "and" => [(``And, LeftAssocAllProp), (``and, LeftAssocAllBool)]
  | "not" => [(``Not, UnaryProp), (``not, UnaryBool)]
  | "=" => [(``Eq, TwoExactEq)]
  | "ite" => [(``Ite, Ite)]
  | _ => []

def builtInSymbolMap : Std.HashMap String Expr :=
  let map := Std.HashMap.emptyWithCapacity
  let map := map.insert "Nat" (mkConst ``Nat)
  let map := map.insert "Int" (mkConst ``Int)
  let map := map.insert "Bool" (.sort .zero)
  let map := map.insert "false" (mkConst ``False)
  let map := map.insert "true" (mkConst ``True)
  let map := map.insert "<" (mkConst ``LT.lt)
  let map := map.insert "<=" (mkConst ``LE.le)
  let map := map.insert ">" (mkConst ``GT.gt)
  let map := map.insert ">=" (mkConst ``GE.ge)
  let map := map.insert "+" (mkConst ``HAdd.hAdd)
  let map := map.insert "-" (mkConst ``HSub.hSub)
  let map := map.insert "nsub" (mkConst ``Nat.sub)
  let map := map.insert "*" (mkConst ``HMul.hMul)
  let map := map.insert "/" (mkConst ``HDiv.hDiv)
  let map := map.insert "or" (mkConst ``Or)
  let map := map.insert "and" (mkConst ``And)
  let map := map.insert "not" (mkConst ``Not)
  let map := map.insert "=" (mkConst ``Eq)
  let map := map.insert "ite" (mkConst ``Ite)
  map

/-- Given an expression `∀ x1 : t1, x2 : t2, ... xn : tn, b`, returns `[t1, t2, ..., tn]`. If the given expression is not
    a forall expression, then `getForallArgumentTypes` just returns the empty list -/
partial def getForallArgumentTypes (e : Expr) : List Expr :=
  match e.consumeMData with
  | Expr.forallE _ t b _ => t :: (getForallArgumentTypes b)
  | _ => []

/-- Like `getForallArgumentTypes` but skips over the types of arguments that have implicit binderInfos -/
partial def getExplicitForallArgumentTypes (e : Expr) : List Expr :=
  match e.consumeMData with
  | Expr.forallE _ t b .default => t :: (getExplicitForallArgumentTypes b)
  | Expr.forallE _ _t b _ => getExplicitForallArgumentTypes b -- Skip over t because this binder is implicit
  | _ => []

inductive ParseTermConstraint
  | expectedType : Expr → ParseTermConstraint
  | noConstraint
  deriving Inhabited, Repr

open ParseTermConstraint

instance : ToMessageData ParseTermConstraint where
  toMessageData := fun
    | expectedType t => m!"expectedType {t}"
    | noConstraint => m!"noConstraint"

/-- A helper function for `parseForall`, `parseExists`, and `parseLambda`

    When parsing the arguments of SMT forall and exists expressions, the SMT type "Bool" can appear, which sometimes must be interpreted
    as `Prop` and sometimes must be interpreted as `Bool`. In `parseForall` and `parseExists`, if there are `x` "Bool" binders, then there
    are `2^x` possible ways to interpret each of those binders. This helper function serves to facilitate the generation of those
    interpretations.

    `getNextSortedVars` takes as input `originalSortedVars` obtained by `parseSortedVar` and `curPropBoolChoice` which is an Array indicating
    which of the "Bool" binders should be interpreted as `Prop` (if `curPropBoolChoice` contains `(i, false)`, then the `i`th element of the
    output `sortedVars` array should be `Bool`, and if `curPropBoolChoice` contains `(i, true)`, then the `i`th element should be `Prop`)

    `getNextSortedVars` outputs the resulting `sortedVars` array (which is identical to `originalSortedVars` except at the indices where
    `Bool` is replaced with `Prop`) as well as `nextPropBoolChoice` (obtained by incrementing `curPropBoolChoice` like a bitvector with the
    least significant bit first).

    If `curPropBoolChoice` is an Array where no idx is mapped to `false`, then instead of supplying the next `curPropBoolChoice`, `getNextSortedVars`
    returns `none` for the second argument -/
def getNextSortedVars (originalSortedVars : Array (String × Expr)) (curPropBoolChoice : Array (Fin originalSortedVars.size × Bool))
  : Array (String × Expr) × Option (Array (Fin originalSortedVars.size × Bool)) := Id.run do
  -- Calculate `sortedVars`
  let mut sortedVars := originalSortedVars
  for (idx, interpAsProp) in curPropBoolChoice do
    sortedVars := sortedVars.set! idx (sortedVars[idx]!.1, if interpAsProp then .sort 0 else mkConst ``Bool)
  -- Calculate `nextPropBoolChoice`
  let mut nextPropBoolChoice := curPropBoolChoice
  for h : i in [:curPropBoolChoice.size] do
    if (curPropBoolChoice[i]'h.2.1).2 then
      nextPropBoolChoice := nextPropBoolChoice.set! i ((curPropBoolChoice[i]'h.2.1).1, false)
    else
      nextPropBoolChoice := nextPropBoolChoice.set! i ((curPropBoolChoice[i]'h.2.1).1, true)
      break
  -- Check whether we should return `some nextPropBoolChoice` or `none`
  if nextPropBoolChoice.any (fun (_, b) => b) then
    return (sortedVars, nextPropBoolChoice)
  else
    return (sortedVars, none)

/-- Given an expression `e` and a ParseTermConstraint, returns an expression that is equivalent to `e` and conforms to the constraint.
    If `parseTermConstraint` is `noConstraint`, then `correctType` will prefer interpreting the SMT "Int" sort as `Int` over `Nat`. -/
def correctType (e : Expr) (parseTermConstraint : ParseTermConstraint) : MetaM Expr := do
  let eType ← inferType e
  match parseTermConstraint with
  | noConstraint =>
    if ← isDefEq eType (mkConst ``Nat) then mkAppM ``Int.ofNat #[e]
    else return e
  | expectedType t => do
    if ← isDefEq eType t then return e
    else if eType.isProp && (← isDefEq t (mkConst ``Bool)) then whnf $ ← mkAppOptM ``decide #[some e, none]
    else if (← isDefEq eType (mkConst ``Bool)) && t.isProp then whnf $ ← mkAppM ``Eq #[e, mkConst ``true]
    else if (← isDefEq eType (mkConst ``Nat)) && (← isDefEq t (mkConst ``Int)) then return ← mkAppM ``Int.ofNat #[e]
    else if (← isDefEq eType (mkConst ``Int)) && (← isDefEq t (mkConst ``Nat)) then return ← mkAppM ``Int.natAbs #[e]
    else throwError "correctType :: {e} is parsed as {eType} which is not a {t}"

mutual
/-- Given a sorted var of the form `(symbol type)`, returns the string of the symbol and the type as an Expr -/
partial def parseSortedVar (sortedVar : Term) (symbolMap : Std.HashMap String Expr) (parseTermConstraint : ParseTermConstraint) : MetaM (String × Expr) := do
  match sortedVar with
  | app sortedVar =>
    match sortedVar with
    | #[var, varType] =>
      let atom (symb varSymbol) := var
        | throwError "parseSortedVar :: Failed to parse {var} as the variable of a sortedVar"
      let varTypeExp ← parseTerm varType symbolMap noConstraint
      match parseTermConstraint with
      | noConstraint => return (varSymbol, varTypeExp)
      | expectedType t =>
        let mut tAndVarTypeExpCompatible ← isDefEq varTypeExp t
        tAndVarTypeExpCompatible := tAndVarTypeExpCompatible || (varTypeExp.isProp && (← isDefEq t (mkConst ``Bool)))
        tAndVarTypeExpCompatible := tAndVarTypeExpCompatible || ((← isDefEq varTypeExp (mkConst ``Bool)) && t.isProp)
        tAndVarTypeExpCompatible := tAndVarTypeExpCompatible || ((← isDefEq varTypeExp (mkConst ``Nat)) && (← isDefEq t (mkConst ``Int)))
        tAndVarTypeExpCompatible := tAndVarTypeExpCompatible || ((← isDefEq varTypeExp (mkConst ``Int)) && (← isDefEq t (mkConst ``Nat)))
        if tAndVarTypeExpCompatible then return (varSymbol, t)
        else throwError "parseSortedVar :: {sortedVar} is parsed as having type {varTypeExp} which is not the expected type {t}"
    | _ => throwError "parseSortedVar :: Failed to parse {sortedVar} as a sortedVar"
  | _ => throwError "parseSortedVar :: {sortedVar} is supposed to be a sortedVar, not an atom"

partial def parseForallBodyWithSortedVars (vs : List Term) (sortedVars : Array (String × Expr))
  (symbolMap : Std.HashMap String Expr) (forallBody : Term) : MetaM Expr := do
  withLocalDeclsD (sortedVars.map fun (n, ty) => (n.toName, fun _ => pure ty)) fun _ => do
    let lctx ← getLCtx
    let mut symbolMap := symbolMap
    let mut sortedVarDecls := #[]
    for sortedVar in sortedVars do
      let some sortedVarDecl := lctx.findFromUserName? sortedVar.1.toName
        | throwError "parseForall :: Unknown sorted var name {sortedVar.1} (parseForall input: {vs})"
      symbolMap := symbolMap.insert sortedVar.1 (mkFVar sortedVarDecl.fvarId)
      sortedVarDecls := sortedVarDecls.push sortedVarDecl
    let body ← parseTerm forallBody symbolMap (expectedType (.sort 0))
    Meta.mkForallFVars (sortedVarDecls.map (fun decl => mkFVar decl.fvarId)) body

partial def parseForall (vs : List Term) (symbolMap : Std.HashMap String Expr) : MetaM Expr := do
  let [app sortedVars, forallBody] := vs
    | throwError "parseForall :: Unexpected input list {vs}"
  let sortedVars ← sortedVars.mapM (fun sv => parseSortedVar sv symbolMap noConstraint)
  let sortedVarsWithIndices := sortedVars.mapFinIdx (fun idx val pf => (val, Fin.mk idx pf))
  let mut curPropBoolChoice := some $ (sortedVarsWithIndices.filter (fun ((_, t), _) => t.isProp)).map (fun (_, idx) => (idx, false))
  let mut possibleSortedVars := #[]
  while curPropBoolChoice.isSome do
    let (nextSortedVars, nextCurPropBoolChoice) := getNextSortedVars sortedVars curPropBoolChoice.get!
    possibleSortedVars := possibleSortedVars.push nextSortedVars
    curPropBoolChoice := nextCurPropBoolChoice
  for sortedVars in possibleSortedVars do
    try
      return ← parseForallBodyWithSortedVars vs sortedVars symbolMap forallBody
    catch _ =>
      continue
  throwError "parseForall :: Failed to parse for all expression with vs: {vs}"

partial def parseExistsBodyWithSortedVars (vs : List Term) (sortedVars : Array (String × Expr))
  (symbolMap : Std.HashMap String Expr) (existsBody : Term) : MetaM Expr := do
  withLocalDeclsD (sortedVars.map fun (n, ty) => (n.toName, fun _ => pure ty)) fun _ => do
    let lctx ← getLCtx
    let mut symbolMap := symbolMap
    let mut sortedVarDecls := #[]
    for sortedVar in sortedVars do
      let some sortedVarDecl := lctx.findFromUserName? sortedVar.1.toName
        | throwError "parseForall :: Unknown sorted var name {sortedVar.1} (parseForall input: {vs})"
      symbolMap := symbolMap.insert sortedVar.1 (mkFVar sortedVarDecl.fvarId)
      sortedVarDecls := sortedVarDecls.push sortedVarDecl
    let lamBody ← parseTerm existsBody symbolMap (expectedType (.sort 0))
    let mut res := lamBody
    for decl in sortedVarDecls.reverse do
      res ← Meta.mkLambdaFVars #[(mkFVar decl.fvarId)] res
      res ← Meta.mkAppM ``Exists #[res]
    return res

partial def parseExists (vs : List Term) (symbolMap : Std.HashMap String Expr) : MetaM Expr := do
  let [app sortedVars, existsBody] := vs
    | throwError "parseExists :: Unexpected input list {vs}"
  let sortedVars ← sortedVars.mapM (fun sv => parseSortedVar sv symbolMap noConstraint)
  let sortedVarsWithIndices := sortedVars.mapFinIdx (fun idx val pf => (val, Fin.mk idx pf))
  let mut curPropBoolChoice := some $ (sortedVarsWithIndices.filter (fun ((_, t), _) => t.isProp)).map (fun (_, idx) => (idx, false))
  let mut possibleSortedVars := #[]
  while curPropBoolChoice.isSome do
    let (nextSortedVars, nextCurPropBoolChoice) := getNextSortedVars sortedVars curPropBoolChoice.get!
    possibleSortedVars := possibleSortedVars.push nextSortedVars
    curPropBoolChoice := nextCurPropBoolChoice
  for sortedVars in possibleSortedVars do
    try
      return ← parseExistsBodyWithSortedVars vs sortedVars symbolMap existsBody
    catch _ =>
      continue
  throwError "parseExists :: Failed to parse exists expression with vs: {vs}"

/-- Note: The `parseTermConstraint` argument passed into `parseLambdaBodyWithSortedVars` corresponds to the expected type of the
    entire lambda expression, not the expected type of the lambda's body. -/
partial def parseLambdaBodyWithSortedVars (vs : List Term) (sortedVars : Array (String × Expr))
  (symbolMap : Std.HashMap String Expr) (lambdaBody : Term) (parseTermConstraint : ParseTermConstraint) : MetaM Expr := do
  withLocalDeclsD (sortedVars.map fun (n, ty) => (n.toName, fun _ => pure ty)) fun _ => do
    let lctx ← getLCtx
    let mut symbolMap := symbolMap
    let mut sortedVarDecls := #[]
    for sortedVar in sortedVars do
      let some sortedVarDecl := lctx.findFromUserName? sortedVar.1.toName
        | throwError "parseForall :: Unknown sorted var name {sortedVar.1} (parseForall input: {vs})"
      symbolMap := symbolMap.insert sortedVar.1 (mkFVar sortedVarDecl.fvarId)
      sortedVarDecls := sortedVarDecls.push sortedVarDecl
    match parseTermConstraint with
    | noConstraint =>
      let body ← parseTerm lambdaBody symbolMap noConstraint
      Meta.mkLambdaFVars (sortedVarDecls.map (fun decl => mkFVar decl.fvarId)) body
    | expectedType t =>
      let tBody := t.getForallBody
      if tBody.hasLooseBVars then throwError "parseLambdaBodyWithSortedVars :: {t} is a dependent type"
      let body ← parseTerm lambdaBody symbolMap (expectedType tBody)
      Meta.mkLambdaFVars (sortedVarDecls.map (fun decl => mkFVar decl.fvarId)) body

partial def parseLambda (vs : List Term) (symbolMap : Std.HashMap String Expr) (parseTermConstraint : ParseTermConstraint) : MetaM Expr := do
  let [app sortedVars, lambdaBody] := vs
    | throwError "parseLambda :: Unexpected input list {vs}"
  match parseTermConstraint with
  | noConstraint =>
    let sortedVars ← sortedVars.mapM (fun sv => parseSortedVar sv symbolMap noConstraint)
    let sortedVarsWithIndices := sortedVars.mapFinIdx (fun idx val pf => (val, Fin.mk idx pf))
    let mut curPropBoolChoice := some $ (sortedVarsWithIndices.filter (fun ((_, t), _) => t.isProp)).map (fun (_, idx) => (idx, false))
    let mut possibleSortedVars := #[]
    while curPropBoolChoice.isSome do
      let (nextSortedVars, nextCurPropBoolChoice) := getNextSortedVars sortedVars curPropBoolChoice.get!
      possibleSortedVars := possibleSortedVars.push nextSortedVars
      curPropBoolChoice := nextCurPropBoolChoice
    for sortedVars in possibleSortedVars do
      try
        return ← parseLambdaBodyWithSortedVars vs sortedVars symbolMap lambdaBody noConstraint
      catch _ =>
        continue
    throwError "parseLambda :: Failed to parse lambda expression with vs: {vs}"
  | expectedType t =>
    let lambdaArgTypes := (getExplicitForallArgumentTypes t).toArray
    if lambdaArgTypes.size != sortedVars.size then
      throwError "parseLambda :: Expected {lambdaArgTypes.size} arguments, but got {sortedVars.size} in {vs}"
    let sortedVars ← (sortedVars.zip lambdaArgTypes).mapM (fun (sv, t) => parseSortedVar sv symbolMap (expectedType t))
    parseLambdaBodyWithSortedVars vs sortedVars symbolMap lambdaBody parseTermConstraint

/-- Given a varBinding of the form `(symbol value)` returns the string of the symbol, the type of the value, and the value itself -/
partial def parseVarBinding (varBinding : Term) (symbolMap : Std.HashMap String Expr) : MetaM (String × Expr × Expr) := do
  match varBinding with
  | app varBinding =>
    match varBinding with
    | #[var, varValue] =>
      let atom (symb var) := var
        | throwError "parseVarBinding :: Failed to parse {var} as the variable of a var binding"
      let varValue ← parseTerm varValue symbolMap noConstraint
      let varType ← inferType varValue
      return (var, varType, varValue)
    | _ => throwError "parseVarBinding :: Failed to parse {varBinding} as a var binding"
  | _ => throwError "parseVarBinding :: {varBinding} is supposed to be a varBinding, not an atom"

partial def parseLet (vs : List Term) (symbolMap : Std.HashMap String Expr) (parseTermConstraint : ParseTermConstraint) : MetaM Expr := do
  let [app varBindings, letBody] := vs
    | throwError "parsseLet :: Unexpected input list {vs}"
  let varBindings ← varBindings.mapM (fun vb => parseVarBinding vb symbolMap)
  withLocalDeclsD (varBindings.map fun (n, ty, _) => (n.toName, fun _ => pure ty)) fun _ => do
    let lctx ← getLCtx
    let mut symbolMap := symbolMap
    let mut varBindingDecls := #[]
    for varBinding in varBindings do
      let some varBindingDecl := lctx.findFromUserName? varBinding.1.toName
        | throwError "parseLet :: Unknown var binding name {varBinding.1} (parseLet input: {vs})"
      symbolMap := symbolMap.insert varBinding.1 (mkFVar varBindingDecl.fvarId)
      varBindingDecls := varBindingDecls.push varBindingDecl
    let body ← parseTerm letBody symbolMap parseTermConstraint
    let abstractedBody ← Expr.abstractM body (varBindingDecls.map (fun decl => mkFVar decl.fvarId))
    let mut res := abstractedBody
    for varBinding in varBindings.reverse do
      res := .letE varBinding.1.toName varBinding.2.1 varBinding.2.2 res true
    return res

partial def parseLeftAssocAppAux (headSymbol : Name) (args : List Term) (symbolMap : Std.HashMap String Expr)
  (acc : Expr) (parseTermConstraint : ParseTermConstraint) : MetaM Expr := do
  match args with
  | [] => return acc
  | arg :: restArgs =>
    let arg ← parseTerm arg symbolMap parseTermConstraint
    let acc ← mkAppM headSymbol #[acc, arg]
    parseLeftAssocAppAux headSymbol restArgs symbolMap acc parseTermConstraint

partial def parseLeftAssocApp (headSymbol : Name) (args : List Term) (symbolMap : Std.HashMap String Expr)
  (parseTermConstraint : ParseTermConstraint) : MetaM Expr := do
  match args with
  | arg1 :: (arg2 :: restArgs) =>
    let arg1 ← parseTerm arg1 symbolMap parseTermConstraint
    let arg2 ← parseTerm arg2 symbolMap parseTermConstraint
    let acc ← mkAppM headSymbol #[arg1, arg2]
    parseLeftAssocAppAux headSymbol restArgs symbolMap acc parseTermConstraint
  | _ => throwError "parseLeftAssocApplication :: Insufficient arguments given to {headSymbol}. args: {args}"

/-- Note: parseImplicationAux expects to receive args in reverse order
    (meaining if args = `[x, y, z]`, this should become `z => y => x`) -/
partial def parseImplicationAux (args : List Term) (symbolMap : Std.HashMap String Expr) (acc : Expr) : MetaM Expr := do
  match args with
  | [] => return acc
  | arg :: restArgs =>
    let arg ← parseTerm arg symbolMap (expectedType (.sort 0))
    let acc := .forallE `_ arg acc .default
    parseImplicationAux restArgs symbolMap acc

/-- SMT implication is right associative -/
partial def parseImplication (args : List Term) (symbolMap : Std.HashMap String Expr) : MetaM Expr := do
  match args.reverse with
  | lastArg :: (lastArg2 :: restArgs) =>
    let lastArg ← parseTerm lastArg symbolMap (expectedType (.sort 0))
    parseImplicationAux (lastArg2 :: restArgs) symbolMap lastArg
  | _ => throwError "parseImplication :: Insufficient arguments given. args: {args}"

/-- The entry function for the variety of mutually recursive functions used to parse SMT terms. `symbolMap` is used to map smt constants to the original
    Lean expressions they are meant to represent. `parseTermConstraint` is used to indicate whether the output expression must be a particular type. -/
partial def parseTerm (e : Term) (symbolMap : Std.HashMap String Expr) (parseTermConstraint : ParseTermConstraint) : MetaM Expr := do
  Core.checkSystem "{decl_name%}"
  match e with
  | atom (num n) => correctType (Expr.lit (Literal.natVal n)) parseTermConstraint
  | atom (rat _ _) => throwError "parseTerm :: Rational/real numbers not supported yet"
  | atom (str s) => correctType (Expr.lit (Literal.strVal s)) parseTermConstraint
  | atom (symb s) =>
    match symbolMap.get? s with
    | some v => correctType v parseTermConstraint
    | none =>
      match builtInSymbolMap.get? s with
      | some v => correctType v parseTermConstraint
      | none => throwError "parseTerm :: Unknown symbol {s}"
  | app vs =>
    match vs.toList with
    | atom (reserved "forall") :: restVs => correctType (← parseForall restVs symbolMap) parseTermConstraint
    | atom (reserved "exists") :: restVs => correctType (← parseExists restVs symbolMap) parseTermConstraint
    | atom (reserved "lambda") :: restVs => parseLambda restVs symbolMap parseTermConstraint
    | atom (reserved "let") :: restVs => parseLet restVs symbolMap parseTermConstraint
    | atom (symb "=>") :: restVs => parseImplication restVs symbolMap
    | app #[atom underscore, atom (symb "is"), ctor] :: [testerArg] =>
      let parsedCtor ← parseTerm ctor symbolMap noConstraint -- Note: `parsedCtor` is already instantiated with datatype parameters
      let parsedTesterArg ← parseTerm testerArg symbolMap noConstraint
      let idtType ← inferType parsedTesterArg -- `idtType` is the type of the inductive datatype of which `ctor` is a constructor
      -- Check that `idtType` is an inductive datatype
      if ← matchConstInduct idtType.getAppFn (fun _ => pure true) (fun _ _ => pure false) then
        throwError "parseTerm :: Tester applied not {testerArg} of type {idtType} which is not an inductive datatype"
      let ctorType ← inferType parsedCtor
      let ctorArgTypes := (getForallArgumentTypes ctorType).toArray
      withLocalDeclsD (ctorArgTypes.mapFinIdx fun idx ty _ => ((.str .anonymous ("arg" ++ idx.repr)), fun _ => pure ty)) fun ctorArgs => do
        let mut res ← mkAppM ``Eq #[parsedTesterArg, ← mkAppM' parsedCtor ctorArgs]
        for ctorArg in ctorArgs do
          res ← mkLambdaFVars #[ctorArg] res
          res ← mkAppM ``Exists #[res]
        correctType res parseTermConstraint
    | atom (symb s) :: restVs =>
      match smtSymbolToLeanName s with
      | [(s1, UnaryProp), (s2, UnaryBool)] =>
        match restVs with
        | [arg] =>
          match parseTermConstraint with
          | noConstraint =>
            let arg ← parseTerm arg symbolMap noConstraint
            let argType ← inferType arg
            if argType.isProp then mkAppM s1 #[arg]
            else if (← isDefEq argType (mkConst ``Bool)) then mkAppM s2 #[arg]
            else throwError "parseTerm :: {arg} was not be interpreted as Prop or Bool in {e}"
          | expectedType t =>
            if t.isProp then
              let arg ← parseTerm arg symbolMap (expectedType t)
              mkAppM s1 #[arg]
            else if (← isDefEq t (mkConst ``Bool)) then
              let arg ← parseTerm arg symbolMap (expectedType t)
              mkAppM s2 #[arg]
            else
              throwError "parseTerm :: {e} is parsed as {arg} which is not a {t}"
        | _ => throwError "parseTerm :: Invalid unary symbol application {e}"
      | [(s, TwoExactNoConstraint)] =>
        match restVs with
        | [arg1, arg2] =>
          let arg1 ← parseTerm arg1 symbolMap noConstraint
          let arg2 ← parseTerm arg2 symbolMap noConstraint
          let res ← mkAppM s #[arg1, arg2]
          correctType res parseTermConstraint
        | _arg1 :: (_arg2 :: _restArgs) =>
          -- **TODO**: Interpret `(< a b c)` as `(and (< a b) (< b c))`
          throwError "parseTerm :: TwoExact symbol with more than two arguments not implemented yet (e: {e})"
        | _ => throwError "parseTerm :: Invalid application {e}"
      | [(s, TwoExactEq)] =>
        match restVs with
        | [arg1, arg2] =>
          let arg1' ← parseTerm arg1 symbolMap noConstraint
          let arg1Type ← inferType arg1'
          let arg2Opt ←
            try pure $ some $ ← parseTerm arg2 symbolMap (expectedType arg1Type)
            catch _ => pure none
          match arg2Opt with
          | some arg2 =>
            correctType (← mkAppM s #[arg1', arg2]) parseTermConstraint
          | none => -- If `arg2` can't be made to match `arg1`'s type, try to make `arg1` match `arg2`'s type
            let arg2 ← parseTerm arg2 symbolMap noConstraint
            let arg2Type ← inferType arg2
            let arg1' ← parseTerm arg1 symbolMap (expectedType arg2Type)
            correctType (← mkAppM s #[arg1', arg2]) parseTermConstraint
        | _arg1 :: (_arg2 :: _restArgs) =>
          -- **TODO**: Interpret `(= a b c)` as `(and (= a b) (= b c))`
          throwError "parseTerm :: TwoExact symbol with more than two arguments not implemented yet (e: {e})"
        | _ => throwError "parseTerm :: Invalid application {e}"
      | [(s, LeftAssocNoConstraint)] => parseLeftAssocApp s restVs symbolMap parseTermConstraint
      | [(s1, LeftAssocAllProp), (s2, LeftAssocAllBool)] =>
        match parseTermConstraint with
        | noConstraint => parseLeftAssocApp s1 restVs symbolMap (expectedType (.sort 0)) -- Favor `Prop` interpretation over `Bool` interpretation
        | expectedType t =>
          if t.isProp then parseLeftAssocApp s1 restVs symbolMap (expectedType t)
          else if (← isDefEq t (mkConst ``Bool)) then parseLeftAssocApp s2 restVs symbolMap (expectedType t)
          else throwError "parseTerm :: {e} has a head symbol {s} that does not permit it to have type {t}"
      | [(s, Minus)] =>
        match restVs with
        | [arg] => -- Subtraction is left associative, but if it takes in just one argument, Minus is interpreted as negation
          let arg ← parseTerm arg symbolMap parseTermConstraint
          mkAppM ``Neg.neg #[arg]
        | _ =>
          if s == ``Nat.sub then
            match parseTermConstraint with
            | noConstraint =>
              parseLeftAssocApp s restVs symbolMap (expectedType (mkConst ``Nat))
            | expectedType t =>
              if (← isDefEq t (mkConst ``Nat)) then parseLeftAssocApp s restVs symbolMap (expectedType t)
              else throwError "parseTerm :: {e} has a head symbol {s} that does not permit it to have type {t}"
          else
            parseLeftAssocApp s restVs symbolMap parseTermConstraint
      | [(_, Ite)] =>
        match restVs with
        | [cond, thenBranch, elseBranch] =>
          -- **TODO** As with `Eq`, we should try to make `thenBranch` and `elseBranch` match each other's type
          -- (if parseTermConstraint is `noConstraint`)
          let cond ← parseTerm cond symbolMap (expectedType (.sort 0))
          let thenBranch ← parseTerm thenBranch symbolMap parseTermConstraint
          let elseBranch ← parseTerm elseBranch symbolMap parseTermConstraint
          mkAppM ``ite #[cond, thenBranch, elseBranch]
        | _ => throwError "parseTerm :: {e} has ite as a head symbol but does not take in exactly three arguments"
      | [] =>
        match symbolMap.get? s with
        | some symbolExp =>
          let symbolExpType ← inferType symbolExp
          let expectedArgTypes := getExplicitForallArgumentTypes symbolExpType
          let args ← (restVs.zip expectedArgTypes).mapM (fun (t, expectedArgType) => parseTerm t symbolMap (expectedType expectedArgType))
          let res ← mkAppM' symbolExp args.toArray
          correctType res parseTermConstraint
        | none => throwError "parseTerm :: Unknown symbol {s} in term {e}"
      | _ => throwError "parseTerm :: Unexpected result of smtSymbolToLeanName {s}"
    | _ => throwError "parseTerm :: Invalid term application {e}"
  | _ => throwError "parseTerm :: Invalid term {e}" -- All other atoms shouldn't exist as standalone terms
end

initialize
  registerTraceClass `auto.smt.parseTermErrors

/-- Calls `parseTerm` on `e` and then abstracts all of the metavariables corresponding to selectors given by `selMVars` (replacing
    the first metavariable with `selMVars` with `Expr.bvar 0` and so on) -/
def parseTermAndAbstractSelectors (e : Term) (symbolMap : Std.HashMap String Expr) (selMVars : Array Expr) : MetaM Expr := do
  let res ← parseTerm e symbolMap noConstraint
  res.abstractM selMVars

/-- Calls `parseTerm` on `e` and then abstracts all of the metavariables corresponding to selectors given by `selMVars` (replacing
    the first metavariable with `selMVars` with `Expr.bvar 0` and so on). Returns `none` if any error occurs. -/
def tryParseTermAndAbstractSelectors (e : Term) (symbolMap : Std.HashMap String Expr) (selMVars : Array Expr) : MetaM (Option Expr) := do
  try
    let res ← parseTerm e symbolMap noConstraint
    res.abstractM selMVars
  catch err =>
    trace[auto.smt.parseTermErrors] "Error parsing {e}. Error: {err.toMessageData}"
    return none
