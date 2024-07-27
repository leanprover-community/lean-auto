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
| .app ls => "(" ++ String.intercalate " " (ls.map toString).data ++ ")"

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
          if attr1 == "forall" || attr1 == "exists" || attr1 == "let" || attr1 == "_" then pure attr1
          else if attr2 == "forall" || attr2 == "exists" || attr2 == "let" || attr2 == "_" then pure attr2
          else throwError "parseTerm :: Attribute conflict not caused by forall, exists, let, or _"
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
          let final := pstk.back
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

/-
private def testLexer (s : String) (p : String.Pos) (print := true) : MetaM Unit := do
  match ← lexTerm s p {} with
  | .complete e p => if print then IO.println e; IO.println (Substring.toString ⟨s, p, s.endPos⟩)
  | .malformed .. => IO.println "malformed"
  | .incomplete .. => IO.println "incomplete"

#eval testLexer "(exists (x Int) (y Int) x0)" 0
#eval testLexer "(forall (x Int) (y Int) (= (+ x y) (+ y x)))" 0
#eval testLexer "(let ((_let_1 (+ x y))) (or (not (forall ((z Int)) (or (not (>= z 0)) (P z)))) (or (not (>= _let_1 0)) (P _let_1))))" 0
#eval testLexer "(or (not (>= x 0)) (not (>= y 0)) (>= (+ x y) 0))" 0
-/

inductive SymbolInput
| UnaryBool -- Used for symbols that take in exactly one Bool argument
| UnaryProp -- Used for symbols that input and output exactly one Prop argument
| LeftAssocNoConstraint-- Used for symbols like `+` or `*` that ideally take in two nonProp/nonBool symbols but can be chained if given more arguments
| LeftAssocAllProp -- Like LeftAssocNoConstraint but all input and output must be of type Prop
| LeftAssocAllBool -- Like LeftAssocNoConstraint but all input and output must be of type Bool
| TwoExactNoConstraint -- Used for symbols like `<` that take in exactly two nonProp/nonBool arguments
| TwoExactEq -- Specifically used for `=` which can invoke Prop typing constraints if a Prop and Bool are equated
| Minus -- Minus is left-associative when given ≥ 2 arguments but is also used for unary negation

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
  | "*" => [(``HMul.hMul, LeftAssocNoConstraint)]
  | "/" => [(``HDiv.hDiv, LeftAssocNoConstraint)]
  | "or" => [(``Or, LeftAssocAllProp), (``or, LeftAssocAllBool)]
  | "and" => [(``And, LeftAssocAllProp), (``and, LeftAssocAllBool)]
  | "not" => [(``Not, UnaryProp), (``not, UnaryBool)]
  | "=" => [(``Eq, TwoExactEq)]
  | _ => []

def builtInSymbolMap : HashMap String Expr :=
  let map := HashMap.empty
  let map := map.insert "Nat" (mkConst ``Nat)
  let map := map.insert "Int" (mkConst ``Int)
  let map := map.insert "Bool" (.sort .zero)
  let map := map.insert "false" (mkConst ``False)
  let map := map.insert "true" (mkConst ``True)
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
  | Expr.forallE _ t b .default => t :: (getForallArgumentTypes b)
  | Expr.forallE _ t b _ => getForallArgumentTypes b -- Skip over t because this binder is implicit
  | _ => []

inductive ParseTermConstraint
  | mustBeProp
  | mustBeBool
  | noConstraint

open ParseTermConstraint

mutual
/-- Given a sorted var of the form `(symbol type)`, returns the string of the symbol and the type as an Expr -/
partial def parseSortedVar (sortedVar : Term) (symbolMap : HashMap String Expr) : MetaM (String × Expr) := do
  match sortedVar with
  | app sortedVar =>
    match sortedVar with
    | #[var, varType] =>
      let atom (symb varSymbol) := var
        | throwError "parseSortedVar :: Failed to parse {var} as the variable of a sortedVar"
      let varTypeExp ← parseTerm varType symbolMap noConstraint
      return (varSymbol, varTypeExp)
    | _ => throwError "parseSortedVar :: Failed to parse {sortedVar} as a sortedVar"
  | _ => throwError "parseSortedVar :: {sortedVar} is supposed to be a sortedVar, not an atom"

partial def parseForall (vs : List Term) (symbolMap : HashMap String Expr) : MetaM Expr := do
  let [app sortedVars, forallBody] := vs
    | throwError "parseForall :: Unexpected input list {vs}"
  let sortedVars ← sortedVars.mapM (fun sv => parseSortedVar sv symbolMap)
  withLocalDeclsD (sortedVars.map fun (n, ty) => (n.toName, fun _ => pure ty)) fun _ => do
    let lctx ← getLCtx
    let mut symbolMap := symbolMap
    let mut sortedVarDecls := #[]
    for sortedVar in sortedVars do
      let some sortedVarDecl := lctx.findFromUserName? sortedVar.1.toName
        | throwError "parseForall :: Unknown sorted var name {sortedVar.1} (parseForall input: {vs})"
      symbolMap := symbolMap.insert sortedVar.1 (mkFVar sortedVarDecl.fvarId)
      sortedVarDecls := sortedVarDecls.push sortedVarDecl
    let body ← parseTerm forallBody symbolMap mustBeProp
    Meta.mkForallFVars (sortedVarDecls.map (fun decl => mkFVar decl.fvarId)) body

partial def parseExists (vs : List Term) (symbolMap : HashMap String Expr) : MetaM Expr := do
  let [app sortedVars, existsBody] := vs
    | throwError "parseExists :: Unexpected input list {vs}"
  let sortedVars ← sortedVars.mapM (fun sv => parseSortedVar sv symbolMap)
  withLocalDeclsD (sortedVars.map fun (n, ty) => (n.toName, fun _ => pure ty)) fun _ => do
    let lctx ← getLCtx
    let mut symbolMap := symbolMap
    let mut sortedVarDecls := #[]
    for sortedVar in sortedVars do
      let some sortedVarDecl := lctx.findFromUserName? sortedVar.1.toName
        | throwError "parseForall :: Unknown sorted var name {sortedVar.1} (parseForall input: {vs})"
      symbolMap := symbolMap.insert sortedVar.1 (mkFVar sortedVarDecl.fvarId)
      sortedVarDecls := sortedVarDecls.push sortedVarDecl
    let lamBody ← parseTerm existsBody symbolMap mustBeProp
    let mut res := lamBody
    for decl in sortedVarDecls.reverse do
      res ← Meta.mkLambdaFVars #[(mkFVar decl.fvarId)] res
      res ← Meta.mkAppM ``Exists #[res]
    return res

/-- Given a varBinding of the form `(symbol value)` returns the string of the symbol, the type of the value, and the value itself -/
partial def parseVarBinding (varBinding : Term) (symbolMap : HashMap String Expr) : MetaM (String × Expr × Expr) := do
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

partial def parseLet (vs : List Term) (symbolMap : HashMap String Expr) (parseTermConstraint : ParseTermConstraint) : MetaM Expr := do
  let [app varBindings, letBody] := vs
    | throwError "parsseLet :: Unexpected input list {vs}"
  let varBindings ← varBindings.mapM (fun vb => parseVarBinding vb symbolMap)
  withLocalDeclsD (varBindings.map fun (n, ty, val) => (n.toName, fun _ => pure ty)) fun _ => do
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

partial def parseLeftAssocAppAux (headSymbol : Name) (args : List Term) (symbolMap : HashMap String Expr)
  (acc : Expr) (parseTermConstraint : ParseTermConstraint) : MetaM Expr := do
  match args with
  | [] => return acc
  | arg :: restArgs =>
    let arg ← parseTerm arg symbolMap parseTermConstraint
    let acc ← mkAppM headSymbol #[acc, arg]
    parseLeftAssocAppAux headSymbol restArgs symbolMap acc parseTermConstraint

partial def parseLeftAssocApp (headSymbol : Name) (args : List Term) (symbolMap : HashMap String Expr)
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
partial def parseImplicationAux (args : List Term) (symbolMap : HashMap String Expr) (acc : Expr) : MetaM Expr := do
  match args with
  | [] => return acc
  | arg :: restArgs =>
    let arg ← parseTerm arg symbolMap mustBeProp
    let acc := .forallE `_ arg acc .default
    parseImplicationAux restArgs symbolMap acc

/-- SMT implication is right associative -/
partial def parseImplication (args : List Term) (symbolMap : HashMap String Expr) : MetaM Expr := do
  match args.reverse with
  | lastArg :: (lastArg2 :: restArgs) =>
    let lastArg ← parseTerm lastArg symbolMap mustBeProp
    parseImplicationAux (lastArg2 :: restArgs) symbolMap lastArg
  | _ => throwError "parseImplication :: Insufficient arguments given. args: {args}"

partial def parseTerm (e : Term) (symbolMap : HashMap String Expr) (parseTermConstraint : ParseTermConstraint) : MetaM Expr := do
  match e with
  | atom (num n) =>
    match parseTermConstraint with
    | noConstraint => mkAppM ``Int.ofNat #[Expr.lit (Literal.natVal n)]
    | mustBeProp => throwError "parseTerm :: {e} can be parsed but not as a Prop"
    | mustBeBool => throwError "parseTerm :: {e} can be parsed but not as a Bool"
  | atom (rat n m) =>
    match parseTermConstraint with
    | noConstraint =>
      let numerator ← mkAppM ``Int.ofNat #[Expr.lit (Literal.natVal n)]
      mkAppM ``mkRat #[numerator, Expr.lit (Literal.natVal m)]
    | mustBeProp => throwError "parseTerm :: {e} can be parsed but not as a Prop"
    | mustBeBool => throwError "parseTerm :: {e} can be parsed but not as a Bool"
  | atom (str s) =>
    match parseTermConstraint with
    | noConstraint => return Expr.lit (Literal.strVal s)
    | mustBeProp => throwError "parseTerm :: {e} can be parsed but not as a Prop"
    | mustBeBool => throwError "parseTerm :: {e} can be parsed but not as a Bool"
  | atom (symb s) =>
    match symbolMap.find? s with
    | some v =>
      match parseTermConstraint with
      | noConstraint => return v
      | mustBeProp =>
        let vType ← inferType v
        if vType.isProp then
          return v
        else if vType == mkConst ``Bool then
          mkAppM ``Eq #[v, mkConst ``true]
        else
          throwError "parseTerm :: {e} is parsed as {v} which is not a Prop"
      | mustBeBool =>
        let vType ← inferType v
        if vType == mkConst ``Bool then
          return v
        else if vType.isProp then
          mkAppOptM ``decide #[some v, none]
        else
          throwError "parseTerm :: {e} is parsed as {v} which is not a Bool"
    | none =>
      match builtInSymbolMap.find? s with
      | some v =>
        match parseTermConstraint with
        | noConstraint => return v
        | mustBeProp =>
          let vType ← inferType v
          if vType.isProp then
            return v
          else if vType == mkConst ``Bool then
            mkAppM ``Eq #[vType, mkConst ``true]
          else
            throwError "parseTerm :: {e} is parsed as {v} which is not a Prop"
        | mustBeBool =>
          let vType ← inferType v
          if vType == mkConst ``Bool then
            return v
          else if vType.isProp then
            mkAppOptM ``decide #[some v, none]
          else
            throwError "parseTerm :: {e} is parsed as {v} which is not a Bool"
      | none => throwError "parseTerm :: Unknown symbol {s}"
  | app vs =>
    match vs.toList with
    | atom (reserved "forall") :: restVs => parseForall restVs symbolMap
    | atom (reserved "exists") :: restVs => parseExists restVs symbolMap
    | atom (reserved "let") :: restVs => parseLet restVs symbolMap parseTermConstraint
    | atom (symb "=>") :: restVs => parseImplication restVs symbolMap
    | app #[atom underscore, atom (symb "is"), ctor] :: [testerArg] =>
      let parsedCtor ← parseTerm ctor symbolMap noConstraint
      let parsedTesterArg ← parseTerm testerArg symbolMap noConstraint
      let idtType ← inferType parsedTesterArg -- `idtType` is the type of the inductive datatype of which `ctor` is a constructor
      -- Check that `idtType` is an inductive datatype
      if ← matchConstInduct idtType.getAppFn (fun _ => pure true) (fun _ _ => pure false) then
        throwError "parseTerm :: Tester applied not {testerArg} of type {idtType} which is not an inductive datatype"
      let idtParams := idtType.getAppArgs
      let ctorWithParams ← mkAppM' parsedCtor idtParams
      let ctorType ← inferType ctorWithParams
      let ctorArgTypes := getForallArgumentTypes ctorType
      withLocalDeclsD (ctorArgTypes.map fun ty => (`_, fun _ => pure ty)).toArray fun ctorArgs => do
        let mut res ← mkAppM ``Eq #[parsedTesterArg, ← mkAppM' ctorWithParams ctorArgs]
        for ctorArg in ctorArgs do
          res ← mkLambdaFVars #[ctorArg] res
          res ← mkAppM ``Exists #[res]
        return res
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
            else if argType == mkConst ``Bool then mkAppM s2 #[arg]
            else throwError "parseTerm :: {arg} was not be interpreted as Prop or Bool in {e}"
          | mustBeProp =>
            let arg ← parseTerm arg symbolMap mustBeProp
            mkAppM s1 #[arg]
          | mustBeBool =>
            let arg ← parseTerm arg symbolMap mustBeBool
            mkAppM s2 #[arg]
        | _ => throwError "parseTerm :: Invalid unary symbol application {e}"
      | [(s, TwoExactNoConstraint)] =>
        match restVs with
        | [arg1, arg2] =>
          let arg1 ← parseTerm arg1 symbolMap noConstraint
          let arg2 ← parseTerm arg2 symbolMap noConstraint
          match parseTermConstraint with
          | noConstraint => mkAppM s #[arg1, arg2]
          | mustBeProp =>
            let res ← mkAppM s #[arg1, arg2]
            let resType ← inferType res
            if resType.isProp then
              return res
            else if resType == mkConst ``Bool then
              mkAppM ``Eq #[res, mkConst ``true]
            else
              throwError "parseTerm :: {e} is parsed as {res} which is not a Prop"
          | mustBeBool =>
            let res ← mkAppM s #[arg1, arg2]
            let resType ← inferType res
            if resType == mkConst ``Bool then
              return res
            else if resType.isProp then
              mkAppOptM ``decide #[some res, none]
            else
              throwError "parseTerm :: {e} is parsed as {res} which is not a Bool"
        | arg1 :: (arg2 :: restArgs) =>
          -- TODO: Interpret `(< a b c)` as `(and (< a b) (< b c))`
          throwError "parseTerm :: TwoExact symbol with more than two arguments not implemented yet (e: {e})"
        | _ => throwError "parseTerm :: Invalid application {e}"
      | [(s, TwoExactEq)] =>
        match restVs with
        | [arg1, arg2] =>
          let arg1 ← parseTerm arg1 symbolMap noConstraint
          let arg1Type ← inferType arg1
          let res ←
            if arg1Type.isProp then
              let arg2 ← parseTerm arg2 symbolMap mustBeProp -- arg2 needs to be a `Prop` to match arg1
              mkAppM s #[arg1, arg2]
            else if arg1Type == mkConst ``Bool then
              let arg2 ← parseTerm arg2 symbolMap mustBeBool -- arg2 needs to be a `Bool` to match arg1
              mkAppM s #[arg1, arg2]
            else
              let arg2 ← parseTerm arg2 symbolMap noConstraint
              mkAppM s #[arg1, arg2]
          match parseTermConstraint with
          | noConstraint => return res
          | mustBeProp => return res
          | mustBeBool => mkAppOptM ``decide #[some res, none]
        | arg1 :: (arg2 :: restArgs) =>
          -- TODO: Interpret `(= a b c)` as `(and (= a b) (= b c))`
          throwError "parseTerm :: TwoExact symbol with more than two arguments not implemented yet (e: {e})"
        | _ => throwError "parseTerm :: Invalid application {e}"
      | [(s, LeftAssocNoConstraint)] =>
        let res ← parseLeftAssocApp s restVs symbolMap noConstraint
        match parseTermConstraint with
        | noConstraint => return res
        | mustBeProp =>
          let resType ← inferType res
          if resType.isProp then
            return res
          else if resType == mkConst ``Bool then
            mkAppM ``Eq #[res, mkConst ``True]
          else
            throwError "parseTerm :: {e} is parsed as {res} which is not a Prop"
        | mustBeBool =>
          let resType ← inferType res
          if resType == mkConst ``Bool then
            return res
          else if resType.isProp then
            mkAppOptM ``decide #[some res, none]
          else
            throwError "parseTerm :: {e} is parsed as {res} which is not a Bool"
      | [(s1, LeftAssocAllProp), (s2, LeftAssocAllBool)] =>
        match parseTermConstraint with
        | noConstraint => parseLeftAssocApp s1 restVs symbolMap mustBeProp -- Favor `Prop` interpretation over `Bool interpretation
        | mustBeProp => parseLeftAssocApp s1 restVs symbolMap mustBeProp
        | mustBeBool => parseLeftAssocApp s2 restVs symbolMap mustBeBool
      | [(s, Minus)] =>
        match parseTermConstraint with
        | noConstraint =>
          match restVs with -- Subtraction is left associative, but if it takes in just one argument, Minus is interpreted as negation
          | [arg] =>
            let arg ← parseTerm arg symbolMap noConstraint
            mkAppM ``Neg.neg #[arg]
          | _ => parseLeftAssocApp s restVs symbolMap noConstraint
        | mustBeProp => throwError "parseTerm :: {e} has minus as a head symbol which cannot yield a result of type Prop"
        | mustBeBool => throwError "parseTerm :: {e} has minus as a head symbol which cannot yield a result of type Bool"
      | [] =>
        match symbolMap.find? s with
        | some symbolExp =>
          let symbolExpType ← inferType symbolExp
          let expectedArgTypes := getExplicitForallArgumentTypes symbolExpType
          let argConstraints := expectedArgTypes.map
            (fun argType =>
              if argType.isProp then mustBeProp
              else if argType == mkConst ``Bool then mustBeBool
              else noConstraint
            )
          let args ← (restVs.zip argConstraints).mapM (fun (t, argConstraint) => parseTerm t symbolMap argConstraint)
          match parseTermConstraint with
          | noConstraint => mkAppM' symbolExp args.toArray
          | mustBeProp =>
            let res ← mkAppM' symbolExp args.toArray
            let resType ← inferType res
            if resType.isProp then
              return res
            else if resType == mkConst ``Bool then
              mkAppM ``Eq #[res, mkConst ``true]
            else
              throwError "parseTerm :: {e} is parsed as {res} which is not a Prop"
          | mustBeBool =>
            let res ← mkAppM' symbolExp args.toArray
            let resType ← inferType res
            if resType == mkConst ``Bool then
              return res
            else if resType.isProp then
              mkAppOptM ``decide #[some res, none]
            else
              throwError "parseTerm :: {e} is parsed as {res} which is not a Bool"
        | none => throwError "parseTerm :: Unknown symbol {s} in term {e}"
      | _ => throwError "parseTerm :: Unexpected result of smtSymbolToLeanName {s}"
    | _ => throwError "parseTerm :: Invalid term application {e}"
  | _ => throwError "parseTerm :: Invalid term {e}" -- All other atoms shouldn't exist as standalone terms
end

initialize
  registerTraceClass `auto.smt.parseTermErrors

/-- Calls `parseTerm e symbolMap` and returns the result if successful, returning `none` if there is an error -/
def tryParseTerm (e : Term) (symbolMap : HashMap String Expr) : MetaM (Option Expr) := do
  try
    parseTerm e symbolMap noConstraint
  catch err =>
    trace[auto.smt.parseTermErrors] "Error parsing {e}. Error: {err.toMessageData}"
    return none

/-
private def testParseTerm (s : String) (p : String.Pos) : MetaM Expr := do
  match ← lexTerm s p {} with
  | .complete e p =>
    IO.println s!"Lexed term: {e}"
    IO.println s!"Rest of string: {(Substring.toString ⟨s, p, s.endPos⟩)}"
    let constants :=
      #[("P", (Expr.forallE `_ (mkConst ``Int) (.sort .zero) .default)),
        ("x", (mkConst ``Int)), ("y", (mkConst ``Int))]
    withLocalDeclsD (constants.map fun (n, ty) => (n, fun _ => pure ty)) fun _ => do
      let some xDecl := (← getLCtx).findFromUserName? `x
        | throwError "Unknown variable name x"
      let some yDecl := (← getLCtx).findFromUserName? `y
        | throwError "Unknown variable name y"
      let some pDecl := (← getLCtx).findFromUserName? `P
        | throwError "Unknown variable name P"
      let symbolMap : HashMap String Expr := HashMap.empty
      let symbolMap := symbolMap.insert "x" (mkFVar xDecl.fvarId)
      let symbolMap := symbolMap.insert "y" (mkFVar yDecl.fvarId)
      let symbolMap := symbolMap.insert "P" (mkFVar pDecl.fvarId)
      let exp ← parseTerm e symbolMap
      let expType ← inferType exp
      IO.println s!"expType: {expType}"
      IO.println "exp:"
      return exp
  | .malformed .. => throwError "malformed"
  | .incomplete .. => throwError "incomplete"

#eval testParseTerm "(or (not (>= x 0)) (not (>= y 0)) (>= (+ x y) 0))" 0
#eval testParseTerm "(or (P (+ x y)) (not (>= (+ x y) 0)) (not (or (not (>= (+ x y) 0)) (P (+ x y)))))" 0
#eval testParseTerm "(or (not (forall ((z Int)) (or (not (>= z 0)) (P z)))) (or (not (>= (+ x y) 0)) (P (+ x y))))" 0
#eval testParseTerm "(let ((_let_1 (+ x y))) (or (not (forall ((z Int)) (or (not (>= z 0)) (P z)))) (or (not (>= _let_1 0)) (P _let_1))))" 0
#eval testParseTerm "(or (not (exists ((z Int) (q Int)) (or (not (>= z 0)) (P z)))) (or (not (>= (+ x y) 0)) (P (+ x y))))" 0
#eval testParseTerm "(=> (forall ((z Int)) (=> (>= z 0) (P z))) (forall ((z Int)) (or (not (>= z 0)) (P z))))" 0
#eval testParseTerm "(forall ((B0 Bool) (B1 Bool)) (= (=> B0 B1) (or (not B0) B1)))" 0
#eval testParseTerm "(- 3)" 0
-/