import Lean
import Auto.Embedding.LamBVarOp
open Lean

set_option linter.unusedVariables false

namespace Auto.Parser.TPTP

namespace Tokenizer

inductive Status where
  | default
  | ident
  | string
  | comment
  deriving Repr, BEq

inductive Token where
  | op (op : String)
  | ident (ident : String)
  deriving Repr, Inhabited, BEq

def Token.toString : Token → String
| .op a => a
| .ident a => a

structure State where
  status    : Status := .default
  currToken : String := ""
  res       : Array Token := #[]
deriving Repr

def tokens := [
  "@", "|", "&", "<=>", "=>", "<=", "<~>", "~|", "~&", ">", "=", "!=", "!!", "??",
  "~", ",", "(", ")", "*", "!", "?", "^", ":", "[", "]", "!>", ".", "*"
]

def tokenHashMap : Std.HashSet String :=
  Std.HashSet.empty.insertMany tokens

def tokenPrefixes : Std.HashSet String :=
  Std.HashSet.empty.insertMany $ tokens.flatMap (fun t => Id.run do
    let mut res := []
    let mut pref := ""
    for c in t.data do
      pref := pref.push c
      res := pref :: res
    return res
)

abbrev TokenizerM := StateRefT State IO

def setStatus (status : Status) : TokenizerM Unit := do
  modify (fun (s : State) => {s with status := status})

def getStatus : TokenizerM Status := do
  return (← get).status

def addToCurrToken (char : Char) : TokenizerM Unit := do
  modify (fun (s : State) => {s with currToken := s.currToken.push char})

def getCurrToken : TokenizerM String := do
  return (← get).currToken

def addCurrToken : TokenizerM Unit := do
  modify fun (s : State) =>
    {s with
      res := s.res.push $
        match s.status with
        | .default => .op s.currToken
        | .ident => .ident s.currToken
        | .string => .ident s.currToken
        | .comment => panic! s!"Cannot add comment as token"
      currToken := ""
    }

def finalizeToken : TokenizerM Unit := do
  if (← getStatus) == .string || (← getCurrToken) != "" then
    match ← getStatus with
    | .default =>
      if tokenHashMap.contains (← getCurrToken)
      then addCurrToken
      else throw $ IO.userError s!"TPTP.parse :: Invalid token: {(← getCurrToken)}"
    | .ident => addCurrToken
    | .string => addCurrToken
    | .comment => throw $ IO.userError s!"TPTP.parse :: Cannot finalize comment"
    setStatus .default

def tokenizeAux (str : String) : TokenizerM Unit := do
  for char in str.data do
    match ← getStatus with
    | .default =>
      if char.isWhitespace then
        finalizeToken
      else if char.isAlpha || char == '$' then
        finalizeToken
        setStatus .ident
        addToCurrToken char
      else if char == '\'' then
        finalizeToken
        setStatus .string
      else if char == '%' then
        finalizeToken
        setStatus .comment
      else if tokenPrefixes.contains ((← getCurrToken).push char) then
        addToCurrToken char
      else if tokenPrefixes.contains (⟨[char]⟩) then
        finalizeToken
        addToCurrToken char
      else throw $ IO.userError s!"TPTP.parse :: Invalid token: {char}"
    | .ident =>
      if char.isWhitespace then
        finalizeToken
      else if char.isAlphanum || char == '_' then
        addToCurrToken char
      else
        finalizeToken
        addToCurrToken char
        setStatus .default
    | .string =>
      if char == '\'' then
        finalizeToken
      else
        addToCurrToken char
    | .comment =>
      if char == '\n' then
        setStatus .default
  finalizeToken

  def tokenize (s : String) : IO (Array Token) := do
    return (← (tokenizeAux s).run {}).2.res

end Tokenizer

open Tokenizer
/- Pratt parser following `https://matklad.github.io/2020/04/13/simple-but-powerful-pratt-parsing.html`-/

structure State where
  tokens : Array Token
  curr   : Nat := 0
deriving Repr

abbrev ParserM := StateRefT State IO

def isEOF : ParserM Bool := do return (← get).curr ==  (← get).tokens.size

def peek : ParserM Token := do
  let i := (← get).curr
  let ts := (← get).tokens
  if i >= ts.size then throw $ IO.userError "TPTP.parse :: Unexpected end of file"
  return ts[i]!

def peek? : ParserM (Option Token) := do
  if ← isEOF then return none else return ← peek

def next : ParserM Token := do
  let c ← peek
  modify (fun (s : State) => {s with curr := s.curr + 1})
  return c

def infixBindingPower? : String → Option (Nat × Nat)
| "|" | "&" | "<=>" | "=>" | "<=" | "<~>" | "~|" | "~&" | "@" => (60,61)
| "=" | "!=" => (90, 90)
| "*" => (41, 40)
| ">" => (51, 50)
| _ => none

def prefixBindingPower? : String → Option Nat
| "~" => some 70
| _ => none

def binderBindingPower? : String → Option Nat
| "!" | "!>" | "?" | "^" => some 70
| _ => none

def isPolyIL? : String → Bool
| "??" | "!!" | "=" => true
| _ => false

inductive Term where
  | mk : Token → List Term → Term
  deriving Inhabited, BEq

partial def Term.toString : Term → String
| .mk head tail =>
  match tail with
  | .nil => head.toString
  | .cons _ _ => head.toString ++ " [" ++ String.intercalate ", " (tail.map Term.toString) ++ "]"

instance : ToString Term where
  toString := Term.toString

def Term.func : Term → Token := fun ⟨n, _⟩ => n
def Term.args : Term → List Term := fun ⟨_, as⟩ => as

def parseToken (t : Token) : ParserM Unit := do
  let nextToken ← next
  if nextToken != t then throw $ IO.userError s!"TPTP.parse :: Expected '{t.toString}', got '{repr nextToken}'"

def parseIdent : ParserM String := do
  let nextToken ← next
  let .ident id := nextToken
    | throw $ IO.userError s!"TPTP.parse :: Expected identifier, got '{repr nextToken}'"
  return id

partial def parseSep (sep : Token) (p : ParserM α) : ParserM (List α) := do
  let t ← p
  if (← peek?) == some sep then
    parseToken sep
    let l ← parseSep sep p
    return t :: l
  else
    return [t]

mutual
partial def parseTerm (minbp : Nat := 0) : ParserM Term := do
  let lhs ← parseLhs
  let res ← addOpAndRhs lhs minbp
  return res

partial def parseLhs : ParserM Term := do
  let nextToken ← next
  if let .ident _ := nextToken then
    if (← peek?) == some (.op "(") then
      parseToken (.op "(")
      let args ← parseSep (.op ",") (parseTerm 0)
      parseToken (.op ")")
      return Term.mk nextToken args
    else
      return Term.mk nextToken []
  else if nextToken == .op "(" then
    let p ← peek
    if (infixBindingPower? p.toString).isSome then
      -- support for (&) syntax
      let p ← next
      parseToken (.op ")")
      return ⟨p, []⟩
    else
      let lhs ← parseTerm 0
      parseToken (.op ")")
      return lhs
  else if nextToken == .op "[" then
    let args ← parseSep (.op ",") (parseTerm 0)
    parseToken (.op "]")
    return Term.mk nextToken args
  else if let some rbp := binderBindingPower? nextToken.toString then
    parseToken (.op "[")
    let vars ← parseSep (.op ",") parseTypeDecl
    parseToken (.op "]")
    parseToken (.op ":")
    let rhs ← parseTerm rbp
    return Term.mk nextToken (rhs :: vars)
  else if let some rbp := prefixBindingPower? nextToken.toString then
    if (← peek?) == .some (.op ")") then -- support for `(~)` syntax
      return Term.mk nextToken []
    else
      let rhs ← parseTerm rbp
      return Term.mk nextToken [rhs]
  else if isPolyIL? nextToken.toString && (← peek?) == .some (.op ")") then
    return Term.mk nextToken []
  else
    throw $ IO.userError s!"TPTP.parse :: Expected term, got '{repr nextToken}'"

partial def addOpAndRhs (lhs : Term) (minbp : Nat) : ParserM Term := do
  if ← isEOF then
    return lhs
  else
    let op ← peek
    let some (lbp, rbp) := infixBindingPower? op.toString
      | return lhs
    if lbp < minbp then
      return lhs
    else
      let op ← next
      let rhs ← parseTerm rbp
      return ← addOpAndRhs (Term.mk op [lhs, rhs]) minbp

partial def parseTypeDecl : ParserM Term := do
  let ident ← parseIdent
  if (← peek?) == some (.op ":") then
    parseToken (.op ":")
    let ty ← parseTerm
    return Term.mk (.ident ident) [ty]
  else
    return Term.mk (.ident ident) []
end

/--
  <thf_atom_typing>
  <tff_atom_typing>
-/
partial def parseAtomTyping : ParserM Term := do
  if (← peek?) == .some (.op "(") then
    parseToken (.op "(")
    let decl ← parseAtomTyping
    parseToken (.op ")")
    return decl
  else
    parseTypeDecl

structure Command where
  cmd : String
  args : List Term
deriving Inhabited, BEq

def Command.toString : Command → String
| .mk cmd args => cmd ++ "(" ++ String.intercalate ", " (args.map Term.toString) ++ ")"

instance : ToString Command where
  toString := Command.toString

def parseCommand : ParserM Command := do
  let cmd ← parseIdent
  match cmd with
  | "thf" | "tff" | "cnf" | "fof" =>
    parseToken (.op "(")
    let name ← parseIdent
    parseToken (.op ",")
    let kind ← parseIdent
    parseToken (.op ",")
    let val ← match kind with
    | "type" => parseAtomTyping
    | _ => parseTerm
    if (← peek?) == some (.op ",") then
      parseToken (.op ",")
      discard $ parseTerm
    parseToken (.op ")")
    parseToken (.op ".")
    return ⟨cmd, [Term.mk (.ident name) [], Term.mk (.ident kind) [], val]⟩
  | "include" =>
    parseToken (.op "(")
    let str ← parseIdent
    parseToken (.op ")")
    parseToken (.op ".")
    return ⟨cmd, [Term.mk (.ident str) []]⟩
  | _ => throw $ IO.userError s!"Command '{cmd}' not supported"

partial def parseCommands : ParserM (List Command) := do
  if ← isEOF
  then return []
  else
    let c ← parseCommand
    return c :: (← parseCommands)

def parse (s : String) : IO (Array Command) := do
  let tokens ← Tokenizer.tokenize s
  let res ← parseCommands.run {tokens}
  return (Array.mk res.fst)

open Embedding.Lam in
def ident2LamSort (s : String) : Option LamSort :=
  match s with
  | "s_nat"    => .some (.base .nat)
  | "s_int"    => .some (.base .int)
  | "s_string" => .some (.base .string)
  | "s_empty"  => .some (.base .empty)
  | _ =>
    if s.take 3 == "s_a" then
      match (s.drop 3).toNat? with
      | .some n => .some (.atom n)
      | .none => .none
    else if s.take 4 == "s_bv" then
      match (s.drop 4).toNat? with
      | .some n => .some (.base (.bv n))
      | .none   => .none
    else
      .none

open Embedding.Lam in
def ident2NatConst (s : String) : Option NatConst :=
  match s with
  | "t_nadd" => .some .nadd
  | "t_nsub" => .some .nsub
  | "t_nmul" => .some .nmul
  | "t_ndiv" => .some .ndiv
  | "t_nmod" => .some .nmod
  | "t_nle"  => .some .nle
  | "t_nlt"  => .some .nlt
  | "t_nmax" => .some .nmax
  | "t_nmin" => .some .nmin
  | _ =>
    match s.take 9 with
    | "t_natVal_" =>
      match (s.drop 9).toNat? with
      | .some n => .some (.natVal n)
      | .none   => .none
    | _ => .none

open Embedding.Lam in
def ident2StringConst (s : String) : Option StringConst :=
  match s with
  | "t_slength"   => .some .slength
  | "t_sapp"      => .some .sapp
  | "t_sle"       => .some .sle
  | "t_slt"       => .some .slt
  | "t_sprefixof" => .some .sprefixof
  | "t_srepall"   => .some .srepall
  | _ =>
    let foldFn (x : Option String) (y : String) : Option String :=
      match x, y.toNat? with
      | .some l, .some y' => .some (l.push (Char.ofNat y'))
      | _,       _        => .none
    match s.take 9, (((s.drop 9).splitOn "d").drop 1).foldl foldFn (.some "") with
    | "t_strVal_", .some s => .some (.strVal s)
    | _,         _       => .none

open Embedding.Lam in
def ident2IntConst (s : String) : Option IntConst :=
  match s with
  | "t_iofNat"   => .some .iofNat
  | "t_inegSucc" => .some .inegSucc
  | "t_ineg"     => .some .ineg
  | "t_iabs"     => .some .iabs
  | "t_iadd"     => .some .iadd
  | "t_isub"     => .some .isub
  | "t_imul"     => .some .imul
  | "t_idiv"     => .some .idiv
  | "t_imod"     => .some .imod
  | "t_iediv"    => .some .iediv
  | "t_iemod"    => .some .iemod
  | "t_ile"      => .some .ile
  | "t_ilt"      => .some .ilt
  | "t_imax"     => .some .imax
  | "t_imin"     => .some .imin
  | _ => .none

open Embedding.Lam in
def ident2BitVecConst (s : String) : Option BitVecConst :=
  match s.take 7 with
  | "t_bvVal" =>
    match (s.drop 7).splitOn "_" with
    | ["", ns, is] =>
      match ns.toNat?, is.toNat? with
      | .some n, .some i => .some (.bvVal n i)
      | _,       _       => .none
    | _ => .none
  | "t_bvofN" =>
    match s.take 10 == "t_bvofNat_", (s.drop 10).toNat? with
    | true, .some n => .some (.bvofNat n)
    | _,    _       => .none
  | "t_bvtoN" =>
    match s.take 10 == "t_bvtoNat_", (s.drop 10).toNat? with
    | true, .some n => .some (.bvtoNat n)
    | _,    _       => .none
  | "t_bvofI" =>
    match s.take 10 == "t_bvofInt_", (s.drop 10).toNat? with
    | true, .some n => .some (.bvofInt n)
    | _,    _       => .none
  | "t_bvtoI" =>
    match s.take 10 == "t_bvtoInt_", (s.drop 10).toNat? with
    | true, .some n => .some (.bvtoInt n)
    | _,    _       => .none
  | "t_bvmsb" =>
    match s.get ⟨7⟩, (s.drop 8).toNat? with
    | '_', .some n => .some (.bvmsb n)
    | _,   _       => .none
  | "t_bvadd" =>
    match s.get ⟨7⟩, (s.drop 8).toNat? with
    | '_', .some n => .some (.bvadd n)
    | _,   _       => .none
  | "t_bvsub" =>
    match s.get ⟨7⟩, (s.drop 8).toNat? with
    | '_', .some n => .some (.bvsub n)
    | _,   _       => .none
  | "t_bvneg" =>
    match s.get ⟨7⟩, (s.drop 8).toNat? with
    | '_', .some n => .some (.bvneg n)
    | _,   _       => .none
  | "t_bvabs" =>
    match s.get ⟨7⟩, (s.drop 8).toNat? with
    | '_', .some n => .some (.bvabs n)
    | _,   _       => .none
  | "t_bvmul" =>
    match s.get ⟨7⟩, (s.drop 8).toNat? with
    | '_', .some n => .some (.bvmul n)
    | _,   _       => .none
  | "t_bvudi" =>
    match s.take 9, (s.drop 8).toNat? with
    | "t_bvudiv_", .some n => .some (.bvudiv n)
    | _,           _       => .none
  | "t_bvure" =>
    match s.take 9, (s.drop 8).toNat? with
    | "t_bvurem_", .some n => .some (.bvurem n)
    | _,           _       => .none
  | "t_bvsdi" =>
    match s.take 9, (s.drop 8).toNat? with
    | "t_bvsdiv_", .some n => .some (.bvsdiv n)
    | _,           _       => .none
  | "t_bvsre" =>
    match s.take 9, (s.drop 8).toNat? with
    | "t_bvsrem_", .some n => .some (.bvsrem n)
    | _,           _       => .none
  | "t_bvsmo" =>
    match s.take 9, (s.drop 8).toNat? with
    | "t_bvsmod_", .some n => .some (.bvsmod n)
    | _,           _       => .none
  | "t_bvult" =>
    match s.get ⟨7⟩, (s.drop 8).toNat? with
    | '_', .some n => .some (.bvult n)
    | _,   _       => .none
  | "t_bvule" =>
    match s.get ⟨7⟩, (s.drop 8).toNat? with
    | '_', .some n => .some (.bvule n)
    | _,   _       => .none
  | "t_bvslt" =>
    match s.get ⟨7⟩, (s.drop 8).toNat? with
    | '_', .some n => .some (.bvslt n)
    | _,   _       => .none
  | "t_bvsle" =>
    match s.get ⟨7⟩, (s.drop 8).toNat? with
    | '_', .some n => .some (.bvsle n)
    | _,   _       => .none
  | "t_bvand" =>
    match s.get ⟨7⟩, (s.drop 8).toNat? with
    | '_', .some n => .some (.bvand n)
    | _,   _       => .none
  | "t_bvor_" =>
    match (s.drop 8).toNat? with
    | .some n => .some (.bvor n)
    | _       => .none
  | "t_bvxor" =>
    match s.get ⟨7⟩, (s.drop 8).toNat? with
    | '_', .some n => .some (.bvxor n)
    | _,   _       => .none
  | "t_bvnot" =>
    match s.get ⟨7⟩, (s.drop 8).toNat? with
    | '_', .some n => .some (.bvnot n)
    | _,   _       => .none
  | "t_bvshl" =>
    match s.get ⟨7⟩, (s.drop 8).toNat? with
    | '_', .some n => .some (.bvshl n)
    | _,   _       => .none
  | "t_bvlsh" =>
    match s.take 9, (s.drop 8).toNat? with
    | "t_bvlshr_", .some n => .some (.bvlshr n)
    | _,           _       => .none
  | "t_bvash" =>
    match s.take 9, (s.drop 8).toNat? with
    | "t_bvashr_", .some n => .some (.bvashr n)
    | _,           _       => .none
  | "t_bvsmt" =>
    match (s.drop 7).take 4 with
    | "shl_" =>
      match (s.drop 11).toNat? with
      | .some n => .some (.bvsmtshl n)
      | .none   => .none
    | _ =>
      match (s.drop 7).take 5, (s.drop 12).toNat? with
      | "lshr", .some n => .some (.bvsmtlshr n)
      | "ashr", .some n => .some (.bvsmtashr n)
      | _,      _       => .none
  | "t_bvapp" =>
    match s.take 11, (s.drop 11).splitOn "_" with
    | "t_bvappend_", [ns, ms] =>
      match ns.toNat?, ms.toNat? with
      | .some n, .some m => .some (.bvappend n m)
      | _,       _       => .none
    | _,             _        => .none
  | "t_bvext" =>
    match s.take 12, (s.drop 12).splitOn "_" with
    | "t_bvextract_", [ns, hs, ls] =>
      match ns.toNat?, hs.toNat?, ls.toNat? with
      | .some n, .some h, .some l => .some (.bvextract n h l)
      | _,       _,       _       => .none
    | _,              _            => .none
  | "t_bvrep" =>
    match s.take 11, (s.drop 11).splitOn "_" with
    | "t_bvrepeat_", [ws, is] =>
      match ws.toNat?, is.toNat? with
      | .some w, .some i => .some (.bvrepeat w i)
      | _,       _       => .none
    | _,             _        => .none
  | "t_bvzer" =>
    match s.take 15, (s.drop 15).splitOn "_" with
    | "t_bvzeroExtend_", [ws, vs] =>
      match ws.toNat?, vs.toNat? with
      | .some w, .some v => .some (.bvzeroExtend w v)
      | _,       _       => .none
    | _,             _        => .none
  | "t_bvsig" =>
    match s.take 15, (s.drop 15).splitOn "_" with
    | "t_bvsignExtend_", [ws, vs] =>
      match ws.toNat?, vs.toNat? with
      | .some w, .some v => .some (.bvsignExtend w v)
      | _,       _       => .none
    | _,             _        => .none
  | _ => .none

open Embedding.Lam in
inductive LamConstr where
  | error : String → LamConstr
  | kind  : LamConstr
  | sort  : LamSort → LamConstr
  | term  : LamSort → LamTerm → LamConstr
  deriving Inhabited, Hashable, BEq

def LamConstr.toString : LamConstr → String
| .error s => s!"error {s}"
| .kind    => "kind"
| .sort s  => s!"sort {s}"
| .term s t => s!"term {t} : {s}"

instance : ToString LamConstr where
  toString := LamConstr.toString

open Embedding.Lam in
structure ParsingInfo where
  lamVarTy     : Array LamSort
  lamEVarTy    : Array LamSort
  proverSkolem : Std.HashMap String (LamSort × Nat) := {}

open Embedding.Lam in
def ParsingInfo.toLamTyVal (pi : ParsingInfo) : LamTyVal :=
  ⟨fun n => pi.lamVarTy.getD n (.base .prop),
   fun _ => .base .prop,
   fun n => pi.lamEVarTy.getD n (.base .prop)⟩

open Embedding.Lam in
def ParsingInfo.addSkolem (pi : ParsingInfo) (name : String) (s : LamSort) :=
  {pi with proverSkolem := pi.proverSkolem.insert name (s, pi.proverSkolem.size)}

open Embedding.Lam in
def LamConstr.ofBaseTerm (pi : ParsingInfo) (b : LamBaseTerm) : LamConstr :=
  .term (b.lamCheck pi.toLamTyVal) (.base b)

open Embedding.Lam in
def ident2LamConstr (pi : ParsingInfo) (s : String) : LamConstr :=
  match pi.proverSkolem.get? s with
  | .some (s, n) => .term s (.etom (n + pi.lamEVarTy.size))
  | .none =>
    match s.get ⟨0⟩ with
    | 's' =>
      match ident2LamSort s with
      | .some b => .sort b
      | _       => .error s!"Unknown identifier {s}"
    | 't' =>
      match s.take 3 with
      | "t_a" =>
        match (s.drop 3).toNat? with
        | .some n =>
          match pi.lamVarTy[n]? with
          | .some s => .term s (.atom n)
          | .none => .error s!"Unknown atom {n}"
        | .none   => .error s!"Unknown identifier {s}"
      | "t_e" =>
        match (s.drop 3).toNat? with
        | .some n =>
          match pi.lamEVarTy[n]? with
          | .some s => .term s (.etom n)
          | .none   => .error s!"Unknown etom {n}"
        | .none   => .error s!"Unknown identifier {s}"
      | "t_n" =>
        match ident2NatConst s with
        | .some n => .term n.lamCheck (.base (.ncst n))
        | .none   => .error s!"Unknown identifier {s}"
      | "t_i" =>
        match ident2IntConst s with
        | .some i => .term i.lamCheck (.base (.icst i))
        | .none   => .error s!"Unknown identifier {s}"
      | "t_s" =>
        match ident2StringConst s with
        | .some s => .term s.lamCheck (.base (.scst s))
        | .none   => .error s!"Unknown identifier {s}"
      | "t_b" =>
        match ident2BitVecConst s with
        | .some bv => .term bv.lamCheck (.base (.bvcst bv))
        | .none   => .error s!"Unknown identifier {s}"
      | _ => .error s!"Unknown identifier {s}"
    | _   => .error s!"Unknown identifier {s}"

open Embedding.Lam in
/-- This function is only for zipperposition's output -/
partial def term2LamTerm (pi : ParsingInfo) (t : Term) (lctx : Std.HashMap String (Nat × LamSort) := {}) : LamConstr :=
  match t with
  | ⟨.ident "$i", []⟩ => .error "Does not have iota"
  | ⟨.ident "$tType", []⟩ => .kind
  | ⟨.ident "$o", []⟩ => .sort (.base .prop)
  | ⟨.ident "$true", []⟩ => .term (.base .prop) (.base .trueE)
  | ⟨.ident "$false", []⟩ => .term (.base .prop) (.base .falseE)
  | ⟨.ident ids, as⟩ =>
    let head :=
      match deBruijnAndSort? lctx ids with
      | .some (db, s) => .term s (.bvar db)
      | .none => ident2LamConstr pi ids
    match as with
    | .nil => head
    | .cons _ _ => lamConstrMkAppN head (as.map (term2LamTerm pi · lctx))
  | ⟨.op "!", body :: var :: tail⟩ =>
    match processVar pi var lctx with
    | .some (name, s) =>
      match term2LamTerm pi ⟨.op "!", body :: tail⟩ (lctx.insert name (lctx.size, s)) with
      | .term (.base .prop) body => .term (.base .prop) (.mkForallEF s body)
      | r => .error s!"Unexpected term {t} produces ({r})"
    | r => .error s!"Unexpected term {t} produces ({r})"
  | ⟨.op "!>", body :: var :: tail⟩ =>
    match processVar pi var lctx with
    | .some (name, s) =>
      match term2LamTerm pi ⟨.op "!>", body :: tail⟩ (lctx.insert name (lctx.size, s)) with
      | .term (.base .prop) body => .term (.base .prop) (.mkForallEF s body)
      | r => .error s!"Unexpected term {t} produces ({r})"
    | r => .error s!"Unexpected term {t} produces ({r})"
  | ⟨.op "^", body :: var :: tail⟩ =>
    match processVar pi var lctx with
    | .some (name, s) =>
      match term2LamTerm pi ⟨.op "^", body :: tail⟩ (lctx.insert name (lctx.size, s)) with
      | .term resTy body => .term (.func s resTy) (.lam s body)
      | r => .error s!"Unexpected term {t} produces ({r})"
    | r => .error s!"Unexpected term {t} produces ({r})"
  | ⟨.op "?", body :: var :: tail⟩ =>
    match processVar pi var lctx with
    | .some (name, s) =>
      match term2LamTerm pi ⟨.op "?", body :: tail⟩ (lctx.insert name (lctx.size, s)) with
      | .term (.base .prop) body => .term (.base .prop) (.mkExistEF s body)
      | r => .error s!"Unexpected term {t} produces ({r})"
    | r => .error s!"Unexpected term {t} produces ({r})"
  | ⟨.op "!", body :: []⟩ | ⟨.op "!>", body :: []⟩ | ⟨.op "^", body :: []⟩ | ⟨.op "?", body :: []⟩ =>
    term2LamTerm pi body lctx
  | ⟨.op "~", [a]⟩     =>
    match term2LamTerm pi a lctx with
    | .term (.base .prop) la => .term (.base .prop) (.mkNot la)
    | r => .error s!"Unexpected term {t} produces ({r})"
  | ⟨.op "|", [a,b]⟩   =>
    match term2LamTerm pi a lctx, term2LamTerm pi b lctx with
    | .term (.base .prop) la, .term (.base .prop) lb => .term (.base .prop) (.mkOr la lb)
    | r₁, r₂ => .error s!"Unexpected term {t} produces ({r₁}) and ({r₂})"
  | ⟨.op "&", [a,b]⟩   =>
    match term2LamTerm pi a lctx, term2LamTerm pi b lctx with
    | .term (.base .prop) la, .term (.base .prop) lb => .term (.base .prop) (.mkAnd la lb)
    | r₁, r₂ => .error s!"Unexpected term {t} produces ({r₁}) and ({r₂})"
  | ⟨.op "<=>", [a,b]⟩ =>
    match term2LamTerm pi a lctx, term2LamTerm pi b lctx with
    | .term (.base .prop) la, .term (.base .prop) lb => .term (.base .prop) (.mkIff la lb)
    | r₁, r₂ => .error s!"Unexpected term {t} produces ({r₁}) and ({r₂})"
  | ⟨.op "!=", [a,b]⟩  =>
    match term2LamTerm pi a lctx, term2LamTerm pi b lctx with
    | .term s₁ la, .term s₂ lb =>
      match s₁.beq s₂ with
      | true => .term (.base .prop) (.mkNot (.mkEq s₁ la lb))
      | false => .error s!"Application type mismatch in {t}"
    | r₁, r₂ => .error s!"Unexpected term {t} produces ({r₁}) and ({r₂})"
  | ⟨.op "=", [a,b]⟩   =>
    match term2LamTerm pi a lctx, term2LamTerm pi b lctx with
    | .term s₁ la, .term s₂ lb =>
      match s₁.beq s₂ with
      | true => .term (.base .prop) (.mkEq s₁ la lb)
      | false => .error s!"Application type mismatch in {t}"
    | r₁, r₂ => .error s!"Unexpected term {t} produces ({r₁}) and ({r₂})"
  | ⟨.op "~|", [a,b]⟩  =>
    match term2LamTerm pi a lctx, term2LamTerm pi b lctx with
    | .term (.base .prop) la, .term (.base .prop) lb =>
      .term (.base .prop) (.mkNot (.mkOr la lb))
    | r₁, r₂ => .error s!"Unexpected term {t} produces ({r₁}) and ({r₂})"
  | ⟨.op "~&", [a,b]⟩  =>
    match term2LamTerm pi a lctx, term2LamTerm pi b lctx with
    | .term (.base .prop) la, .term (.base .prop) lb =>
      .term (.base .prop) (.mkNot (.mkAnd la lb))
    | r₁, r₂ => .error s!"Unexpected term {t} produces ({r₁}) and ({r₂})"
  | ⟨.op "<~>", [a,b]⟩ =>
    match term2LamTerm pi a lctx, term2LamTerm pi b lctx with
    | .term (.base .prop) la, .term (.base .prop) lb =>
      .term (.base .prop) (.mkNot (.mkIff la lb))
    | r₁, r₂ => .error s!"Unexpected term {t} produces ({r₁}) and ({r₂})"
  | ⟨.op "@", [a,b]⟩   =>
    match term2LamTerm pi b lctx with
    | .term argTy' lb =>
      match isPolyIL? a.toString with
      | true =>
        if a.toString == "=" then
          .term (.base .prop) (.app argTy' (.base (.eq argTy')) lb)
        else
          match argTy' with
          | .func domTy (.base .prop) =>
            let b := if a.toString == "??" then .existE domTy else .forallE domTy
            .term (.base .prop) (.app argTy' (.base b) lb)
          | _ => .error s!"Invalid argument type for {a.toString}"
      | false =>
        match term2LamTerm pi a lctx with
        | .term fnTy la =>
          match fnTy with
          | .func argTy resTy =>
            match argTy.beq argTy' with
            | true => .term resTy (.app argTy la lb)
            | false => .error s!"Application type mismatch ({fnTy} applied to {argTy'}) in {t}"
          | _ => .error s!"Non-function type {fnTy} applied to arg in {t}"
        | r => .error s!"Unexpected term {t} produces ({r}) at appFn"
    | r => .error s!"Unexpected term {t} produces ({r}) at appArg"
  | ⟨.op "=>", [a,b]⟩ | ⟨.op "<=", [b,a]⟩ =>
    match term2LamTerm pi a lctx, term2LamTerm pi b lctx with
    | .term (.base .prop) la, .term (.base .prop) lb => .term (.base .prop) (.mkImp la lb)
    | r₁, r₂ => .error s!"Unexpected term {t} produces ({r₁}) and ({r₂})"
  | ⟨.op "~", []⟩   => .ofBaseTerm pi .not
  | ⟨.op "|", []⟩   => .ofBaseTerm pi .or
  | ⟨.op "&", []⟩   => .ofBaseTerm pi .and
  | ⟨.op "<=>", []⟩ => .ofBaseTerm pi .iff
  | ⟨.op "!=", []⟩  => .error s!"Unapplied (!=), cannot infer type"
  | ⟨.op "=", []⟩   => .error s!"Unapplied (=), cannot infer type"
  | ⟨.op "!!", []⟩  => .error s!"Unapplied (!!), cannot infer type"
  | ⟨.op "??", []⟩  => .error s!"Unapplied (??), cannot infer type"
  | ⟨.op "~|", []⟩  => .term (.func (.base .prop) (.func (.base .prop) (.base .prop)))
    (.lam (.base .prop) (.lam (.base .prop) (.mkNot (.mkOr (.bvar 1) (.bvar 0)))))
  | ⟨.op "~&", []⟩  => .term (.func (.base .prop) (.func (.base .prop) (.base .prop)))
    (.lam (.base .prop) (.lam (.base .prop) (.mkNot (.mkAnd (.bvar 1) (.bvar 0)))))
  | ⟨.op "<~>", []⟩ => .term (.func (.base .prop) (.func (.base .prop) (.base .prop)))
    (.lam (.base .prop) (.lam (.base .prop) (.mkNot (.mkIff (.bvar 1) (.bvar 0)))))
  | ⟨.op "=>", []⟩  => .ofBaseTerm pi .imp
  | ⟨.op "<=", []⟩  => .term (.func (.base .prop) (.func (.base .prop) (.base .prop)))
    (.lam (.base .prop) (.lam (.base .prop) (.mkImp (.bvar 0) (.bvar 1))))
  | ⟨.op ">", [⟨.op "*", [a, b]⟩, c]⟩   =>
    term2LamTerm pi ⟨.op ">", [a, ⟨.op ">", [b, c]⟩]⟩ lctx
  | ⟨.op ">", [a, b]⟩ =>
    match term2LamTerm pi a lctx, term2LamTerm pi b lctx with
    | .sort sa, .sort sb => .sort (.func sa sb)
    | _, r => .error s!"Unexpected term {t} produces ({r})"
  | _ => .error s!"term2LamTerm :: Could not translate to Lean Expr: {t}"
where
  processVar (pi : ParsingInfo) (var : Term) (lctx : Std.HashMap String (Nat × LamSort)) : Option (String × LamSort) :=
    match var with
    | ⟨.ident v, ty⟩ =>
      match ty with
      | [ty] =>
        match term2LamTerm pi ty lctx with
        | .sort s => .some (v, s)
        | _ => .none
      | _ => .none
    | _ => .none
  deBruijnAndSort? (lctx : Std.HashMap String (Nat × LamSort)) (id : String) : Option (Nat × LamSort) :=
    match lctx.get? id with
    | .some (n, s) => (lctx.size - 1 - n, s)
    | .none => none
  lamConstrMkAppN (head : LamConstr) (args : List LamConstr) :=
    match head, args with
    | .term s₁ t₁, .nil => .term s₁ t₁
    | .term s₁ t₁, .cons (.term s₂ t₂) tail =>
      match s₁ with
      | .func argTy resTy =>
        match argTy.beq s₂ with
        | true => lamConstrMkAppN (.term resTy (.app s₂ t₁ t₂)) tail
        | false => .error s!"term2LamTerm :: Application type ({s₁} applied to {s₂}) mismatch in lamConstrMkAppN, `{head}` `{args}`"
      | _ => .error s!"term2LamTerm :: Non-function head `{head}` applied to argument"
    | _, _ => .error s!"term2LamTerm :: Unexpected input `{head}`, `{args}` to lamConstrMkAppN"

open Embedding.Lam in
/--
  Turn TSTP term into LamSort/LamTerm
  This function is only for zipperposition's output
-/
def getProof (lamVarTy lamEVarTy : Array LamSort) (cmds : Array Command) : MetaM (Array LamTerm) := do
  let mut ret := #[]
  let mut pi : ParsingInfo := ⟨lamVarTy, lamEVarTy, {}⟩
  for ⟨cmd, args⟩ in cmds do
    match cmd with
    | "thf" | "tff" | "cnf" | "fof" =>
      match args with
      | [⟨.ident name, []⟩, ⟨.ident kind, _⟩, val] =>
        if kind != "type" then
          match term2LamTerm pi val with
          | .term (.base .prop) t =>
            ret := ret.push t
          | .error e => throwError (decl_name% ++ " :: " ++ e)
          | lc => throwError "{decl_name%} :: Unexpected LamConstr {lc}, expected term"
        else
          match val with
          | ⟨.ident name, [ty]⟩ =>
            -- In zipperposition, skolems start with `sk_` or `#sk_`
            if name.take 3 == "sk_" || name.take 3 == "#sk" then
              match term2LamTerm pi ty with
              | .sort s => pi := pi.addSkolem name s
              | lc => throwError "{decl_name%} :: Unexpected LamConstr {lc}, expected sort"
            else
              continue
          | _ => continue
      | _ => continue
    | "include" => throwError "{decl_name%} :: `include` should not occur in proof output of TPTP solvers"
    | _ => throwError "{decl_name%} :: Unknown command {cmd}"
  return ret

/-- Returns the unsat core of an array of TSTP steps -/
def unsatCore (cmds : Array Command) : MetaM (Array Nat) := do
  let mut res := #[]
  for ⟨_, args⟩ in cmds do
    if args.length > 1 then
      if let ⟨.ident kind, []⟩ := args[1]! then
        if ["axiom", "conjecture", "negated_conjecture"].contains kind then
          if let ⟨.ident id, []⟩ := args[0]! then
            if id.take 4 == "fact" then
              if let .some n := (id.drop 4).toNat? then
                res := res.push n
  return res

end TPTP
