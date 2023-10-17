import Lean
import Auto.Embedding.LamBase
open Lean

namespace Auto.Parser.TPTP

namespace Tokenizer

inductive Status :=
| default
| ident
| string
| comment
deriving Repr, BEq

inductive Token :=
| op (op : String)
| ident (ident : String)
deriving Repr, Inhabited, BEq

def Token.toString : Token → String
| .op a => a
| .ident a => a

structure State where
(status : Status := .default)
(currToken : String := "")
(res : Array Token := #[])
deriving Repr

def tokens := [
  "@", "|", "&", "<=>", "=>", "<=", "<~>", "~|", "~&", ">", "=", "!=",
  "~", ",", "(", ")", "*", "!", "?", "^", ":", "[", "]", "!>", ".", "*"
] -- TODO: Add ?? and !!

def tokenHashMap : HashSet String := 
  HashSet.empty.insertMany tokens

def tokenPrefixes : HashSet String := 
  HashSet.empty.insertMany $ tokens.bind (fun t => Id.run do
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
      else throw $ IO.userError s!"Invalid token: {(← getCurrToken)}"
    | .ident => addCurrToken
    | .string => addCurrToken
    | .comment => throw $ IO.userError s!"Cannot finalize comment"
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
      else throw $ IO.userError s!"Invalid token: {char}"
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
(tokens : Array Token)
(curr : Nat := 0)
deriving Repr


abbrev ParserM := StateRefT State IO

def isEOF : ParserM Bool := do return (← get).curr ==  (← get).tokens.size

def peek : ParserM Token := do
  let i := (← get).curr
  let ts := (← get).tokens
  if i >= ts.size then throw $ IO.userError "Unexpected end of file"
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

def BinderBindingPower? : String → Option Nat
| "!" | "!>" | "?" | "^" => some 70
| _ => none

inductive Term where
| mk : Token → List Term → Term
deriving Inhabited, Repr, BEq

def Term.func : Term → Token := fun ⟨n, _⟩ => n
def Term.args : Term → List Term := fun ⟨_, as⟩ => as

def parseToken (t : Token) : ParserM Unit := do
  let nextToken ← next
  if nextToken != t then throw $ IO.userError s!"Expected '{t.toString}', got '{repr nextToken}'"

def parseIdent : ParserM String := do
  let nextToken ← next
  let .ident id := nextToken
    | throw $ IO.userError s!"Expected identifier, got '{repr nextToken}'"
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
  else if let some rbp := BinderBindingPower? nextToken.toString then
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
  else
    throw $ IO.userError s!"Expected term, got '{repr nextToken}'"

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

structure Command where
(cmd : String)
(args : List Term)
deriving Repr

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
    | "type" => parseTypeDecl
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
  | _ => throw $ IO.userError "Command '{cmd}' not supported"

partial def parseCommands : ParserM (List Command) := do
  if ← isEOF 
  then return []
  else
    let c ← parseCommand
    return c :: (← parseCommands)

def parse (s : String) : IO (List Command) := do
  let tokens ← Tokenizer.tokenize s
  let res ← parseCommands.run {tokens}
  return res.1

open Embedding.Lam in
partial def term2LamTerm : Term → Except String LamTerm := fun _ => sorry
-- | ⟨.ident "$i", []⟩ =>
--   .error "term2LamTerm :: Does not support iota"
-- | ⟨.ident "$tType", []⟩ => mkSort levelOne
-- | ⟨.ident "$o", []⟩ => .ok (.base .prop)
-- | ⟨.ident "$true", []⟩ => mkConst `True
-- | ⟨.ident "$false", []⟩ => mkConst `False
-- | ⟨.ident n, as⟩ => do
--   let some decl := (← getLCtx).findFromUserName? n
--     | throwError "Unknown variable name {n}"
--   mkAppN (mkFVar decl.fvarId) (← as.mapM toLeanExpr).toArray
-- | ⟨.op "!", body :: var :: tail⟩ =>
--   withVar var fun v => do
--     mkForallFVars #[v] (← toLeanExpr ⟨.op "!", body :: tail⟩)
-- | ⟨.op "!>", body :: var :: tail⟩ =>
--   withVar var fun v => do
--     mkForallFVars #[v] (← toLeanExpr ⟨.op "!>", body :: tail⟩)
-- | ⟨.op "^", body :: var :: tail⟩ =>
--   withVar var fun v => do
--     mkLambdaFVars #[v] (← toLeanExpr ⟨.op "^", body :: tail⟩)
-- | ⟨.op "?", body :: var :: tail⟩ =>
--   withVar var fun v => do
--     mkAppM `Exists #[← mkLambdaFVars #[v] (← toLeanExpr ⟨.op "?", body :: tail⟩)]
-- | ⟨.op "!", body :: []⟩ | ⟨.op "!>", body :: []⟩ | ⟨.op "^", body :: []⟩ | ⟨.op "?", body :: []⟩ =>
--   body.toLeanExpr
-- | ⟨.op "~", [a]⟩     => mkAppM `Not #[← a.toLeanExpr]
-- | ⟨.op "|", [a,b]⟩   => mkAppM `Or (← [a,b].mapM toLeanExpr).toArray
-- | ⟨.op "&", [a,b]⟩   => mkAppM `And (← [a,b].mapM toLeanExpr).toArray
-- | ⟨.op "<=>", [a,b]⟩ => mkAppM `Iff (← [a,b].mapM toLeanExpr).toArray
-- | ⟨.op "!=", [a,b]⟩  => mkAppM `Ne (← [a,b].mapM toLeanExpr).toArray
-- | ⟨.op "=", [a,b]⟩   => mkAppM `Eq (← [a,b].mapM toLeanExpr).toArray
-- | ⟨.op "~|", [a,b]⟩  => mkAppM ``Not #[← mkAppM `Or (← [a,b].mapM toLeanExpr).toArray]
-- | ⟨.op "~&", [a,b]⟩  => mkAppM ``Not #[← mkAppM `And (← [a,b].mapM toLeanExpr).toArray]
-- | ⟨.op "<~>", [a,b]⟩ => mkAppM ``Not #[← mkAppM `Iff (← [a,b].mapM toLeanExpr).toArray]
-- | ⟨.op "@", [a,b]⟩   => mkApp (← a.toLeanExpr) (← b.toLeanExpr)
-- | ⟨.op "=>", [a,b]⟩ | ⟨.op "<=", [b,a]⟩ => mkArrow (← a.toLeanExpr) (← b.toLeanExpr)
-- | ⟨.op "~", []⟩   => pure $ mkConst `Not
-- | ⟨.op "|", []⟩   => pure $ mkConst `Or
-- | ⟨.op "&", []⟩   => pure $ mkConst `And
-- | ⟨.op "<=>", []⟩ => pure $ mkConst `Iff
-- | ⟨.op "!=", []⟩  => pure $ mkConst `Ne
-- | ⟨.op "=", []⟩   => pure $ mkConst `Eq
-- | ⟨.op "~|", []⟩  => pure $ mkLambda `x .default (mkSort levelZero) $
--                        mkLambda `y .default (mkSort levelZero) $ 
--                          mkAppN (mkConst ``Not) #[mkAppN (mkConst ``Or) #[.bvar 1, .bvar 0]]
-- | ⟨.op "~&", []⟩  => pure $ mkLambda `x .default (mkSort levelZero) $
--                        mkLambda `y .default (mkSort levelZero) $ 
--                          mkAppN (mkConst ``Not) #[mkAppN (mkConst ``And) #[.bvar 1, .bvar 0]]
-- | ⟨.op "<~>", []⟩  => pure $ mkLambda `x .default (mkSort levelZero) $
--                        mkLambda `y .default (mkSort levelZero) $ 
--                          mkAppN (mkConst ``Not) #[mkAppN (mkConst ``Iff) #[.bvar 1, .bvar 0]]
-- | ⟨.op "=>", []⟩  => pure $ mkLambda `x .default (mkSort levelZero) $
--                        mkLambda `y .default (mkSort levelZero) $ 
--                          Lean.mkForall `i BinderInfo.default (.bvar 1) (.bvar 1)
-- | ⟨.op "<=", []⟩  => pure $ mkLambda `x .default (mkSort levelZero) $
--                        mkLambda `y .default (mkSort levelZero) $ 
--                          Lean.mkForall `i BinderInfo.default (.bvar 0) (.bvar 2)
-- | ⟨.op ">", [⟨.op "*", [a, b]⟩, c]⟩   => toLeanExpr ⟨.op ">", [a, ⟨.op ">", [b, c]⟩]⟩
-- | ⟨.op ">", [a, b]⟩ => mkArrow (← a.toLeanExpr) (← b.toLeanExpr)
-- | _ => .error "term2LamTerm :: Could not translate to Lean Expr: {repr t}"
-- where
--   withVar {α : Type _} (var : TPTP.Term) (k : Expr → MetaM α) : MetaM α := do
--     match var with
--     | ⟨.ident v, ty⟩ =>
--       let ty ← match ty with
--       | [ty] => toLeanExpr ty
--       | [] => pure $ mkConst `Iota
--       | _ => throwError "invalid bound var: {repr var}"
--       withLocalDeclD v ty k
--     | _ => throwError "invalid bound var: {repr var}"

open Meta

partial def findFile (name : String) (dir : System.FilePath) : IO (Option System.FilePath) := do
  -- search in [dir], and its parents recursively
  if (name : System.FilePath).isRelative
  then match ← search dir with
    | .none =>
      match ← IO.getEnv "TPTP" with
      | .none => return .none
      | .some dir' => search dir'
    | .some res => return res
  else if ← System.FilePath.pathExists name
  then return .some name
  else return .none
where search (dir : System.FilePath) : IO (Option System.FilePath) := do
    let curName := dir / name
    if ← System.FilePath.pathExists curName
    then return .some curName
    else
      let some dir' := dir.parent
        | return .none
      return ← search dir'

partial def resolveIncludes (cmds : List Command) (dir : System.FilePath) : IO (List Command) := do
  let mut res : Array Command := #[]
  for cmd in cmds do
    match cmd with
    | ⟨"include", [⟨.ident name, []⟩]⟩ =>
      let some path ← findFile (name : String) (dir : System.FilePath)
        | throw $ IO.userError s!"Cannot find: {name}"
      IO.println s!"Reading included file: {path}"
      let s ← IO.FS.readFile path
      let cmds' ← parse s
      let cmds' ← resolveIncludes cmds' dir
      for cmd' in cmds' do
        res := res.push cmd'
    | _ => res := res.push cmd   
  return res.toList

abbrev Formulas := Array (Expr × Expr × Array Name)

-- def compileCmds (cmds : List TPTP.Command) (acc : Formulas) (k : Formulas → MetaM α): MetaM α := do
--   match cmds with
--   | ⟨cmd, args⟩ :: cs =>
--     match cmd with
--     | "thf" | "tff" | "cnf" | "fof" => 
--       match args with
--       | [_, ⟨.ident "type", _⟩, ⟨.ident id, [ty]⟩]  =>
--         withLocalDeclD id (← toLeanExpr ty) fun _ => do
--           compileCmds cs acc k
--       | [⟨.ident name, []⟩, ⟨.ident kind, _⟩, val] =>
--         let val ← toLeanExpr val
--         let val := if kind == "conjecture" then ← mkAppM ``Not #[val] else val
--         withLocalDeclD ("H_" ++ name) val fun x => do
--           let acc := acc.push (val, x, #[])
--           compileCmds cs acc k
--       | _ => throwError "Unknown declaration kind: {args.map repr}"
--     | "include" => throwError "includes should have been unfolded first: {args.map repr}"
--     | cmd => throwError "Unknown command: {cmd}"
--   | [] => k acc

/-- Collect all constants (lower case variables) since these are not explicitly declared in FOF and CNF format. -/
partial def collectConstantsOfCmd (topLevel : Bool) (acc : HashMap String Expr) (t : Term): MetaM (HashMap String Expr) := do
  match t with
  | ⟨.ident n, as⟩ => do
    let acc ← as.foldlM (collectConstantsOfCmd false) acc
    if n.data[0]!.isLower && n.data[0]! != '$' && !acc.contains n
    then 
      let ty ← as.foldlM 
        (fun acc _ => mkArrow (mkConst `Iota) acc)
        (if topLevel then mkSort levelZero else mkConst `Iota)
      let acc := acc.insert n ty
      return acc
    else 
      return acc
  | ⟨.op "!", body :: _⟩ | ⟨.op "?", body :: _⟩ =>
    collectConstantsOfCmd topLevel acc body
  | ⟨.op "~", as⟩
  | ⟨.op "|", as⟩
  | ⟨.op "&", as⟩
  | ⟨.op "<=>", as⟩ 
  | ⟨.op "=>", as⟩ | ⟨.op "<=", as⟩ 
  | ⟨.op "~|", as⟩ 
  | ⟨.op "~&", as⟩  
  | ⟨.op "<~>", as⟩ => 
    as.foldlM (collectConstantsOfCmd topLevel) acc
  | ⟨.op "!=", as⟩ 
  | ⟨.op "=", as⟩ =>
    as.foldlM (collectConstantsOfCmd false) acc
  | _ => throwError "Failed to collect constants: {repr t}"

def collectCnfFofConstants (cmds : List Command) : MetaM (HashMap String Expr) := do
  let mut acc := HashMap.empty
  for cmd in cmds do
    match cmd with
    | ⟨"cnf", [_, _, val]⟩ | ⟨"fof", [_, _, val]⟩ =>
      acc ← collectConstantsOfCmd true acc val
    | _ => pure ()
  return acc

-- def compile [Inhabited α] (code : String) (dir : System.FilePath) (k : Formulas → MetaM α) : MetaM α := do
--   let cmds ← TPTP.parse code
--   let cmds ← resolveIncludes cmds dir
--   let constants ← collectCnfFofConstants cmds
--   withLocalDeclsD (constants.toArray.map fun (n, ty) => (n, fun _ => pure ty)) fun _ => do
--     compileCmds cmds #[] k

-- def compileFile [Inhabited α] (path : String) (k : Formulas → MetaM α) : MetaM α := do
--   let code ← IO.FS.readFile path
--   compile code (path : System.FilePath).parent.get! k

/-- Returns the unsat core (= all used facts) of a TSTP output string. -/
def unsatCore (str : String) : IO (Array String) := do
  let parseTree ← TPTP.parse str
  let mut res := #[]
  for ⟨_, args⟩ in parseTree do
    if args.length > 1 then
      if let ⟨.ident kind, []⟩ := args[1]! then
        if ["axiom", "conjecture", "negated_conjecture"].contains kind then
          if let ⟨.ident id, []⟩ := args[0]! then
            res := res.push id
  return res

-- def toLeanExpr (s : String) : MetaM Expr := do
--   let tokens ← Tokenizer.tokenize s
--   let (t, _) ← parseTerm.run {tokens}
--   let r ← toLeanExpr t
--   trace[Meta.debug] "{r}"
--   return r
-- 
-- set_option trace.Meta.debug true
-- #eval toLeanExpr "?[a : $tType, b : $tType]: a = b"
-- #eval toLeanExpr "![x : $tType]: ![a : x]: a != a"
-- #eval toLeanExpr "$true != $true"
-- #eval toLeanExpr "$true & $true"
-- #eval toLeanExpr "(<=)"

end TPTP