import Auto.Embedding.LamConv

namespace Auto.Embedding.Lam

structure IndInfo where
  type  : LamSort
  ctors : List (LamSort × LamTerm)
  projs : Option (List (LamSort × LamTerm))

def IndInfo.toString (i : IndInfo) :=
  s!"IndInfo ⦗⦗ {i.type} || " ++
    String.intercalate ", " (i.ctors.map (fun (s, t) => s!"{t} : {s}")) ++
    (match i.projs with
     | .some arr => " || " ++ String.intercalate ", " (arr.map (fun (s, t) => s!"{t} : {s}"))
     | .none => "") ++ " ⦘⦘"

instance : ToString IndInfo where
  toString := IndInfo.toString

def IndInfo.mpAll?Aux (rw : LamTerm) : List (LamSort × LamTerm) → Option (List (LamSort × LamTerm))
| [] => .some []
| .cons (s, t) tail =>
  match LamTerm.mpAll? rw t, mpAll?Aux rw tail with
  | .some t', .some tail' => .some (.cons (s, t') tail')
  | _,        _           => .none

def IndInfo.mpAll? (rw : LamTerm) (ii : IndInfo) : Option IndInfo :=
  match mpAll?Aux rw ii.ctors with
  | .some ii' => .some ⟨ii.type, ii', ii.projs.bind (mpAll?Aux rw)⟩
  | .none     => .none

abbrev MutualIndInfo := List IndInfo

def MutualIndInfo.mpAll? (rw : LamTerm) : MutualIndInfo → Option MutualIndInfo
| [] => .some []
| .cons ii tail =>
  match ii.mpAll? rw, mpAll? rw tail with
  | .some ii', .some tail' => .some (.cons ii' tail')
  | _,         _           => .none

end Auto.Embedding.Lam
