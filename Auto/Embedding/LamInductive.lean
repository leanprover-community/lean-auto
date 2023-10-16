import Auto.Embedding.LamConv

namespace Auto.Embedding.Lam

structure IndInfo where
  type  : LamSort
  ctors : List (LamSort × LamTerm)

def IndInfo.toString (i : IndInfo) :=
  s!"IndInfo ⦗⦗ {i.type} || " ++ String.intercalate ", "
    (i.ctors.map (fun (s, t) => s!"{t} : {s}")) ++ " ⦘⦘"

instance : ToString IndInfo where
  toString := IndInfo.toString

abbrev MutualIndInfo := List IndInfo

end Auto.Embedding.Lam