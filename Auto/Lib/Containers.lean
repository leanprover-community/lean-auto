import Lean
open Lean

namespace Auto

def mergeHashSet {α : Type u} [BEq α] [Hashable α] (a1 a2 : HashSet α) :=
  if a1.size < a2.size then
    a2.insertMany a1.toArray
  else
    a1.insertMany a2.toArray

def mergeArray (a1 a2 : Array α) :=
  if a1.size < a2.size then
    a2 ++ a1
  else
    a1 ++ a2

end Auto