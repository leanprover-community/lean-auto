import Auto.Lib.BinNat

inductive BinTree (α : Sort _) where
  | leaf : BinTree α
  | node : BinTree α → α → BinTree α → BinTree α

structure BinList (α : Sort _) where
  zero : α
  pos  : BinTree α

def BinTree.val (bt : BinTree α) (default : α) :=
  match bt with
  | .leaf => default
  | .node _ x _ => x

def BinTree.left (bt : BinTree α) :=
  match bt with
  | .leaf => BinTree.leaf
  | .node l _ _ => l

def BinTree.right (bt : BinTree α) :=
  match bt with
  | .leaf => BinTree.leaf
  | .node _ _ r => r

def BinTree.get (bt : BinTree α) (default : α) (bs : Pos) :=
  match bs with
  | .xH => bt.val default
  | .xO bs' => BinTree.get bt.left default bs'
  | .xI bs' => BinTree.get bt.right default bs'
    
structure QList (α : Sort _) where
  data : BinTree α
  size : Nat
  default : α