namespace Auto

inductive LazyList (α : Type u)
| nil                             : LazyList α
| cons (hd : α) (tl : LazyList α) : LazyList α
| delayed (t : Thunk (LazyList α)): LazyList α

-- @[extern cpp inline "#2"]
def List.toLazy {α : Type u} : List α → LazyList α
| []     => LazyList.nil
| (h::t) => LazyList.cons h (List.toLazy t)

namespace LazyList
variable {α : Type u} {β : Type v} {δ : Type w}

instance : Inhabited (LazyList α) :=
⟨nil⟩

partial def nats i := cons i (delayed (nats (i + 1)))

def size : LazyList α → Nat
| nil        => 0
| cons hd tl => size tl + 1
| delayed t  => size t.get + 1

@[inline] protected def pure : α → LazyList α
| a => cons a nil

def isEmpty : LazyList α → Bool
| nil          => true
| (cons _ _)   => false
| (delayed as) => isEmpty as.get

def toList : LazyList α → List α
| nil          => []
| (cons a as)  => a :: toList as
| (delayed as) => toList as.get

def head [Inhabited α] : LazyList α → α
| nil          => default
| (cons a _)  => a
| (delayed as) => head as.get

def tail : LazyList α → LazyList α
| nil          => nil
| (cons _ as)  => as
| (delayed as) => tail as.get

def append : LazyList α → LazyList α → LazyList α
| nil          , bs => bs
| (cons a as)  , bs => cons a (delayed (append as bs))
| (delayed as) , bs => append as.get bs

instance : Append (LazyList α) :=
⟨LazyList.append⟩

@[specialize] def map (f : α → β) : LazyList α → LazyList β
| nil          => nil
| (cons a as)  => cons (f a) (map f as)
| (delayed as) => delayed (map f as.get)

@[specialize] def map₂ (f : α → β → δ) : LazyList α → LazyList β → LazyList δ
| nil          , _            => nil
| _            , nil          => nil
| (cons a as)  , (cons b bs)  =>
  have : size as + size bs < size (cons a as) + size (cons b bs) := by simp_arith [size]
  cons (f a b) (delayed (map₂ f as bs))
| (delayed as) , bs           =>
  have : size (Thunk.get as) + size bs < size (delayed as) + size bs := by simp_arith [size]
  map₂ f as.get bs
| as           , (delayed bs) =>
  have : size as + size (Thunk.get bs) < size as + size (delayed bs) := by simp_arith [size]
  map₂ f as bs.get
termination_by map₂ f as bs => size as + size bs

-- interleave between 2 lists
def interleave : LazyList α → LazyList α → LazyList α
| nil          , bs  => bs
| (cons a as)  , bs  =>
  have : size bs + size as < size (cons a as) + size bs := by simp_arith [size]
  cons a (delayed (interleave bs as))
| (delayed as) , bs  =>
  have : size (Thunk.get as) + size bs < size (delayed as) + size bs := by simp_arith [size]
  delayed (interleave as.get bs)
termination_by interleave as bs => size as + size bs

-- interleave between N lists
partial def interleaveN : Array (LazyList α) → LazyList α := fun x => iNrec (Std.Queue.empty.enqueueAll x.toList)
  where iNrec (q : Std.Queue (LazyList α)) :=
    if let some (a, q') := q.dequeue? then
      match a with
      | nil => iNrec q'
      | cons a as => cons a (iNrec (q'.enqueue as))
      | delayed t => delayed (iNrec (q'.enqueue t.get))
    else
      nil

-- Another type of "join" operator
partial def interleaveω : LazyList (LazyList α) → LazyList α := fun x => iωrec 0 0 Std.Queue.empty x
  where iωrec (i j : Nat) (q : Std.Queue (LazyList α)) x :=
    if j = i then
      match x with
      | nil => if q.isEmpty then nil else iωrec (i + 1) 0 q nil
      | cons a as => iωrec (i + 1) 0 (q.enqueue a) as
      | delayed t => delayed (iωrec (i + 1) 0 q t.get)
    else
      if let some (a, q') := q.dequeue? then
        match a with
        | nil => iωrec i j q' x
        | cons a as => cons a (iωrec i (j + 1) (q'.enqueue as) x)
        | delayed t => delayed (iωrec i (j + 1) (q'.enqueue t.get) x)
      else
        iωrec 0 0 q x

-- Another type of "bind" operator
def bindω (xs : LazyList α) (f : α → LazyList β) : LazyList β := interleaveω (xs.map f)

@[inline] def zip : LazyList α → LazyList β → LazyList (α × β) := map₂ Prod.mk

def join : LazyList (LazyList α) → LazyList α
| nil          => nil
| (cons a as)  => append a (delayed (join as))
| (delayed as) => join as.get

@[inline] protected def bind (x : LazyList α) (f : α → LazyList β) : LazyList β :=
  join (x.map f)

instance isMonad : Monad LazyList :=
{ pure := @LazyList.pure, bind := @LazyList.bind, map := @LazyList.map }

instance : Alternative LazyList :=
{ failure := nil,
  orElse  := fun a b => LazyList.append a (b PUnit.unit) }

def approx : Nat → LazyList α → List α
| 0    , _            => []
| _    , nil          => []
| (i+1), (cons a as)  => a :: approx i as
| (i+1), (delayed as) => approx (i+1) as.get

@[specialize] partial def iterate (f : α → α) : α → LazyList α
| x => cons x (delayed (iterate f (f x)))

@[specialize] partial def iterate₂ (f : α → α → α) : α → α → LazyList α
| x, y => cons x (delayed (iterate₂ f y (f x y)))

@[specialize] def filter (p : α → Bool) : LazyList α → LazyList α
| nil          => nil
| (cons a as)  => if p a then cons a (filter p as) else filter p as
| (delayed as) => delayed (filter p as.get)

partial def cycle : LazyList α → LazyList α
| xs => xs ++ delayed (cycle xs)

partial def repeats : α → LazyList α
| a => cons a (delayed (repeats a))

def inits : LazyList α → LazyList (LazyList α)
| nil          => cons nil nil
| (cons a as)  => cons nil (delayed (map (λ as => cons a as) (inits as)))
| (delayed as) => inits as.get

def addOpenBracket (s : String) : String :=
  if s.isEmpty then "[" else s

def approxToStringAux [ToString α] : Nat → LazyList α → String → String
| _    , nil         , r => (if r.isEmpty then "[" else r) ++ "]"
| 0    , _           , r => (if r.isEmpty then "[" else r) ++ ", ..]"
| (n+1), (cons a as) , r => approxToStringAux n as ((if r.isEmpty then "[" else r ++ ", ") ++ toString a)
| n    , (delayed as), r => approxToStringAux n as.get r

def approxToString [ToString α] (as : LazyList α) (n : Nat := 10) : String :=
  as.approxToStringAux n ""

instance [ToString α] : ToString (LazyList α) := ⟨approxToString⟩

end LazyList



-- Other utilities

def List.lazySubsequences {α : Type u} : List α → LazyList (List α)
| .nil => .cons .nil .nil
| .cons a as => List.lazySubsequences as ++ .delayed (LazyList.map (List.cons a) (lazySubsequences as))



-- Testing

section Test

  private def fib : LazyList Nat :=
    LazyList.iterate₂ (·+·) 0 1
  
  private def tst : LazyList String := do
    let x ← List.toLazy [1, 2, 3]
    let y ← List.toLazy [2, 3, 4]
    -- dbgTrace (toString x ++ " " ++ toString y) $ λ _,
    guard (x + y > 5)
    pure (toString x ++ " + " ++ toString y ++ " = " ++ toString (x+y))
  
  open LazyList
  
  private def iota (i : UInt32 := 0) : LazyList UInt32 :=
    iterate (·+1) i
  
  set_option pp.explicit true
  
  private partial def sieve : LazyList UInt32 → LazyList UInt32
  | nil          => nil
  | (cons a as)  => cons a (delayed (sieve (filter (λ b => b % a != 0) as)))
  | (delayed as) => sieve as.get
  
  private partial def primes : LazyList UInt32 :=
    sieve (iota 2)
  
  private def maintest : IO Unit := do
    let _ := 10
    -- IO.println $ tst.isEmpty,
    -- IO.println $ [1, 2, 3].toLazy.cycle,
    -- IO.println $ [1, 2, 3].toLazy.cycle.inits,
    -- IO.println $ ((iota.filter (λ v, v % 5 == 0)).approx 50000).foldl (+) 0,
    IO.println $ (primes.approx 2000).foldl (·+·) 0
    -- IO.println $ tst.head,
    -- IO.println $ fib.interleave (iota.map (+100)),
    -- IO.println $ ((iota.map (+10)).filter (λ v, v % 2 == 0)),
    pure ()
  
  private partial def natuple := LazyList.bindω (LazyList.nats 0) (fun i => (LazyList.nats 0).zip (repeats i))
  
end Test

end Auto