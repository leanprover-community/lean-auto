-- This is a temporary file which emulates mathlib
--   in order to reduce initialization time

namespace Auto

section classes

  class Zero.{u} (α : Type u) where
    zero : α
  
  instance Zero.toOfNat0 {α} [Zero α] : OfNat α (nat_lit 0) where
    ofNat := ‹Zero α›.1
  
  instance Zero.ofOfNat0 {α} [OfNat α (nat_lit 0)] : Zero α where
    zero := 0

  class One (α : Type u) where
    one : α
  
  instance One.toOfNat1 {α} [One α] : OfNat α (nat_lit 1) where
    ofNat := ‹One α›.1

  instance One.ofOfNat1 {α} [OfNat α (nat_lit 1)] : One α where
    one := 1

end classes

section Real

  local instance : Inhabited ((α : Type) × α) where
    default := ⟨Nat, 0⟩
  
  opaque RealPre : (α : Type) × α
  
  def Real := RealPre.fst
  
  local instance : Inhabited Real where
    default := RealPre.snd
  
  @[irreducible] private def zero : Real :=
    Inhabited.default
  
  @[irreducible] private def one : Real :=
    Inhabited.default

  instance : Zero Real :=
    ⟨zero⟩
  
  instance : One Real :=
    ⟨one⟩

end Real

end Auto