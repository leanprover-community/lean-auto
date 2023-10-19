import Auto.Embedding.LamConv
import Std.Data.Int.Lemmas
import Std.Data.Fin.Lemmas

namespace Auto.Embedding.Lam

section BVTheorems

  open Std.BitVec
  
  theorem ofNat_add (n a b : Nat) : (a + b)#n = a#n + b#n := by
    apply congrArg (f:=Std.BitVec.ofFin); apply Fin.eq_of_val_eq
    dsimp [Fin.ofNat']; rw [Nat.add_mod]; rfl
  
  theorem ofNat_mod_pow2 (n a : Nat) : (a % (2 ^ n))#n = a#n := by
    apply congrArg (f:=Std.BitVec.ofFin); apply Fin.eq_of_val_eq
    dsimp [Fin.ofNat']; apply Nat.mod_mod
  
  theorem ofNat_mul (n a b : Nat) : (a * b)#n = a#n * b#n := by
    apply congrArg (f:=Std.BitVec.ofFin); apply Fin.eq_of_val_eq
    dsimp [Fin.ofNat']; rw [Nat.mul_mod]; rfl

end BVTheorems

theorem LamEquiv.bvofNat :
  LamEquiv lval lctx (.base (.bv n)) (.mkBvofNat n (.mkNatVal i)) (.base (.bvVal' n i)) :=
  ⟨.mkBvofNat (.ofBase (.ofNatVal' i)), .ofBase (.ofBvVal' n i), fun _ => rfl⟩

theorem LamEquiv.bvofNat_nadd
  (wfa : LamWF lval.toLamTyVal ⟨lctx, a, .base .nat⟩)
  (wfb : LamWF lval.toLamTyVal ⟨lctx, b, .base .nat⟩) :
  LamEquiv lval lctx (.base (.bv n))
    (.mkBvofNat n (.mkNatBinOp .nadd a b))
    (.mkBvBinOp n (.bvadd n) (.mkBvofNat n a) (.mkBvofNat n b)) :=
  ⟨.mkBvofNat (.mkNatBinOp .ofNadd wfa wfb),
   .mkBvBinOp (.ofBvadd _) (.mkBvofNat wfa) (.mkBvofNat wfb), fun lctxTerm => by
      apply GLift.down.inj; apply ofNat_add⟩

end Auto.Embedding.Lam