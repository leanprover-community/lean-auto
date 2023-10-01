import Auto.Embedding.LamBase
open Lean

namespace Auto.Embedding.Lam

-- Given two sorts s₁ s₂, run a quick test on whether the
--   inhabitation of s₁ subsumes the inhabitation of s₂
def Inhabitation.subsumeQuick (s₁ s₂ : LamSort) : Bool :=
  let s₁args := s₁.getArgTys
  let s₁res := s₁.getResTy
  let s₂args := HashSet.empty.insertMany s₂.getArgTys
  let s₂res := s₂.getResTy
  s₂args.contains s₂res || (s₁res == s₂res && (
    s₁args.all (fun arg => s₂args.contains arg)
  ))

-- Run a quick test on whether the inhabitation of `s` is trivial
def Inhabitation.trivialQuick := go HashSet.empty
where go (argTys : HashSet LamSort) (s : LamSort) : Bool :=
  match s with
  | .func argTy resTy =>
    argTys.contains s || go (argTys.insert argTy) resTy
  | _ => argTys.contains s

end Auto.Embedding.Lam