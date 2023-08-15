import Lean
import Auto.Embedding.LamBase
import Auto.Translation.LamReif
open Lean

-- Lam2DTT : Simply-typed lambda calculus to Lean
-- The reason we need this file is that, sometimes we want external
--   provers (e.g. duper) to help us complete proofs. Note that
--   external provers does not work with things like `GLift.up Prop`.
--   Therefore, we must have a function to translate expressions
--   into `un-lifted` (original) `Lean expressions`.
-- Also, an important part of translating to un-lifted Lean
--   expressions is to deal with `=, ∀` and `∃`. Since we might
--   transform `<eq/forall/exist>` into the form without valuation
--   when we process λ terms, we also need to transform the
--   λ term into one that has the appropriate `<eq/forall/exist>Val`,
--   which means that we need to construct the corresponding
--   `<eq/forall/exist>Val`

namespace Auto

open Embedding.Lam



end Auto