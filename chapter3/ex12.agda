{-# OPTIONS --without-K #-}
module chapter3.ex12 where

open import decidable
open import sets.empty
open import hott

open import chapter3.ex9

module _ {i}(lem : LEM i) where
  weak-η-inv : (A : Set i) → ∥ (∥ A ∥ → A) ∥
  weak-η-inv A with lem {∥ A ∥} (prop⇒h1 trunc-prop)
  ... | yes p = elim' (prop⇒h1 trunc-prop) (λ x → η (λ _ → x)) p
  ... | no u = η λ x → ⊥-elim (u x)

  -- Informal proof:

  -- Given LEM, A is either merely inhabited or not.
  --
  -- Assume first that A is merely inhabited.  Since we need to prove a mere
  -- proposition, it is enough to assume some (x : A), hence the constant
  -- function to x shows that ∥ A ∥ → A is inhabited.
  --
  -- If A is not merely inhabited, then ∥ A ∥ implies everything, and in
  -- particular ∥ A ∥ → A is merely inhabited.
