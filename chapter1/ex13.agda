{-# OPTIONS --without-K #-}
module chapter1.ex13 where

open import level
open import sum
open import sets.empty

dneg-lem : ∀ {i}{A : Set i} → ¬ ¬ (A ⊎ ¬ A)
dneg-lem f = f (inj₂ (λ a → f (inj₁ a)))
