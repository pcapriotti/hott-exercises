{-# OPTIONS --without-K #-}
module chapter1.ex12 where

open import level
open import sum
open import sets.empty

module Tautologies {i j}(A : Set i)(B : Set j) where
  taut₁ : A → B → A
  taut₁ a _ = a

  taut₂ : A → ¬ ¬ A
  taut₂ a f = f a

  taut₃ : (¬ A ⊎ ¬ B) → ¬ (A × B)
  taut₃ (inj₁ f) (a , b) = f a
  taut₃ (inj₂ f) (a , b) = f b
