{-# OPTIONS --without-K #-}

module chapter1.ex4 where

open import sum
open import equality
open import sets.nat

iter : ∀ {i}{C : Set i}
     → C → (C → C)
     → ℕ → C
iter z s 0 = z
iter z s (suc n) = s (iter z s n)

rec : ∀ {i}{C : Set i}
    → C → (ℕ → C → C)
    → ℕ → C
rec {i}{C} z f n = proj₂ (iter z' s' n)
  where
    z' : ℕ × C
    z' = (0 , z)

    s' : ℕ × C → ℕ × C
    s' (n , c) = (suc n , f n c)
