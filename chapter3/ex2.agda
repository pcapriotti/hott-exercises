{-# OPTIONS --without-K #-}
module chapter3.ex2 where

open import sum
open import hott
open import sets.nat

⊎-set : ∀ {i j}{A : Set i}{B : Set j}
      → h 2 A → h 2 B → h 2 (A ⊎ B)
⊎-set = ⊎-hlevel refl-≤
