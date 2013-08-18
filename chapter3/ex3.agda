{-# OPTIONS --without-K #-}
module chapter3.ex3 where

open import sum
open import hott

Σ-set : ∀ {i j}{A : Set i}{B : A → Set j}
      → h 2 A
      → ((x : A) → h 2 (B x))
      → h 2 (Σ A B)
Σ-set = Σ-hlevel
