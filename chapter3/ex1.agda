{-# OPTIONS --without-K #-}
module chapter3.ex1 where

open import function
open import hott

iso-set : ∀ {i j}{A : Set i}{B : Set j}
        → A ≅ B → h 2 A → h 2 B
iso-set = iso-hlevel
