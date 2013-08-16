{-# OPTIONS --without-K #-}

module chapter2.ex2 {i}{A : Set i} where

open import equality.core
open import chapter2.ex1

triangle : {x y z : A}(p : x ≡ y)(q : y ≡ z)
         → trans₁ (eq₁₂ p q) (eq₂₃ p q) ≡ eq₁₃ p q
triangle refl refl = refl
