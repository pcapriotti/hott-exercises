{-# OPTIONS --without-K #-}

module chapter2.ex3 {i}{A : Set i} where

open import equality
open import chapter2.ex1

-- I'll take _·_ as the fourth proof of transitivity

eq : {x y z : A}(p : x ≡ y)(q : y ≡ z)
   → trans₁ p q ≡ p · q
eq refl refl = refl
