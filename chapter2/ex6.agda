{-# OPTIONS --without-K #-}
module chapter2.ex6 where

open import sum
open import equality
open import function.isomorphism
open import hott.weak-equivalence
open import hott.univalence

etrans : ∀ {i}{A : Set i}{x y : A}
       → x ≡ y
       → (z : A)
       → y ≡ z
       → x ≡ z
etrans p _ q = p · q

trans-equiv : ∀ {i}{A : Set i}{x y : A}
            → (p : x ≡ y)
            → {z : A}
            → weak-equiv (etrans p z)
trans-equiv refl = coerce-equiv refl

trans-iso : ∀ {i}{A : Set i}{x y : A}
          → (p : x ≡ y)
          → {z : A}
          → (y ≡ z) ≅ (x ≡ z)
trans-iso p = ≈⇒≅ (etrans p _ , trans-equiv p)
