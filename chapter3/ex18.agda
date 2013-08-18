{-# OPTIONS --without-K #-}
module chapter3.ex18 where

open import decidable
open import hott
open import sets.empty

open import chapter3.ex6
open import chapter3.ex9

lem⇒dneg-elim : ∀ {i} → LEM i
               → {A : Set i}
               → h 1 A
               → ¬ ¬ A → A
lem⇒dneg-elim lem hA z with lem hA
... | yes a = a
... | no u = ⊥-elim (z u)

dneg-elim⇒lem : ∀ {i}
               → ({A : Set i} → h 1 A →  ¬ ¬ A → A)
               → LEM i
dneg-elim⇒lem dneg-elim {A} hA = dneg-elim (dec-h1 hA) dneg-lem
  where
    dneg-lem : ¬ ¬ Dec A
    dneg-lem u = u (no λ x → u (yes x))
