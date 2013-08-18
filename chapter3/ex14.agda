{-# OPTIONS --without-K #-}
module chapter3.ex14 where

open import decidable
open import equality
open import function
open import hott
open import sets.empty

open import chapter3.ex9

module _ {i}(lem : LEM i) where
  dneg-η : {A : Set i} → A → ¬ ¬ A
  dneg-η x u = u x

  dneg-h1 : {A : Set i} → h 1 (¬ ¬ A)
  dneg-h1 = Π-hlevel λ _ → ⊥-prop

  dneg-univ : {A P : Set i}
            → h 1 P
            → (A → P)
            → (¬ ¬ A → P)
  dneg-univ {A}{P} hP f z with lem hP
  ... | yes p = p
  ... | no u = ⊥-elim (z (λ x → u (f x)))
