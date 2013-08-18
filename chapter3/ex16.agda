{-# OPTIONS --without-K #-}
module chapter3.ex16 where

open import sum
open import decidable
open import function
open import hott
open import sets.empty

open import chapter3.ex9

module _ {i}(lem : LEM i) where
  dneg-elim : {X : Set i} → h 1 X
            → ¬ ¬ X → X
  dneg-elim hX z with lem hX
  ... | yes x = x
  ... | no u = ⊥-elim (z u)

  Π-dneg : ∀ {X : Set i}{Y : X → Set i}
         → h 2 X → ((x : X) → h 1 (Y x))
         → ((x : X) → ¬ ¬ Y x)
         ≅ (¬ ¬ ((x : X) → Y x))
  Π-dneg {X}{Y} hX hY = record
    { to = λ f u → u λ x → dneg-elim (hY x) (f x)
    ; from = λ u x v → u (λ f → v (f x))
    ; iso₁ = λ f
           → h1⇒prop ( Π-hlevel λ x
                     → Π-hlevel λ _
                     → ⊥-prop) _ _
    ; iso₂ = λ u → h1⇒prop (Π-hlevel λ _ → ⊥-prop) _ _ }
