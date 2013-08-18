{-# OPTIONS --without-K #-}
module chapter3.ex6 where

open import sum
open import decidable
open import equality
open import function
open import hott
open import sets.empty

open import chapter3.ex7

prop-lem : ∀ {i}{A : Set i}
         → prop A
         → prop (A ⊎ ¬ A)
prop-lem {i}{A} pA = prop-excl pA p¬A (λ {(a , u) → u a })
  where
    p¬A : prop (¬ A)
    p¬A = h1⇒prop (Π-hlevel λ _ → ⊥-prop)

dec-h1 : ∀ {i}{A : Set i}
       → h 1 A
       → h 1 (Dec A)
dec-h1 {A = A} hA = iso-hlevel isom (prop⇒h1 (prop-lem (h1⇒prop hA)))
  where
    isom : (A ⊎ ¬ A) ≅ Dec A
    isom = record
      { to = λ { (inj₁ a) → yes a ; (inj₂ u) → no u }
      ; from = λ { (yes a) → inj₁ a ; (no u) → inj₂ u }
      ; iso₁ = λ { (inj₁ a) → refl ; (inj₂ u) → refl }
      ; iso₂ = λ { (yes a) → refl ; (no u) → refl } }
