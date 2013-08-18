{-# OPTIONS --without-K #-}
module chapter3.ex10 where

open import level using (lsuc; ↑)
open import decidable
open import sum
open import equality
open import function
open import hott
open import sets.unit
open import sets.empty

open import chapter3.ex9

module _ {i}(lem : LEM (lsuc i)) where
  top-h1 : h 1 (↑ i ⊤)
  top-h1 = iso-hlevel (lift-iso i ⊤) (h↑ ⊤-contr)

  bot-h1 : h 1 (↑ i ⊥)
  bot-h1 = iso-hlevel (lift-iso i ⊥) ⊥-prop

  lift : {A : Set i} → h 1 A → Set (lsuc i)
  lift {A} hA = ↑ (lsuc i) A

  lift-h1 : ∀ {A : Set i}(hA : h 1 A)
          → h 1 (lift hA)
  lift-h1 {A} hA = iso-hlevel (lift-iso _ A) hA

  lower : {A : Set (lsuc i)} → h 1 A → Set i
  lower {A} hA with lem hA
  ... | yes a = ↑ i ⊤
  ... | no u = ↑ i ⊥

  lower-h1 : {A : Set (lsuc i)}(hA : h 1 A)
           → h 1 (lower hA)
  lower-h1 {A} hA with lem hA
  ... | yes a = top-h1
  ... | no u = bot-h1

  lower-iso : ∀ {A : Set (lsuc i)}(hA : h 1 A)
            → A ≅ lower hA
  lower-iso {A} hA with lem hA
  ... | yes a = trans≅ (contr-⊤-iso (a , h1⇒prop hA a))
                       (lift-iso i ⊤)
  ... | no u = trans≅ (empty-⊥-iso u)
                      (lift-iso i ⊥)

  lift-lower-iso : {A : Set i}(hA : h 1 A)
                 → lower (lift-h1 hA) ≅ A
  lift-lower-iso {A} hA = sym≅ (trans≅ (lift-iso _ _) (lower-iso _))

  lower-lift-iso : {A : Set (lsuc i)}(hA : h 1 A)
                 → lift (lower-h1 hA) ≅ A
  lower-lift-iso {A} hA = sym≅ (trans≅ (lower-iso _) (lift-iso _ _))

  univ-incl-iso : HProp i ≅ HProp (lsuc i)
  univ-incl-iso = record
    { to = λ { (A , hA) → lift hA , lift-h1 hA }
    ; from = λ { (A , hA) → lower hA , lower-h1 hA }
    ; iso₁ = λ { (A , hA) → prop-eq _ hA (lift-lower-iso hA) }
    ; iso₂ = λ { (A , hA) → prop-eq _ hA (lower-lift-iso hA) } }
