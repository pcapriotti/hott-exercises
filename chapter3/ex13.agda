{-# OPTIONS --without-K #-}
module chapter3.ex13 where

open import sum
open import decidable
open import hott.hlevel.core
open import hott.truncation
open import sets.empty

module _ {i}(lem' : (A : Set i) → Dec A) where
  -- in the following, we are not allowed to make use of univalence

  η-inv : {X : Set i} → ∥ X ∥ → X
  η-inv {X} with lem' X
  ... | yes x = λ _ → x
  ... | no u = elim' (prop⇒h1 h1-X) (λ x → x)
    where
      h1-X : prop X
      h1-X x = ⊥-elim (u x)

  ac : {X : Set i}{A : X → Set i}
     → (P : (x : X) → A x → Set i)
     → ((x : X) → ∥ Σ (A x) (P x) ∥)
     → Σ ((x : X) → A x) λ f → (x : X) → P x (f x)
  ac {X}{A} P f = (λ x → proj₁ (f' x)) , (λ x → proj₂ (f' x))
    where
      f' : (x : X) → Σ (A x) (P x)
      f' x = η-inv (f x)
