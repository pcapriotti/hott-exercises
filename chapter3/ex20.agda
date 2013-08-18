{-# OPTIONS --without-K #-}
module chapter3.ex20 where

open import sum
open import hott
open import function
open import sets.unit

isom : ∀ {i j}{A : Set i}{P : A → Set j}
     → (hA : contr A)
     → Σ A P
     ≅ P (proj₁ hA)
isom {A = A}{P} hA = begin
    (Σ A P)
  ≅⟨ (Σ-ap-iso' (contr-⊤-iso hA) λ _ → refl≅) ⟩
    (Σ ⊤ λ { tt → P a })
  ≅⟨ ×-left-unit ⟩
    P a
  ∎
  where
    open ≅-Reasoning
    a = proj₁ hA
