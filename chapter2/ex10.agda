{-# OPTIONS --without-K #-}
module chapter2.ex10 where

open import sum
open import equality
open import function.isomorphism.core

-- copied from function.isomorphism.utils
Σ-assoc-iso : ∀ {i j k}
              {X : Set i}{Y : X → Set j}
              {Z : (x : X) → Y x → Set k}
            → Σ (Σ X Y) (uncurry Z)
            ≅ Σ X λ x → Σ (Y x) (Z x)
Σ-assoc-iso = record
  { to = λ {((x , y) , z) → (x , y , z) }
  ; from = λ {(x , y , z) → ((x , y) , z) }
  ; iso₁ = λ _ → refl
  ; iso₂ = λ _ → refl }
