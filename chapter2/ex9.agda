{-# OPTIONS --without-K #-}
module chapter2.ex9 where

open import sum
open import equality
open import function.extensionality
open import function.isomorphism

⊎-univ : ∀ {i j k}{A : Set i}{B : Set j}{P : A ⊎ B → Set k}
       → ((x : A ⊎ B) → P x)
       ≅ (((x : A) → P (inj₁ x)) × ((y : B) → P (inj₂ y)))
⊎-univ {A = A}{B = B}{P = P} = record
  { to = f
  ; from = g
  ; iso₁ = λ u → funext (α u)
  ; iso₂ = λ {(u , v) → β u v} }
  where
    f : ((xy : A ⊎ B) → P xy)
      → (((x : A) → P (inj₁ x)) × ((y : B) → P (inj₂ y)))
    f u = (λ a → u (inj₁ a)) , (λ b → u (inj₂ b))

    g : (((x : A) → P (inj₁ x)) × ((y : B) → P (inj₂ y)))
      → ((x : A ⊎ B) → (P x))
    g (u , _) (inj₁ a) = u a
    g (_ , v) (inj₂ b) = v b

    α : (u : (x : A ⊎ B) → P x)
      → (x : A ⊎ B)
      → g (f u) x ≡ u x
    α u (inj₁ a) = refl
    α u (inj₂ b) = refl

    β : (u : (x : A) → P (inj₁ x))
        (v : (y : B) → P (inj₂ y))
      → f (g (u , v)) ≡ (u , v)
    β u v = refl

⊎-univ' : ∀ {i j k}{A : Set i}{B : Set j}{X : Set k}
        → (A ⊎ B → X)
        ≅ ((A → X) × (B → X))
⊎-univ' = ⊎-univ
