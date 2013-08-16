{-# OPTIONS --without-K #-}

module chapter1.ex5 where

open import equality
open import sum using (Σ; _,_; proj₁; proj₂)
open import sets.bool

ind₂ : ∀ {i} (P : Bool → Set i)
     → P true → P false
     → (b : Bool) → P b
ind₂ P d₁ d₂ true = d₁
ind₂ P d₁ d₂ false = d₂

recΣ : ∀ {i j k} {A : Set i}{B : A → Set j}
     → (P : Σ A B → Set k)
     → (d : (x : A)(y : B x) → P (x , y))
     → (u : Σ A B) → P u
recΣ P d (x , y) = d x y

_⊎_ : ∀ {i} → Set i → Set i → Set _
A ⊎ B = Σ Bool λ b → if b then A else B

module ⊎-def {i}{A B : Set i} where
  inl : A → A ⊎ B
  inl x = true , x

  inr : B → A ⊎ B
  inr y = false , y

module ⊎-Ind {i}{A B : Set i} where
  open ⊎-def

  ind : ∀ {j} (P : A ⊎ B → Set j)
      → ((x : A) → P (inl x))
      → ((y : B) → P (inr y))
      → (u : A ⊎ B) → P u
  ind P d₁ d₂ u
    = recΣ P (ind₂ (λ b → (z : if b then A else B) → P (b , z)) d₁ d₂) u

  ind-β₁ : ∀ {j}(P : A ⊎ B → Set j)
         → (d₁ : (x : A) → P (inl x))
         → (d₂ : (y : B) → P (inr y))
         → (x : A)
         → ind P d₁ d₂ (inl x) ≡ d₁ x
  ind-β₁ P d₁ d₂ x = refl

  ind-β₂ : ∀ {j}(P : A ⊎ B → Set j)
         → (d₁ : (x : A) → P (inl x))
         → (d₂ : (y : B) → P (inr y))
         → (y : B)
         → ind P d₁ d₂ (inr y) ≡ d₂ y
  ind-β₂ P d₁ d₂ y = refl
