{-# OPTIONS --without-K #-}
module chapter1.ex3 where

open import level
open import equality

-- this would be trivial in agda due to definitional η for records
-- so I'll define a product type without η:
data _×_ {i j}(A : Set i)(B : Set j) : Set (i ⊔ j) where
  _,_ : A → B → A × B

module ×-def {i j}{A : Set i}{B : Set j} where
  proj₁ : A × B → A
  proj₁ (a , b) = a

  proj₂ : A × B → B
  proj₂ (a , b) = b

  uppt : (u : A × B) → (proj₁ u , proj₂ u) ≡ u
  uppt (a , b) = refl

module ×-Ind {i j}{A : Set i}{B : Set j} where
  open ×-def

  ×-ind : ∀ {k}(P : A × B → Set k)
        → ((x : A)(y : B) → P (x , y))
        → (p : A × B) → P p
  ×-ind P d p = subst P (uppt p) (d (proj₁ p) (proj₂ p))

  ×-ind-β : ∀ {k} (P : A × B → Set k)
          → (d : (x : A)(y : B) → P (x , y))
          → (x : A)(y : B)
          → ×-ind P d (x , y) ≡ d x y
  ×-ind-β P d x y = refl

data Σ {i j}(A : Set i)(B : A → Set j) : Set (i ⊔ j) where
  _,_ : (x : A) → B x → Σ A B

module Σ-def {i j}{A : Set i}{B : A → Set j} where
  proj₁ : Σ A B → A
  proj₁ (a , b) = a

  proj₂ : (u : Σ A B) → B (proj₁ u)
  proj₂ (a , b) = b

  uppt : (u : Σ A B) → (proj₁ u , proj₂ u) ≡ u
  uppt (a , b) = refl

module Σ-ind {i j}{A : Set i}{B : A → Set j} where
  open Σ-def

  Σ-ind : ∀ {k}(P : Σ A B → Set k)
        → ((x : A)(y : B x) → P (x , y))
        → (u : Σ A B) → P u
  Σ-ind P d u = subst P (uppt u) (d (proj₁ u) (proj₂ u))

  Σ-ind-β : ∀ {k}(P : Σ A B → Set k)
          → (d : (x : A)(y : B x) → P (x , y))
          → (x : A)(y : B x)
          → Σ-ind P d (x , y) ≡ d x y
  Σ-ind-β P d x y = refl
