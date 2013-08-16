{-# OPTIONS --without-K #-}

module chapter1.ex6 where

open import equality
open import function.extensionality
open import sets.bool

_×_ : ∀ {i} → Set i → Set i → Set i
A × B = (b : Bool) → if b then A else B

module ×-def {i}{A B : Set i} where
  _,_ : A → B → A × B
  _,_ x y true = x
  _,_ x y false = y

  proj₁ : A × B → A
  proj₁ u = u true

  proj₂ : A × B → B
  proj₂ u = u false

  abstract
    uppt : (u : A × B) → (proj₁ u , proj₂ u) ≡ u
    uppt u = funext λ { true → refl ; false → refl }

module ×-Ind {i}{A B : Set i} where
  open ×-def

  -- first define a version of uppt for which the computation
  -- rule is easier to prove
  uppt' : (u : A × B) → (proj₁ u , proj₂ u) ≡ u
  uppt' u = sym (uppt (proj₁ u , proj₂ u)) · uppt u

  uppt-compute : (x : A)(y : B) → uppt' (x , y) ≡ refl
  uppt-compute x y = right-inverse (uppt (x , y))

  -- given the computation rule for funext, uppt itself has a computation rule,
  -- but we don't need it for this exercise

  ind : ∀ {j}(P : A × B → Set j)
      → (d : (x : A)(y : B) → P (x , y))
      → (u : A × B) → P u
  ind P d u = subst P (uppt' u) (d (proj₁ u) (proj₂ u))

  ind-β : ∀ {j}(P : A × B → Set j)
        → (d : (x : A)(y : B) → P (x , y))
        → (x : A)(y : B)
        → ind P d (x , y) ≡ d x y
  ind-β P d x y = ap (λ z → subst P z (d x y)) (uppt-compute x y)
