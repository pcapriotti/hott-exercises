{-# OPTIONS --without-K #-}

module chapter1.ex7 where

open import sum
open import equality
open import hott.hlevel.core

ind' : ∀ {i j}{X : Set i}{x : X}
     → (P : (y : X) → x ≡ y → Set j)
     → P x refl
     → (y : X)
     → (p : x ≡ y)
     → P y p
ind' {X = X}{x = x} P d y p =
  subst (λ {(y , p) → P y p })
        (proj₂ (singl-contr x) (y , p)) d
