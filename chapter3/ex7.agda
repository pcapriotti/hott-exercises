{-# OPTIONS --without-K #-}
module chapter3.ex7 where

open import sum
open import equality
open import hott
open import sets.empty

prop-excl : ∀ {i j}{A : Set i}{B : Set j}
          → prop A → prop B
          → ¬ (A × B)
          → prop (A ⊎ B)
prop-excl pA pB u (inj₁ x) (inj₁ x') = ap inj₁ (pA x x')
prop-excl pA pB u (inj₁ x) (inj₂ y) = ⊥-elim (u (x , y))
prop-excl pA pB u (inj₂ y) (inj₁ x) = ⊥-elim (u (x , y))
prop-excl pA pB u (inj₂ y) (inj₂ y') = ap inj₂ (pB y y')
