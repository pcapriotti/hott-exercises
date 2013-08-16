{-# OPTIONS --without-K #-}

module chapter2.ex4 where

open import sum
open import equality.core
open import sets.nat

Paths : ∀ {i} → ℕ → Set i → Set _
Paths 0 A = A
Paths (suc n) A = Σ (Paths n A × Paths n A) λ { (p₁ , p₂) → p₁ ≡ p₂ }
