{-# OPTIONS --without-K #-}
module chapter1.ex9 where

open import sets.nat
open import sets.fin

ind : ∀ {i} (P : ∀ {n} → Fin n → Set i)
    → (∀ {n} → P {suc n} zero)
    → (∀ {n} (i : Fin n) → P i → P (suc i))
    → ∀ {n} (i : Fin n) → P i
ind P d₀ ds zero = d₀
ind P d₀ ds (suc i) = ds i (ind P d₀ ds i)

fmax : ∀ n → Fin (suc n)
fmax zero = zero
fmax (suc i) = suc (fmax i)
