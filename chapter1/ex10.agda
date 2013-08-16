{-# OPTIONS --without-K #-}
module chapter1.ex10 where

open import equality
open import sets.nat

rec : ∀ {i}{C : Set i}
    → C → (ℕ → C → C)
    → ℕ → C
rec z f 0 = z
rec z f (suc n) = f n (rec z f n)

ack : ℕ → ℕ → ℕ
ack = rec suc (λ _ f → rec (f 1) (λ _ → f))

ack' : ℕ → ℕ → ℕ
ack' 0 n = suc n
ack' (suc m) 0 = ack' m 1
ack' (suc m) (suc n) = ack' m (ack' (suc m) n)
