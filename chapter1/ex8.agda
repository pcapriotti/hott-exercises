{-# OPTIONS --without-K #-}

module chapter1.ex8 where

open import equality
open import sets.nat.core
  hiding (_*_)

rec : ∀ {i}{C : Set i}
    → C → (ℕ → C → C)
    → ℕ → C
rec z f 0 = z
rec z f (suc n) = f n (rec z f n)

ind : ∀ {i}(P : ℕ → Set i)
    → P 0 → ((n : ℕ) → P n → P (suc n))
    → (n : ℕ) → P n
ind P z f 0 = z
ind P z f (suc n) = f n (ind P z f n)

_*_ : ℕ → ℕ → ℕ
_*_ m = rec 0 (λ _ mn → m + mn)
infixl 7 _*_

_^_ : ℕ → ℕ → ℕ
_^_ n = rec 1 (λ _ e → n * e)

+-left-unit : ∀ n → 0 + n ≡ n
+-left-unit n = refl

+-right-unit : ∀ n → n + 0 ≡ n
+-right-unit = ind (λ n → n + 0 ≡ n) refl (λ _ → ap suc)

+-associativity : ∀ n m p → n + m + p ≡ n + (m + p)
+-associativity = ind (λ n → ∀ m p → n + m + p ≡ n + (m + p))
                      (λ _ _ → refl)
                      (λ n r m p → ap suc (r m p))

+-suc : ∀ n m → suc n + m ≡ n + suc m
+-suc = ind (λ n → ∀ m → suc n + m ≡ n + suc m)
            (λ m → refl)
            (λ n ih m → ap suc (ih m))

+-commutativity : ∀ n m → n + m ≡ m + n
+-commutativity = ind (λ n → ∀ m → n + m ≡ m + n)
                      (λ m → sym (+-right-unit m))
                      (λ n ih m → step n m (ih m))
  where
    open ≡-Reasoning

    step : ∀ n m
         → n + m ≡ m + n
         → suc n + m ≡ m + suc n
    step n m ih = begin
        suc (n + m)
      ≡⟨ ap suc ih ⟩
        suc (m + n)
      ≡⟨ +-suc m n ⟩
        m + suc n
      ∎

*-left-unit : ∀ n → 1 * n ≡ n
*-left-unit = ind (λ n → 1 * n ≡ n) refl (λ _ → ap suc)

*-right-unit : ∀ n → n * 1 ≡ n
*-right-unit n = +-right-unit n

left-distr : ∀ n m p → n * (m + p) ≡ n * m + n * p
left-distr n = ind (λ m → ∀ p → n * (m + p) ≡ n * m + n * p)
                   (λ _ → refl)
                   (λ m ih p → ap (_+_ n) (ih p)
                             · sym (+-associativity n _ _))

*-associativity : ∀ n m p → n * m * p ≡ n * (m * p)
*-associativity n m = ind (λ p → n * m * p ≡ n * (m * p))
                          refl
                          (λ p ih → ap (_+_ (n * m)) ih
                                  · sym (left-distr n m (m * p)))
