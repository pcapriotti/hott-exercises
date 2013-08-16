{-# OPTIONS --without-K #-}

module chapter2.ex1 {i}{A : Set i} where

open import equality.core

id' : {x y : A} → x ≡ y → x ≡ y
id' = J (λ x y _ → x ≡ y)
        (λ x → refl) _ _

trans₁ : {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans₁ p = J (λ x y p → ∀ z → y ≡ z → x ≡ z)
             (λ x z q → q) _ _ p _

trans₂ : {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans₂ {x} p q = J (λ y z q → x ≡ y → x ≡ z)
                   (λ y p → p) _ _ q p

trans₃ : {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans₃ p = J (λ x y p → ∀ z → y ≡ z → x ≡ z)
             (λ x z → id') _ _ p _

eq₁₂ : {x y z : A}(p : x ≡ y)(q : y ≡ z)
     → trans₁ p q ≡ trans₂ p q
eq₁₂ refl refl = refl

eq₂₃ : {x y z : A}(p : x ≡ y)(q : y ≡ z)
     → trans₂ p q ≡ trans₃ p q
eq₂₃ refl refl = refl

eq₁₃ : {x y z : A}(p : x ≡ y)(q : y ≡ z)
     → trans₁ p q ≡ trans₃ p q
eq₁₃ refl refl = refl
