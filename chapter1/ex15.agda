{-# OPTIONS --without-K #-}
module chapter1.ex15 where

open import equality

-- this is the same as subst

f : ∀ {i j} {A : Set i}
  → (C : A → Set j)
  → {x y : A}(p : x ≡ y)
  → C x → C y
f C = J (λ x y p → C x → C y)
        (λ x u → u) _ _
