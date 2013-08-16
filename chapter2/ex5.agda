{-# OPTIONS --without-K #-}

module chapter2.ex5
  {i j} {A : Set i}{B : Set j} (f : A → B) where

open import equality

u : {x y : A}(p : x ≡ y)
  → f x ≡ f y
  → subst (λ _ → B) p (f x) ≡ f y
u {x} p q = subst-const p (f x) · q

v : {x y : A}(p : x ≡ y)
  → subst (λ _ → B) p (f x) ≡ f y
  → f x ≡ f y
v {x} p q = sym (subst-const p (f x)) · q

α : {x y : A}(p : x ≡ y)(q : f x ≡ f y)
  → v p (u p q) ≡ q
α refl q = refl

β : {x y : A}(p : x ≡ y)(q : subst (λ _ → B) p (f x) ≡ f y)
  → u p (v p q) ≡ q
β refl q = refl
