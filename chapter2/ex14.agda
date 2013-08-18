{-# OPTIONS --without-K #-}
module chapter2.ex14 where

open import level
open import equality

UIP : ∀ i → Set (lsuc i)
UIP i = {A : Set i}{x : A}(p : x ≡ x) → p ≡ refl

{-

The following would typecheck if agda had the equality reflection rule:

uip : ∀ {i} → UIP i
uip {x = x} p
  = J (λ x y p → p ≡ refl)
      (λ x → refl)
      x x p

-}

module with-uip (uip : ∀ {i} → UIP i) where
  open import hott.hlevel.core

  uip' : ∀ {i}{A : Set i}{x y : A}(p q : x ≡ y) → p ≡ q
  uip' p q = begin
      p
    ≡⟨ sym (left-unit p)
     · ap (_·_ p) (sym (right-inverse q))
     · sym (associativity p (sym q) q) ⟩
      p · sym q · q
    ≡⟨ ap (λ z → z · q) (uip (p · sym q))
     · right-unit q ⟩
      q
    ∎
    where open ≡-Reasoning

  type-is-set : ∀ {i}{A : Set i} → h 2 A
  type-is-set x y = prop⇒h1 uip'
