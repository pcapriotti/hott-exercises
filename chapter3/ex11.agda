{-# OPTIONS --without-K #-}
module chapter3.ex11 where

open import level
open import equality
open import function
open import sum
open import hott

module _ {i}(η-inv : {A : Set i} → ∥ A ∥ → A) where
  abstract
    endo : {A : Set i} → A → A
    endo = η-inv ∘' η

    endo-const : {A : Set i}(x y : A) → endo x ≡ endo y
    endo-const x y = ap η-inv (trunc-prop (η x) (η y))

  -- the proof of hedberg's theorem applies to all types now
  hedberg' : {A : Set i} → h 2 A
  hedberg' {A = A} x y = prop⇒h1 ≡-prop
    where
      open ≡-Reasoning

      endo-inv : {x y : A}(p : x ≡ y)
               → endo p · sym (endo refl) ≡ p
      endo-inv refl = left-inverse (endo refl)

      ≡-prop : {x y : A}(p q : x ≡ y) → p ≡ q
      ≡-prop p q = begin
          p
        ≡⟨ sym (endo-inv p) ⟩
          endo p · sym (endo refl)
        ≡⟨ ap (λ z → z · sym (endo refl))
                (endo-const p q) ⟩
          endo q · sym (endo refl)
        ≡⟨ endo-inv q ⟩
          q
        ∎
