{-# OPTIONS --without-K #-}
module chapter3.ex8 where

open import level
open import equality
open import function
open import hott

record qinv {i j}{A : Set i}{B : Set j} (to : A → B) : Set (i ⊔ j) where
  constructor mk-qinv
  field
    from : B → A
    iso₁ : (x : A) → from (to x) ≡ x
    iso₂ : (y : B) → to (from y) ≡ y

  isom : A ≅ B
  isom = iso to from iso₁ iso₂

iso⇒qinv : ∀ {i j}{A : Set i}{B : Set j}
          → (f : A ≅ B)
          → qinv (apply f)
iso⇒qinv (iso _ g α β) = mk-qinv g α β

record IsEquiv {i j k}(A : Set i)(B : Set j)
                      (X : (A → B) → Set k) : Set (i ⊔ j ⊔ k) where
  field
    iso⇒equiv : (f : A → B) → qinv f → X (apply f)
    equiv⇒iso : (f : A → B) → X f → qinv f
    h1-equiv : ∀ f → h 1 (X f)

module _ {i j k}{A : Set i}{B : Set j}
         (equiv : (A → B) → Set k)
         (eq : IsEquiv A B equiv) where
  open IsEquiv

  trunc-qinv-is-equiv : IsEquiv A B (λ f → ∥ qinv f ∥)
  trunc-qinv-is-equiv = record
    { iso⇒equiv = λ _ → η
    ; equiv⇒iso = λ f e → equiv⇒iso eq f (lem f e)
    ; h1-equiv = λ f → prop⇒h1 trunc-prop }
    where
      lem : (f : A → B)(e : ∥ qinv f ∥) → equiv f
      lem f = elim' (h1-equiv eq f) (iso⇒equiv eq f)

  trunc-qinv⇔equiv : ∀ f → ∥ qinv f ∥ ≅ equiv f
  trunc-qinv⇔equiv f = record
    { to = elim' (h1-equiv eq f) (iso⇒equiv eq f)
    ; from = η ∘' equiv⇒iso eq f
    ; iso₁ = λ e → trunc-prop _ _
    ; iso₂ = λ e → h1⇒prop (h1-equiv eq f) _ _ }
