{-# OPTIONS --without-K #-}
module chapter3.ex17 where

open import sum
open import hott
open import equality

ind : ∀ {i j}{A : Set i}
    → (P : ∥ A ∥ → Set j)
    → ((x : ∥ A ∥) → h 1 (P x))
    → ((x : A) → P (η x))
    → (x : ∥ A ∥) → P x
ind {A = A} P hP f x = subst P (trunc-prop _ _) (proj₂ (f' x))
  where
    S : Set _
    S = Σ ∥ A ∥ P

    hS : h 1 S
    hS = Σ-hlevel (prop⇒h1 trunc-prop) hP

    f' : ∥ A ∥ → S
    f' = elim' hS λ x → η x , f x
