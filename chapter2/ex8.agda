{-# OPTIONS --without-K #-}
module chapter2.ex8 where

open import sum
open import equality

[_,_] : ∀ {i j k}{A : Set i}{B : Set j}{Z : Set k}
      → (A → Z) → (B → Z)
      → A ⊎ B → Z
[ f , g ] (inj₁ x) = f x
[ f , g ] (inj₂ y) = g y

ap-⊎₁ : ∀ {i j k}{A : Set i}{B : Set j}{Z : Set k}
      → (f : A → Z)(g : B → Z)
      → {x x' : A}(p : x ≡ x')
      → ap [ f , g ] (ap inj₁ p)
      ≡ ap f p
ap-⊎₁ f g refl = refl

ap-⊎₂ : ∀ {i j k}{A : Set i}{B : Set j}{Z : Set k}
      → (f : A → Z)(g : B → Z)
      → {y y' : B}(p : y ≡ y')
      → ap [ f , g ] (ap inj₂ p)
      ≡ ap g p
ap-⊎₂ f g refl = refl
