{-# OPTIONS --without-K #-}
module chapter2.ex7 where

open import sum
open import equality

ap-Σ : ∀ {i j k}{A : Set i}{B : A → Set j}{Z : Set k}
     → (f : Z → A)(g : (z : Z) → B (f z))
     → {z z' : Z}(p : z ≡ z')
     → ap {B = Σ A B} (λ z → (f z , g z)) p
     ≡ unapΣ (ap f p , sym (subst-naturality B f p (g z)) · ap' g p)
ap-Σ f g refl = refl
