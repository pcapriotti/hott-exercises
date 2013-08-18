{-# OPTIONS --without-K #-}
module chapter3.ex15 where

open import level
open import hott

-- we don't have propositional resizing here, but this definition still works,
-- although it resides in a bigger universe
inhab : ∀ {i} → Set i → Set (lsuc i)
inhab {i} A = (P : Set i) → h 1 P
            → (A → P) → P

inhab-h1 : ∀ {i}{A : Set i} → h 1 (inhab A)
inhab-h1 = Π-hlevel λ P
         → Π-hlevel λ hP
         → Π-hlevel λ f
         → hP

inhab-η : ∀ {i}{A : Set i} → A → inhab A
inhab-η x P hP f = f x

inhab-univ : ∀ {i}{A P : Set i}
           → h 1 P
           → (A → P)
           → inhab A → P
inhab-univ hP f x = x _ hP f
