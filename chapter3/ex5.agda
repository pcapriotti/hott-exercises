{-# OPTIONS --without-K #-}
module chapter3.ex5 where

open import sum
open import hott

prop⇒hyp-contr : ∀ {i}{A : Set i}
                → h 1 A
                → (A → contr A)
prop⇒hyp-contr hA x = x , h1⇒prop hA x

hyp-contr⇒prop : ∀ {i}{A : Set i}
                → (A → contr A)
                → h 1 A
hyp-contr⇒prop f = prop⇒h1 λ x y
                  → h1⇒prop (h↑ (f x)) x y
