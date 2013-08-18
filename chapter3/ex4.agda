{-# OPTIONS --without-K #-}
module chapter3.ex4 where

open import sum
open import equality
open import function
open import hott

h1⇒exp-contr : ∀ {i}{A : Set i}
              → h 1 A
              → contr (A → A)
h1⇒exp-contr hA = id , h1⇒prop (Π-hlevel (λ _ → hA)) id

exp-contr⇒h1 : ∀ {i}{A : Set i}
              → contr (A → A)
              → h 1 A
exp-contr⇒h1 hAA = prop⇒h1 λ x y
                 → funext-inv (h1⇒prop (h↑ hAA)
                                       (λ _ → x)
                                       (λ _ → y)) x
