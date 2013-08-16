{-# OPTIONS --without-K #-}
module chapter1.ex11 where

open import sets.empty

double-neg : ∀ {i} {A : Set i} → A → ¬ ¬ A
double-neg a f = f a

triple-neg-elim : ∀ {i} {A : Set i}
                → ¬ ¬ ¬ A
                → ¬ A
triple-neg-elim f a = f (double-neg a)
