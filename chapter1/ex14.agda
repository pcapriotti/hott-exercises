{-# OPTIONS --without-K #-}
module chapter1.ex14 where

open import equality

-- f : ∀ {i}{A : Set i}
--   → (x : A)(p : x ≡ x)
--   → p ≡ refl
-- f x p = J (λ x y p → p ≡ refl)
--         refl x x p

-- The above is not well typed.

-- The problem is that, to apply path induction, we need to generalise the goal
-- so that both endpoints are free. When we do that in this example, the
-- equality p ≡ refl is not well-typed anymore.
