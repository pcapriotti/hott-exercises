{-# OPTIONS --without-K #-}
module chapter3.ex19 where

open import sum
open import decidable
open import equality
open import hott
open import sets.nat
open import sets.fin
open import sets.empty

module _ {i}(P : ℕ → Set i)
         (hP : (n : ℕ) → h 1 (P n))
         (P? : (n : ℕ) → Dec (P n)) where
  None : ℕ → Set _
  None n = ∀ j → j < n → ¬ P j

  none-h1 : ∀ n → h 1 (None n)
  none-h1 n = Π-hlevel λ j
            → Π-hlevel λ p
            → Π-hlevel λ _
            → ⊥-prop

  none-cons : ∀ {n} → None n → ¬ P n → None (suc n)
  none-cons {n} u v .n suc< = v
  none-cons u v j (n<s p) = u j p

  data Result (n : ℕ) : Set i where
    found : (i : ℕ) → i < n
          → P i → None i
          → Result n
    not-found : None n → Result n

  IsMin : ℕ → Set _
  IsMin n = P n × None n

  is-min-h1 : (n : ℕ) → h 1 (IsMin n)
  is-min-h1 n = ×-hlevel (hP n) (none-h1 n)

  Min : Set i
  Min = Σ ℕ IsMin

  min-eq : {n m : Min}
         → proj₁ n ≡ proj₁ m
         → n ≡ m
  min-eq {n , d}{m , d'} p = unapΣ (p , h1⇒prop (is-min-h1 m) _ _)

  min-prop : prop Min
  min-prop (n , d , u) (m , d' , u') with compare n m
  ... | lt q = ⊥-elim (u' n q d)
  ... | eq q = min-eq q
  ... | gt q = ⊥-elim (u m q d')

  find : (n : ℕ) → Result n
  find 0 = not-found (λ j ())
  find (suc n) with find n
  ... | found i q p u = found i (n<s q) p u
  ... | not-found u with P? n
  ... | yes r = found n suc< r u
  ... | no v = not-found (none-cons u v)

  min' : Σ ℕ P → Min
  min' (n , p) with find n
  ... | found i q p' u = i , p' , u
  ... | not-found u = n , p , u

  min : ∥ Σ ℕ P ∥ → Min
  min = elim' (prop⇒h1 min-prop) min'

  markov : ∥ Σ ℕ P ∥ → Σ ℕ P
  markov z = let (n , d , u) = min z in n , d
