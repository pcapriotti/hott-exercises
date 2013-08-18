{-# OPTIONS --without-K #-}
module chapter3.ex9 where

open import level
open import sum
open import decidable
open import equality
open import function
open import sets.empty
open import sets.unit
open import sets.bool
open import hott

LEM : ∀ i → Set _
LEM i = {A : Set i} → h 1 A → Dec A

dec-to-bool : ∀ {i}{A : Set i} → Dec A → Bool
dec-to-bool (yes _) = true
dec-to-bool (no _) = false

prop-eq : ∀ {i} {A B : Set i}
        → (hA : h 1 A)(hB : h 1 B)
        → A ≅ B
        → (A , hA) ≡ (B , hB)
prop-eq {B = B} hA hB isom = unapΣ ( ≅⇒≡ isom
                                   , h1⇒prop (hn-h1 1 B) _ _)

module _ (lem : LEM lzero) where
  canonical : Bool → Σ Set (h 1)
  canonical true = ⊤ , h↑ ⊤-contr
  canonical false = ⊥ , ⊥-prop

  classify : {A : Set}(hA : h 1 A)
           → A ≅ proj₁ (canonical (dec-to-bool (lem hA)))
  classify hA with lem hA
  ... | yes x = contr-⊤-iso (x , h1⇒prop hA x)
  ... | no u = empty-⊥-iso u

  lem-⊤ : lem {⊤} (h↑ ⊤-contr) ≡ yes tt
  lem-⊤ with lem (h↑ ⊤-contr)
  ... | yes p = ap yes refl
  ... | no u = ⊥-elim (u tt)

  lem-⊥ : lem {⊥} ⊥-prop ≡ no ⊥-elim
  lem-⊥ with lem ⊥-prop
  ... | yes p = ⊥-elim p
  ... | no u = ap no (funext λ ())

  prop-bool : (Σ Set (h 1)) ≅ Bool
  prop-bool = record
    { to = λ { (A , hA) → dec-to-bool (lem hA) }
    ; from = canonical
    ; iso₁ = λ { (A , hA) →
          prop-eq (proj₂ (canonical (dec-to-bool (lem hA)))) hA
                  (sym≅ (classify hA)) }
    ; iso₂ = λ { true → subst (λ z → dec-to-bool z ≡ true) (sym lem-⊤) refl
               ; false → subst (λ z → dec-to-bool z ≡ false) (sym lem-⊥) refl } }
