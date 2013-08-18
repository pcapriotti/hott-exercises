{-# OPTIONS --without-K #-}
module chapter2.ex13 where

open import sum
open import decidable
open import equality
open import function
open import hott.weak-equivalence
open import hott.univalence
open import hott.hlevel
open import sets.bool
open import sets.empty
open import sets.unit

not-invol : (x : Bool) → not (not x) ≡ x
not-invol true = refl
not-invol false = refl

not-iso : Bool ≅ Bool
not-iso = record
  { to = not
  ; from = not
  ; iso₁ = not-invol
  ; iso₂ = not-invol }

bool-nontrivial : ¬ (true ≡ false)
bool-nontrivial ()

bool-tf : (b b' : Bool) → ¬ (b ≡ b') → b ≡ not b'
bool-tf true true u = ⊥-elim (u refl)
bool-tf true false u = refl
bool-tf false true u = refl
bool-tf false false u = ⊥-elim (u refl)

bool-to-func : Bool → Bool → Bool
bool-to-func true = id
bool-to-func false = not

bool-to-equiv : (b : Bool) → weak-equiv (bool-to-func b)
bool-to-equiv true = coerce-equiv refl
bool-to-equiv false = proj₂ (≅⇒≈ not-iso)

images : (f : Bool → Bool) → weak-equiv f
       → ¬ (f true ≡ f false)
images f we p = bool-nontrivial (iso⇒inj (≈⇒≅ (f , we)) p)

image-not : (f : Bool → Bool) → weak-equiv f
          → f false ≡ not (f true)
image-not f we = bool-tf (f false) (f true) (images f we ∘ sym)

classify : (f : Bool → Bool) → weak-equiv f
         → (x : Bool) → bool-to-func (f true) x ≡ f x
classify f we true with f true ≟ true
... | yes p = subst (λ z → bool-to-func z true ≡ z)
                    (sym p) refl
... | no u = subst (λ z → bool-to-func z true ≡ z)
                   (sym (bool-tf (f true) true u)) refl
classify f we false with f true ≟ true
... | yes p = ap (λ z → bool-to-func z false) p
            · sym (image-not f we · ap not p)
... | no u = ap (λ z → bool-to-func z false) p
           · sym (image-not f we · ap not p)
  where
    p : f true ≡ false
    p = bool-tf (f true) true u

equiv-eq : ∀ {i j}{A : Set i}{B : Set j}
         → {f g : A → B}
         → {f-we : weak-equiv f}
         → {g-we : weak-equiv g}
         → f ≡ g
         → (f , f-we) ≡ (g , g-we)
equiv-eq {f = f} {f-we = f-we} {g-we} refl
  = ap (_,_  f) (h1⇒prop (weak-equiv-h1 f) f-we g-we)

isom : (Bool ≈ Bool) ≅ Bool
isom = record
  { to = λ f → proj₁ f true
  ; from = λ b → bool-to-func b , bool-to-equiv b
  ; iso₁ = λ { (f , we) → equiv-eq (funext (classify f we)) }
  ; iso₂ = λ { true → refl ; false → refl } }
