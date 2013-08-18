{-# OPTIONS --without-K #-}
module chapter2.ex12.part2 where

open import sum
open import equality
open import function
open import hott hiding (h)
open import sets.unit

open import chapter2.ex11
open import chapter2.ex12.core

is-pullback₂' : ∀ {i} (sq₂ : Square₂ i)
             → (lcomm : IsCommutative (Square₂.left sq₂))
             → (rpb : IsPullback (Square₂.right sq₂))
             → IsPullbackDef.PullbackUniv (Square₂.outer sq₂)
                                          (outer-comm sq₂ lcomm (IsPullback.comm rpb))
             → IsPullback (Square₂.left sq₂)
is-pullback₂' {i} sq₂ lcomm rpb univ-equiv = record
  { comm = lcomm
  ; univ-equiv = λ X → subst weak-equiv (funext (isom-compute X))
                                        (proj₂ (≅⇒≈ (isom X))) }
  where
    open IsPullback rpb
      renaming ( comm to rcomm
               ; univ-iso to runiv-iso
               ; univ-β₂ to runiv-β₂ )

    comm = outer-comm sq₂ lcomm rcomm

    open Square₂ sq₂

    pb : IsPullback outer
    pb = record { comm = comm ; univ-equiv = univ-equiv }

    open IsPullback pb
      using (univ-iso)
    open IsPullbackDef outer comm
    open IsPullbackDef left lcomm
      using () renaming (univ to luniv)

    isom : (X : Set i)
         → (X → A)
         ≅ Pullback.P (comp X f) (comp X g)
    isom X = begin
        (X → A)
      ≅⟨ univ-iso X ⟩
        Pullback.P (comp X u) (comp X (v ∘' g))
      ≅⟨ sym≅ (pb₂-isom sq₂ lcomm rpb X) ⟩
        Pullback.P (comp X f) (comp X g)
      ∎
      where
        open ≅-Reasoning

    isom-compute : (X : Set i)
                 → ∀ δ
                 → apply (isom X) δ
                 ≡ luniv X δ
    isom-compute X = lem (pb₂-isom sq₂ lcomm rpb X)
                         (pb₂-isom-univ sq₂ lcomm rpb X)
      where
        lem : ∀ {i j k}{A : Set i}{B : Set j}{C : Set k}
            → {f : A → B}{g : A → C}
            → (h : B ≅ C)
            → (∀ x → apply h (f x) ≡ g x)
            → (∀ x → invert h (g x) ≡ f x)
        lem {f = f}{g} h p x = sym (iso⇒inj h (p x · sym (_≅_.iso₂ h (g x))))
