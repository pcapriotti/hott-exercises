{-# OPTIONS --without-K #-}
module chapter2.ex12.part1 where

open import sum
open import equality
open import function
open import hott hiding (h)

open import chapter2.ex11
open import chapter2.ex12.core

is-pullback₂ : ∀ {i} (sq₂ : Square₂ i)
             → IsPullback (Square₂.left sq₂)
             → IsPullback (Square₂.right sq₂)
             → IsPullback (Square₂.outer sq₂)
is-pullback₂ {i} sq₂ lpb rpb = record
  { comm = comm
  ; univ-equiv = λ X → subst weak-equiv
                       (funext (isom-compute X))
                       (proj₂ (≅⇒≈ (isom X))) }
  where
    open IsPullback lpb
      renaming ( comm to lcomm
               ; univ-iso to luniv-iso )
    open IsPullback rpb
      renaming ( comm to rcomm
               ; univ-iso to runiv-iso
               ; univ-β₂ to runiv-β₂ )

    comm = outer-comm sq₂ lcomm rcomm

    open Square₂ sq₂
    open IsPullbackDef outer comm
    open IsPullbackDef right rcomm
      using () renaming (univ to runiv)

    isom : (X : Set i)
         → (X → A)
         ≅ Pullback.P (comp X u) (comp X (v ∘' g))
    isom X = begin
        (X → A)
      ≅⟨ luniv-iso X ⟩
        Pullback.P (comp X f) (comp X g)
      ≅⟨ pb₂-isom sq₂ lcomm rpb X ⟩
        Pullback.P (comp X u) (comp X (v ∘ g))
      ∎
      where
        open ≅-Reasoning

    isom-compute : (X : Set i)(δ : X → A)
                 → apply (isom X) δ
                 ≡ univ X δ
    isom-compute X δ = pb₂-isom-univ sq₂ lcomm rpb X δ
