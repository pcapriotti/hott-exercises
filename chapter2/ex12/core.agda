{-# OPTIONS --without-K #-}
module chapter2.ex12.core where

open import level
open import sum
open import equality
open import function
open import hott hiding (h)
open import sets.unit

open import chapter2.ex11

record Square₂ i : Set (lsuc i) where
  field
    A B C D E F : Set i
    l-is-sq : IsSquare C B D A
    u : E → F
    v : D → F
    t : C → E

--      h     t
--   A --> C --> E
--   |     |     |
-- k |   f |     | u
--   v     v     v
--   B --> D --> F
--      g     v

  open IsSquare l-is-sq public

  left : Square i
  left = mk-square _ _ _ _ l-is-sq

  right : Square i
  right = mk-square' _ _ _ _ u v t f

  is-square : IsSquare E B F A
  is-square = mk-is-square u (v ∘' g) (t ∘' h) k

  outer : Square i
  outer = mk-square _ _ _ _ is-square

outer-comm : ∀ {i} (sq₂ : Square₂ i)
           → IsCommutative (Square₂.left sq₂)
           → IsCommutative (Square₂.right sq₂)
           → IsCommutative (Square₂.outer sq₂)
outer-comm sq₂ lcomm rcomm a = rcomm (h a) · ap v (lcomm a)
  where
    open Square₂ sq₂

private
  module Isom {i}(sq₂ : Square₂ i)
              (lcomm : IsCommutative (Square₂.left sq₂))
              (rpb : IsPullback (Square₂.right sq₂)) where

    open IsPullback rpb
      renaming ( comm to rcomm
               ; univ-iso to runiv-iso
               ; univ-β₂ to runiv-β₂ )

    comm = outer-comm sq₂ lcomm rcomm

    open Square₂ sq₂
    open IsPullbackDef outer comm
    open IsPullbackDef left lcomm
      using ()
      renaming (univ to luniv)

    abstract
      pb₂-isom : (X : Set i)
               → Pullback.P (comp X f) (comp X g)
               ≅ Pullback.P (comp X u) (comp X (v ∘ g))
      pb₂-isom X = begin
          Pullback.P (comp X f) (comp X g)
        ≅⟨ Σ-ap-iso₁ (×-ap-iso (runiv-iso X) refl≅) ⟩
          ( Σ (Pullback.P (comp X u) (comp X v) × (X → B)) λ { (((γ , β) , p) , α)
          → β ≡ g ∘' α } )
        ≅⟨ record
              { to = λ { ((((γ , β) , p) , α) , q) → (γ , α , (β , q) , p) }
              ; from = λ { (γ , α , (β , q) , p) → ((((γ , β) , p) , α) , q) }
              ; iso₁ = λ _ → refl
              ; iso₂ = λ _ → refl } ⟩
          ( Σ (X → E) λ γ
          → Σ (X → B) λ α
          → Σ (singleton' (g ∘ α)) λ { (β , q)
          → u ∘' γ ≡ v ∘' β } )
        ≅⟨ ( Σ-ap-iso₂ λ γ
            → Σ-ap-iso₂ λ α
            → Σ-ap-iso₂ λ { (β , q)
            → trans≡-iso' (ap (_∘'_ v) q) } ) ⟩
          ( Σ (X → E) λ γ
          → Σ (X → B) λ α
          → Σ (singleton' (g ∘ α)) λ { (β , q)
          → u ∘' γ ≡ v ∘' g ∘' α } )
        ≅⟨ ( Σ-ap-iso₂ λ γ
           → Σ-ap-iso₂ λ α
           → trans≅ (×-ap-iso (contr-⊤-iso (singl-contr' _)) refl≅)
                       ×-left-unit ) ⟩
          ( Σ (X → E) λ γ
          → Σ (X → B) λ α
          → u ∘' γ ≡ v ∘' (g ∘' α) )
        ≅⟨ sym≅ Σ-assoc-iso ⟩
          Pullback.P (comp X u) (comp X (v ∘ g))
        ∎
        where open ≅-Reasoning

      pb₂-isom-compute : (X : Set i)
                       → (β : X → C)
                       → (α : X → B)
                       → (p : f ∘' β ≡ g ∘' α)
                       → apply (pb₂-isom X) ((β , α) , p)
                       ≡ ( (t ∘' β , α)
                         , ((funext λ x → rcomm (β x)) · ap (_∘'_ v) p))
      pb₂-isom-compute X β α p = refl

      pb₂-isom-univ : (X : Set i)
                    → (δ : X → A)
                    → apply (pb₂-isom X) (luniv X δ)
                    ≡ univ X δ
      pb₂-isom-univ X δ = unapΣ (refl , lem)
        where
          lem : (funext λ x → rcomm (h (δ x)))
              · (ap (_∘'_ v) (funext λ x → lcomm (δ x)))
              ≡ (funext λ x → rcomm (h (δ x)) · (ap v (lcomm (δ x))))
          lem = begin
                  (funext λ x → rcomm (h (δ x)))
                · ap (_∘'_ v) (funext λ x → lcomm (δ x))
              ≡⟨ ap (_·_ (funext λ x → rcomm (h (δ x))))
                    (sym (funext-ap v (λ x → lcomm (δ x)))) ⟩
                  (funext λ x → rcomm (h (δ x)))
                · (funext λ x → ap v (lcomm (δ x)))
              ≡⟨ sym (funext-hom _ _) ⟩
                (funext λ x → rcomm (h (δ x)) · ap v (lcomm (δ x)))
            ∎
            where open ≡-Reasoning

open Isom public using (pb₂-isom; pb₂-isom-compute; pb₂-isom-univ)
