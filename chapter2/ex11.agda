{-# OPTIONS --without-K #-}
module chapter2.ex11 where

open import level
open import sum
open import equality
open import function
open import hott.weak-equivalence

record IsSquare {i} (A B C P : Set i) : Set i where
  constructor mk-is-square
  field
    f : A → C
    g : B → C
    h : P → A
    k : P → B

-- a square diagram
record Square i : Set (lsuc i) where
  constructor mk-square
  field
    A : Set i
    B : Set i
    C : Set i
    P : Set i
    is-square : IsSquare A B C P
  open IsSquare is-square public

mk-square' : ∀ {i} (A B C P : Set i)
          → (A → C) → (B → C)
          → (P → A) → (P → B)
          → Square i
mk-square' A B C P f g h k
  = mk-square A B C P (mk-is-square f g h k)

-- definition of commutative square
IsCommutative : ∀ {i} → Square i → Set _
IsCommutative s = (u : P) → f (h u) ≡ g (k u)
  where open Square s

-- homotopy pullback, as in 2.15.11
module Pullback {i} {A : Set i}{B : Set i}{C : Set i}
                (f : A → C)(g : B → C) where
  P = Σ (A × B) λ {(x , y) → f x ≡ g y}

  h : P → A
  h ((x , _) , _) = x

  k : P → B
  k ((_ , y) , _) = y

  sq : Square i
  sq = mk-square' A B C P f g h k

-- auxiliary definitions for defining pullback square
module IsPullbackDef {i}(sq : Square i)(comm : IsCommutative sq) where
  open Square sq

  comp : {U V : Set i} → (X : Set i)
       → (U → V) → (X → U) → (X → V)
  comp _ u v x = u (v x)

  univ : (X : Set i) → (X → P) → Pullback.P (comp X f) (comp X g)
  univ X u = (h ∘ u , k ∘ u) , funext λ x → comm (u x)

  PullbackUniv : Set _
  PullbackUniv = (X : Set i) → weak-equiv (univ X)

-- definition of pullback square
record IsPullback {i}(sq : Square i) : Set (lsuc i) where
  field comm : IsCommutative sq
  open IsPullbackDef sq comm
  field univ-equiv : PullbackUniv

  open Square sq
  univ-iso : (X : Set i)
           → (X → P) ≅ Pullback.P (comp X f) (comp X g)
  univ-iso X = ≈⇒≅ (univ X , univ-equiv X)

  univ-β₁ : (X : Set i) (α : X → A)(β : X → B)
          → (p : f ∘ α ≡ g ∘ β)
          → h ∘ invert (univ-iso X) ((α , β) , p) ≡ α
  univ-β₁ X α β p = ap (proj₁ ∘ proj₁) (_≅_.iso₂ (univ-iso X) ((α , β) , p))

  univ-β₂ : (X : Set i) (α : X → A)(β : X → B)
          → (p : f ∘ α ≡ g ∘ β)
          → k ∘ invert (univ-iso X) ((α , β) , p) ≡ β
  univ-β₂ X α β p = ap (proj₂ ∘ proj₁) (_≅_.iso₂ (univ-iso X) ((α , β) , p))

-- properties of definition 2.15.11 (i.e. Pullback)
module PullbackProp {i} {A : Set i}{B : Set i}{C : Set i}
                    (f : A → C)(g : B → C) where
  open Pullback f g

  -- Pullback.sq is a commutative square
  comm : IsCommutative sq
  comm ((x , y) , p) = p

  open IsPullbackDef sq comm

  -- universal property of the pullback
  isom : (X : Set i) → (X → P) ≅ Pullback.P (comp X f) (comp X g)
  isom X = begin
      (X → P)
    ≅⟨ ΠΣ-swap-iso ⟩
      ( Σ (X → A × B) λ uv
      → ((x : X) → f (proj₁ (uv x)) ≡ g (proj₂ (uv x))) )
    ≅⟨ ( Σ-ap-iso ΠΣ-swap-iso (λ u → strong-funext-iso) ) ⟩
      Pullback.P (comp X f) (comp X g)
    ∎
    where open ≅-Reasoning

  -- t X is an equivalence by direct computation
  -- of the above isomorphism
  is-pullback : IsPullback sq
  is-pullback = record
    { comm = comm
    ; univ-equiv = λ X → proj₂ (≅⇒≈ (isom X)) }
