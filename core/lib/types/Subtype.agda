{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.NType2

-- [Subtype] is defined in lib.NType.

module lib.types.Subtype where

infix 40 _⊆_
_⊆_ : ∀ {i j₁ j₂} {A : Type i} → SubtypeProp A j₁ → SubtypeProp A j₂
  → Type (lmax i (lmax j₁ j₂))
P₁ ⊆ P₂ = ∀ a → SubtypeProp.prop P₁ a → SubtypeProp.prop P₂ a

infix 80 _∘sub_
_∘sub_ : ∀ {i j k} {A : Type i} {B : Type j}
  → SubtypeProp B k → (A → B) → SubtypeProp A k
_∘sub_ {A = A} P f = SubtypeProp.prop P ∘ f , level where
  abstract
    level : (a : A) → is-prop ((SubtypeProp.prop P ∘ f) a)
    level = SubtypeProp.level P ∘ f

Subtype-has-dec-eq : ∀ {i j} {A : Type i} (subProp : SubtypeProp A j)
  → has-dec-eq A → has-dec-eq (Subtype subProp)
Subtype-has-dec-eq subProp dec s₁ s₂ with dec (fst s₁) (fst s₂)
... | inl s₁=s₂ = inl (Subtype=-out subProp s₁=s₂)
... | inr s₁≠s₂ = inr λ s₁=s₂ → s₁≠s₂ (ap fst s₁=s₂)

{- Dependent paths in a Σ-type -}
module _ {i j k} {A : Type i} {B : A → Type j} (subB : (a : A) → SubtypeProp (B a) k)
  where

  ↓-Subtype-in : {x x' : A} {p : x == x'} {r : B x} {r' : B x'}
    {s : SubtypeProp.prop (subB x) r} {s' : SubtypeProp.prop (subB x') r'}
    (q : r == r' [ B ↓ p ])
    → (r , s) == (r' , s') [ (λ x → Subtype (subB x)) ↓ p ]
  ↓-Subtype-in {p = idp} q = Subtype=-out (subB _) q
