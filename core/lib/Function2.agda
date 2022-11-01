{-# OPTIONS --without-K --rewriting --allow-unsolved-meta #-}

open import lib.Basics
open import lib.types.Truncation
open import lib.types.Sigma
open import lib.types.Paths
open import lib.Equivalence

module lib.Function2 where

is-surj : ∀ {i j} {A : Type i} {B : Type j} (f : A → B) → Type (lmax i j)
is-surj {A = A} f = ∀ b → Trunc -1 (hfiber f b)

module _ {i j k} {A : Type i} {B : Type j} {C : Type k}
  {f : A → B} {g : B → C} where
  abstract
    ∘-is-surj : is-surj g → is-surj f → is-surj (g ∘ f)
    ∘-is-surj g-is-surj f-is-surj c =
      Trunc-rec
        (λ{(b , gb=c) →
          Trunc-rec
          (λ{(a , fa=b) → [ a , ap g fa=b ∙ gb=c ]})
          (f-is-surj b)})
        (g-is-surj c)

module _ {i j} {A : Type i} {B : Type j} {f : A → B} where
  abstract
    equiv-is-surj : is-equiv f → is-surj f
    equiv-is-surj f-is-equiv b = [ g b , f-g b ]
      where open is-equiv f-is-equiv

hfiber-pth-characterization : ∀ {i j} {A : Type i} {B : Type j} (f : A → B) (x : B)
  → {p q : hfiber f x}
  → (p == q) ≃ Σ (fst p == fst q) λ r → ap f r ∙ snd q == snd p
hfiber-pth-characterization f x {p} {q} =
  Σ-emap-r (λ { idp → !-equiv }) ∘e =Σ-econv p q ⁻¹

is-embedding : ∀ {i j} {A : Type i} {B : Type j} (f : A → B) → Type (lmax i j)
is-embedding {A = A} f = {x y : A} → is-equiv (ap f {x} {y})

id-is-embd : ∀ {i} (A : Type i) → is-embedding (idf A)
id-is-embd A = transport is-equiv (! (λ= ap-idf)) (idf-is-equiv _)

embedding-inj : ∀ {i} {A B : Type i} (f : A → B)
  → is-embedding f
  → is-inj f
embedding-inj f f-is-embd a₁ a₂ = <– (_ , f-is-embd)

eq-is-embedding : ∀ {i} {A B : Type i}
  → (e : A ≃ B)
  → is-embedding (–> e)
eq-is-embedding e = equiv-induction (λ e → is-embedding (–> e)) id-is-embd e
