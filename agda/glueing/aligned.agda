{-# OPTIONS --rewriting #-}
module glueing.aligned where

open import glueing.core
open import glueing.strict

open import prelude
open import interval
open import cof
open import fibrations
open import equivs
open import realignment

----------------------------------------------------------------------
-- Realigning strict glue
----------------------------------------------------------------------

FibSGlue :
  ∀{a}{Γ : Set a}
  (Φ : Γ → Cof)
  {A : res Γ Φ → Set}
  {B : Γ → Set}
  (f : (xu : res Γ Φ) → A xu → B (xu .fst))
  (equiv : Equiv' f)
  → ---------------
  isFib A → isFib B → isFib (SGlue' Φ A B f)
FibSGlue {a} {Γ} Φ {A} {B} f equiv α β =
  realign Φ (SGlue' Φ A B f)
    (subst isFib (SGlueStrictness' Φ f) α)
    (Misaligned.FibSGlue Φ f equiv α β)

FibSGlueStrictness :
  {ℓ : Level}
  {Γ : Set ℓ}
  (Φ : Γ → Cof)
  {A : res Γ Φ → Set}
  {B : Γ → Set}
  (f : (xu : res Γ Φ) → A xu → B (xu .fst))
  (equiv : Equiv' f)
  (α : isFib A) (β : isFib B)
  → ---------------
  subst isFib (SGlueStrictness' Φ f) α ≡ reindex (SGlue' Φ A B f) (FibSGlue Φ f equiv α β) fst
FibSGlueStrictness Φ {A} {B} f equiv α β =
  symm
    (isRealigned Φ (SGlue' Φ A B f)
      (subst isFib (SGlueStrictness' Φ f) α)
      (Misaligned.FibSGlue Φ f equiv α β))

SGlueFib :
  ∀{a}{Γ : Set a}
  (Φ : Γ → Cof)
  (Aα : Fib (res Γ Φ))
  (Bβ : Fib Γ)
  (f : (xu : res Γ Φ) → Aα .fst xu → Bβ .fst (xu .fst))
  (equiv : Equiv' f)
  → ---------------
  Fib Γ
SGlueFib {a} {Γ} Φ (A , α) (B , β) f equiv =
  (SGlue' Φ A B f , FibSGlue Φ f equiv α β)

SGlueFibStrictness :
  ∀{ℓ}{Γ : Set ℓ}
  (Φ : Γ → Cof)
  (Aα : Fib (res Γ Φ))
  (Bβ : Fib Γ)
  (f : (xu : res Γ Φ) → Aα .fst xu → Bβ .fst (xu .fst))
  (equiv : Equiv' f)
  → Aα ≡ reindex' (SGlueFib Φ Aα Bβ f equiv) fst
SGlueFibStrictness Φ (A , α) (B , β) f equiv =
  Σext (SGlueStrictness' Φ f) (FibSGlueStrictness Φ f equiv α β)

reindexFibSGlue :
  ∀ {ℓ} {Δ Γ : Set ℓ}
  (Φ : Γ → Cof)
  {A : res Γ Φ → Set}
  {B : Γ → Set}
  (f : (xu : res Γ Φ) → A xu → B (xu .fst))
  (equiv : Equiv' f)
  (α : isFib A) (β : isFib B)
  (ρ : Δ → Γ)
  → reindex (SGlue' Φ A B f) (FibSGlue Φ f equiv α β) ρ
    ≡ FibSGlue (Φ ∘ ρ) (f ∘ (ρ ×id)) (equiv ∘ (ρ ×id)) (reindex A α (ρ ×id)) (reindex B β ρ)
reindexFibSGlue Φ {A} {B} f equiv α β ρ =
  trans
    (cong₂ (realign (Φ ∘ ρ) (SGlue' Φ A B f ∘ ρ))
      (reindexSubst (ρ ×id) (SGlueStrictness' Φ f) (SGlueStrictness' (Φ ∘ ρ) (f ∘ (ρ ×id))) α)
      (Misaligned.reindexFibSGlue Φ f equiv α β ρ))
    (reindexRealign  Φ (SGlue' Φ A B f)
      (subst isFib (SGlueStrictness' Φ f) α)
      (Misaligned.FibSGlue Φ f equiv α β)
      ρ)
  where
  reindexSubst : ∀ {ℓ ℓ'} {Δ : Set ℓ} {Γ : Set ℓ'} {A A' : Γ → Set}
   (ρ : Δ → Γ)(P : A ≡ A') (Q : A ∘ ρ ≡ A' ∘ ρ) (α : isFib A)
    → reindex A' (subst isFib P α) ρ ≡ subst isFib Q (reindex A α ρ)
  reindexSubst ρ refl refl α = refl
