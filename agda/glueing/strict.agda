{-

Strict Glue types.

-}
{-# OPTIONS --rewriting #-}
module glueing.strict where

open import glueing.core

open import prelude
open import interval
open import cofprop
open import fibrations
open import equivs
open import Data.paths
open import Data.products
open import strictness-axioms

----------------------------------------------------------------------
-- Strict glueing
----------------------------------------------------------------------
includeA :
  (φ : CofProp)
  {A : [ φ ] → Set}
  {B : Set}
  (f : (u : [ φ ]) → A u → B)
  → ---------------
  (u : [ φ ]) → A u → Glue φ A B f
includeA φ {A} {B} f u a =
  glue
    (λ v → moveA v a)
    (f u a)
    (λ v → cong (λ{(u , a) → f u a}) (symm (moveMove v)))
  where
  moveA : (v : [ φ ]) → A u → A v
  moveA v = subst A (cofIsProp φ _ _)
  moveMove : (v : [ φ ]) → (u , a) ≡ (v , moveA v a)
  moveMove v = Σext (cofIsProp φ _ _) refl

includeAIso :
  (φ : CofProp)
  {A : [ φ ] → Set}
  {B : Set}
  (w : (u : [ φ ]) → A u → B)
  → ---------------
  (u : [ φ ]) → A u ≅ Glue φ A B w
includeAIso φ {A} {B} w u = iso
  where
  prfIr : {a : A u} → subst A (cofIsProp φ u u) a ≡ a
  prfIr {a} = cong (λ p → subst A p a) (uip (cofIsProp φ u u) refl)

  iso : A u ≅ Glue φ A B w
  iso .to a = includeA φ w u a
  iso .from (glue a _ _) = a u
  iso .inv₁ = funext (λ a → prfIr)
  iso .inv₂ = funext fg≡id where
    parEq : {a a' : (u : [ φ ]) → A u} → a u ≡ a' u → a ≡ a'
    parEq {a} {a'} eq = funext (λ v → subst (λ v → a v ≡ a' v) (cofIsProp φ u v) eq)

    fg≡id : (gl : Glue φ A B w) → (includeA φ w u (gl .dom u)) ≡ gl
    fg≡id gl =
      glueExt w (includeA φ w u (gl .dom u)) gl (parEq prfIr) (gl .match u)

SGlue :
  (φ : CofProp)
  (A : [ φ ] → Set)
  (B : Set)
  (f : (u : [ φ ]) → A u → B)
  → ---------------
  Set
SGlue φ A B f = strictify φ A (Glue φ A B f) (includeAIso φ f)

strictifyGlueIso :
  (φ : CofProp)
  {A : [ φ ] → Set}
  {B : Set}
  (f : (u : [ φ ]) → A u → B)
  → ---------------
  SGlue φ A B f ≅ Glue φ A B f
strictifyGlueIso φ {A} {B} f = isoB φ A (Glue φ A B f) (includeAIso φ f)

sglue :
  {φ : CofProp}
  {A : [ φ ] → Set}
  {B : Set}
  (f : (u : [ φ ]) → A u → B)
  → ---------------
  (u : [ φ ]) → A u → SGlue φ A B f
sglue {φ} f u = strictifyGlueIso φ f .from ∘ includeA φ f u

sunglue :
  {φ : CofProp}
  {A : [ φ ] → Set}
  {B : Set}
  (f : (u : [ φ ]) → A u → B)
  → ---------------
  SGlue φ A B f → B
sunglue {φ} f = cod ∘ strictifyGlueIso φ f .to

SGlueStrictness :
  (φ : CofProp)
  {A : [ φ ] → Set}
  {B : Set}
  (f : (u : [ φ ]) → A u → B)
  (u : [ φ ])
  → ---------------
  A u ≡ SGlue φ A B f
SGlueStrictness φ {A} {B} f u =
  restrictsToA φ A (Glue φ A B f) (includeAIso φ f) u

sunglue-boundary :
  (φ : CofProp)
  {A : [ φ ] → Set}
  {B : Set}
  (f : (u : [ φ ]) → A u → B)
  (u : [ φ ]) (a : A u)
  → sunglue f (coe (SGlueStrictness φ f u) a) ≡ f u a
sunglue-boundary φ {A} {B} f u a =
  symm
    (appdep
      (restrictsToA φ A (Glue φ A B f) (includeAIso φ f) u)
      (trans
        (congdep (λ p → cod ∘ p .snd .to) (restrictsToM φ A (Glue φ A B f) (includeAIso φ f) u))
        (symm
          (appCong
            (subst-cong-assoc (λ D → D → B) fst
              (restrictsToM φ A (Glue φ A B f) (includeAIso φ f) u)))))
      refl)
  where
  appdep : ∀ {ℓ ℓ' ℓ''} {A : Set ℓ} {B : A → Set ℓ'} {C : Set ℓ''}
    {a a' : A} (p : a ≡ a') {f : B a → C} {f' : B a' → C}
    (q : subst (λ a → B a → C) p f ≡ f')
    {b : B a} {b' : B a'} (r : subst B p b ≡ b')
    → f b ≡ f' b'
  appdep refl refl refl = refl

----------------------------------------------------------------------
-- Indexed versions
----------------------------------------------------------------------

SGlue' :
  ∀{a}{Γ : Set a}
  (Φ : Γ → CofProp)
  (A : res Γ Φ → Set)
  (B : Γ → Set)
  (f : (xu : res Γ Φ) → A xu → B (xu .fst))
  → ---------------
  Γ → Set
SGlue' Φ A B f x = SGlue (Φ x) (λ u → A (x , u)) (B x) (λ u → f (x , u))

strictifyGlueIso' :
  ∀{a}{Γ : Set a}
  (Φ : Γ → CofProp)
  {A : res Γ Φ → Set}
  {B : Γ → Set}
  (f : (xu : res Γ Φ) → A xu → B (xu .fst))
  → ---------------
  SGlue' Φ A B f ≅' Glue' Φ A B f
strictifyGlueIso' Φ {A} {B} f x = strictifyGlueIso (Φ x) (λ u → f (x , u))

SGlueStrictness' :
  ∀{a}{Γ : Set a}
  (Φ : Γ → CofProp)
  {A : res Γ Φ → Set}
  {B : Γ → Set}
  (f : (xu : res Γ Φ) → A xu → B (xu .fst))
  → ---------------
  A ≡ SGlue' Φ A B f ∘ fst
SGlueStrictness' Φ {A} {B} f =
  funext λ {(x , u) → SGlueStrictness (Φ x) (λ u' → f (x , u')) u}

module Misaligned where

  abstract
    FibSGlueId :
      (Φ : Int → CofProp)
      {A : res Int Φ → Set}
      {B : Int → Set}
      (f : (xu : res Int Φ) → A xu → B (xu .fst))
      (equiv : Equiv' f)
      → ---------------
      isFib A → isFib B → isFib (SGlue' Φ A B f)
    FibSGlueId Φ {A} {B} f equiv α β =
      FibIso (SGlue' Φ A B f) (Glue' Φ A B f) (strictifyGlueIso' Φ f) (FibGlueId Φ f equiv α β)

  FibSGlue :
    ∀{a}{Γ : Set a}
    (Φ : Γ → CofProp)
    {A : res Γ Φ → Set}
    {B : Γ → Set}
    (f : (xu : res Γ Φ) → A xu → B (xu .fst))
    (equiv : Equiv' f)
    → ---------------
    isFib A → isFib B → isFib (SGlue' Φ A B f)
  FibSGlue {a} {Γ} Φ {A} {B} f equiv α β r p =
    FibSGlueId (Φ ∘ p)
      (f ∘ (p ×id))
      (equiv ∘ (p ×id))
      (reindex A α (p ×id))
      (reindex B β p)
      r
      id

  reindexFibSGlue :
    ∀ {ℓ} {Δ Γ : Set ℓ}
    (Φ : Γ → CofProp)
    {A : res Γ Φ → Set}
    {B : Γ → Set}
    (f : (xu : res Γ Φ) → A xu → B (xu .fst))
    (equiv : Equiv' f)
    (α : isFib A) (β : isFib B)
    (ρ : Δ → Γ)
    → reindex (SGlue' Φ A B f) (FibSGlue Φ f equiv α β) ρ
      ≡ FibSGlue (Φ ∘ ρ) (f ∘ (ρ ×id)) (equiv ∘ (ρ ×id)) (reindex A α (ρ ×id)) (reindex B β ρ)
  reindexFibSGlue Φ f equiv α β ρ = refl
