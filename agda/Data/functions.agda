{-

Fibrancy of Π-types.

-}
{-# OPTIONS --rewriting #-}
module Data.functions where

open import prelude
open import interval
open import cofprop
open import fibrations
open import Data.paths

----------------------------------------------------------------------
-- Dependent functions
----------------------------------------------------------------------
Π' : ∀{a}{Γ : Set a}(A : Γ → Set)(B : (Σ x ∈ Γ , A x) → Set) → Γ → Set
Π' A B x = (a : A x) → B (x , a)

FibΠid :
  {A : Int → Set}
  {B : (Σ x ∈ Int , A x) → Set}
  (α : isFib A)
  (β : isFib B)
  → -----------
  isFib (Π' A B)
FibΠid {A} {B} α β r p φ f (g , ex) =
  record
  { comp = λ s →
    ( (λ a →
      let open Comp s a
      in
      subst (λ a → B (p s , a))
        (wA .cap .fst .atI)
        (fix O compUnfixed .comp I (≡IIsCofProp O) .fst)
      )
    , λ u → funext λ a →
      let open Comp s a
      in
      adjustSubstEq (λ a → B (p s , a))
        (symm (wA .cap .fst .atI)) refl
        refl (wA .cap .fst .atI)
        (trans
          (fix O compUnfixed .comp I (≡IIsCofProp O) .snd u)
          (congdep (f u s) (symm (wA .cap .fst .atI))))
    )
  ; cap =
    ( path
      (λ t a → fixCap a t .fst)
      (funext λ a →
        let open Comp r a in
        trans
          (cong
            (λ b → subst (λ a → B (p r , a)) (wA .cap .fst .atI) (fix O b .comp I (≡IIsCofProp O) .fst))
            (Σext
              (cong (subst (λ a → B (p r , a)) (symm (wA .cap .fst .atO)))
                (wB .cap .fst .atO))
              (funext λ _ → uipImp)))
          (symm (fixCap a O .snd ∣ inr ∣ inl refl ∣ ∣)))
      (funext λ a →
        symm (fixCap a I .snd ∣ inr ∣ inr refl ∣ ∣))
    , λ t u → funext λ a →
      fixCap a t .snd ∣ inl u ∣
    )
  }
  where
  module Comp (s : Int) (a : A (p s)) where

      wA = α s p ⊥ O≠I (a , λ u → O≠I u)

      wBTube : [ φ ] → (i : Int) → B (p i , wA .comp i .fst)
      wBTube u i = f u i (wA .comp i .fst)

      wBBase : B (p r , wA .comp r .fst) [ φ ↦ wBTube ◆ r ]
      wBBase =
        ( g (wA .comp r .fst)
        , λ u → cong (λ h → h (wA .comp r .fst)) (ex u)
        )

      wB = β r (λ i → (p i , wA .comp i .fst)) φ wBTube wBBase

      fixTube : [ φ ] → (j : Int) → B (p s , wA .cap .fst .at j)
      fixTube u j = f u s (wA .cap .fst .at j)

      fix : ∀ k y → SComp k (λ j → B (p s , wA .cap .fst .at j)) φ fixTube y
      fix k = strictifyFib B β k (λ j → (p s , wA .cap .fst .at j)) φ fixTube

      compUnfixed : B (p s , wA .cap .fst .at O) [ φ ↦ fixTube ◆ O ]
      compUnfixed =
        ( subst (λ a → B (p s , a)) (symm (wA .cap .fst .atO)) (wB .comp s .fst)
        , λ u →
          adjustSubstEq (λ a → B (p s , a))
            (wA .cap .fst .atO) refl
            refl (symm (wA .cap .fst .atO))
            (trans (wB .comp s .snd u) (congdep (f u s) (wA .cap .fst .atO)))
        )

  module _ (a : A (p r)) where

    open Comp r a

    capUnfixedO : Int → B (p r , wA .cap .fst .at O) [ φ ↦ fixTube ◆ O ]
    capUnfixedO j =
      ( subst (λ a → B (p r , a)) (symm (wA .cap .fst .atO)) (wB .cap .fst .at j)
      , λ u →
        adjustSubstEq (λ a → B (p r , a))
          (wA .cap .fst .atO) refl
          refl (symm (wA .cap .fst .atO))
          (trans (wB .cap .snd j u) (congdep (f u r) (wA .cap .fst .atO)))
      )

    fixCapTube : (t : Int) → [ φ ∨ t ≈O ∨ t ≈I ] → Int → B (p r , a)
    fixCapTube =
      enlargeSys φ
        (λ t u _ → f u r a)
        ( (λ j →
            subst (λ a → B (p r , a))
              (wA .cap .fst .atI)
              (fix O (capUnfixedO j) .comp I (≡IIsCofProp O) .fst))
        , λ u → funext λ j →
          adjustSubstEq (λ a → B (p r , a))
            (symm (wA .cap .fst .atI)) refl
            refl (wA .cap .fst .atI)
            (trans
              (fix O (capUnfixedO j) .comp I (≡IIsCofProp O) .snd u)
              (congdep (f u r) (symm (wA .cap .fst .atI))))
        )
        ( (λ _ → g a)
        , λ u → funext λ _ → cong (λ h → h a) (ex u)
        )

    capUnfixedBase : (t : Int) → B (p r , wA .cap .fst .at t) [ φ ↦ fixTube ◆ t ]
    capUnfixedBase t =
      ( g (wA .cap .fst .at t)
      , λ u → cong (λ h → h (wA .cap .fst .at t)) (ex u)
      )

    fixCapBase : (t : Int)
      → B (p r , a) [ φ ∨ t ≈O ∨ t ≈I ↦ fixCapTube t ◆ I ]
    fixCapBase t =
      ( elem t
      , enlargedExtends φ fixCapTube I elem
          (λ t u →
            adjustSubstEq (λ a → B (p r , a))
              (symm (wA .cap .fst .atI)) refl
              refl (wA .cap .fst .atI)
              (trans
                (fix t (capUnfixedBase t) .comp I (≡IIsCofProp t) .snd u)
                (congdep (f u r) (symm (wA .cap .fst .atI)))))
          (cong
            (λ b → subst (λ a → B (p r , a)) (wA .cap .fst .atI) (fix O b .comp I (≡IIsCofProp O) .fst))
            (Σext
              (adjustSubstEq (λ a → B (p r , a))
                refl (wA .cap .fst .atO)
                (symm (wA .cap .fst .atO)) refl
                (trans (symm (congdep g (wA .cap .fst .atO))) (wB .cap .fst .atI)))
              (funext λ _ → uipImp)))
          (adjustSubstEq (λ a → B (p r , a))
            (symm (wA .cap .fst .atI)) refl
            refl (wA .cap .fst .atI)
            (trans
              (symm (fix I (capUnfixedBase I) .cap (≡IIsCofProp I)))
              (congdep g (symm (wA .cap .fst .atI)))))
          t
      )
      where
      elem : (t : Int) → B (p r , a)
      elem t =
        subst (λ a → B (p r , a))
          (wA .cap .fst .atI)
          (fix t (capUnfixedBase t) .comp I (≡IIsCofProp t) .fst)

    fixCap : (t : Int) → B (p r , a) [ φ ∨ t ≈O ∨ t ≈I ↦ fixCapTube t ◆ O ]
    fixCap t =
      β I (λ _ → (p r , a)) (φ ∨ t ≈O ∨ t ≈I) (fixCapTube t) (fixCapBase t) .comp O

-- trick to get Agda to check reindexing stability quickly
private
  abstract
    FibΠid' = FibΠid

FibΠ :
  ∀{a}{Γ : Set a}
  {A : Γ → Set}
  {B : (Σ x ∈ Γ , A x) → Set}
  (α : isFib A)
  (β : isFib B)
  → -----------
  isFib (Π' A B)
FibΠ {_} {Γ} {A} {B} α β e p = FibΠid' (reindex A α p) (reindex B β (p ×id)) e id

FibΠ' :
  {Γ : Set}
  (A : Fib Γ)
  (B : Fib (Σ x ∈ Γ , fst A x))
  → -----------
  Fib Γ
FibΠ' (A , α) (B , β) = (Π' A B , FibΠ {A = A} {B = B} α β)

----------------------------------------------------------------------
-- Forming Π-types is stable under reindexing
----------------------------------------------------------------------
reindexΠ :
  ∀{a b}{Δ : Set a}{Γ : Set b}
  (A : Γ → Set)
  (B : Σ Γ A → Set)
  (α : isFib A)
  (β : isFib B)
  (ρ : Δ → Γ)
  → ----------------------
  reindex (Π' A B) (FibΠ {B = B} α β) ρ ≡ FibΠ {B = B ∘ (ρ ×id)} (reindex A α ρ) (reindex B β (ρ ×id))
reindexΠ A B α β ρ = refl
