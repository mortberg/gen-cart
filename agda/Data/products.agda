{-

Fibrancy of Σ-types.

-}
{-# OPTIONS --rewriting #-}
module Data.products where

open import prelude
open import interval
open import cofprop
open import fibrations
open import Data.paths

----------------------------------------------------------------------
-- Dependent products
----------------------------------------------------------------------

Σ' : ∀{a}{Γ : Set a}(A : Γ → Set)(B : (Σ x ∈ Γ , A x) → Set) → Γ → Set
Σ' A B x = Σ a ∈ A x , B (x , a)

FibΣid :
  {A : Int → Set}
  {B : (Σ x ∈ Int , A x) → Set}
  (α : isFib A)
  (β : isFib B)
  → -----------
  isFib (Σ' A B)
FibΣid {A} {B} α β r p φ f ((a₀ , b₀) , ex₀) =
  record
  { comp = λ s →
    ( (wA .comp s .fst , wB .comp s .fst)
    , λ u → Σext (wA .comp s .snd u) (wB .comp s .snd u)
    )
  ; cap =
    ( path
      (λ t → (wA .cap .fst .at t , c t .fst))
      (Σext (wA .cap .fst .atO)
        (trans
          (wB .cap .fst .atO)
          (adjustSubstEq (λ a → B (p r , a))
            refl (symm (wA .cap .fst .atO))
            (wA .cap .fst .atO) refl
            (symm (c O .snd ∣ inr ∣ inl refl ∣ ∣)))))
      (Σext (wA .cap .fst .atI)
        (adjustSubstEq (λ a → B (p r , a))
          refl (symm (wA .cap .fst .atI))
          (wA .cap .fst .atI) refl
          (symm (c I .snd ∣ inr ∣ inr refl ∣ ∣))))
    , λ t u →
      Σext (wA .cap .snd t u) (c t .snd ∣ inl u ∣)
    )
  }
  where
  fA : [ φ ] → Π (A ∘ p)
  fA u i = f u i .fst

  wA = α r p φ fA (a₀ , λ u → Σeq₁ (ex₀ u))

  pcomp : Int → (Σ x ∈ Int , A x)
  pcomp i = (p i , wA .comp i .fst)

  pcap : Int → (Σ x ∈ Int , A x)
  pcap i = (p r , wA .cap .fst .at i)

  fB : [ φ ] → Π (B ∘ pcomp)
  fB u i = subst (λ a → B (p i , a)) (wA .comp i .snd u) (snd (f u i))

  b₀FixTube : [ φ ] → (i : Int) → B (pcap i)
  b₀FixTube u i = subst (λ a → B (p r , a)) (wA .cap .snd i u) (snd (f u r))

  b₀FixBase : B (pcap I) [ φ ↦ b₀FixTube ◆ I ]
  b₀FixBase =
    ( subst (λ a → B (p r , a)) (symm (wA .cap .fst .atI)) b₀
    , λ u → 
      adjustSubstEq (λ a → B (p r , a))
        (Σeq₁ (ex₀ u)) refl
        (wA .cap .snd I u) (symm (wA .cap .fst .atI))
        (Σeq₂ (ex₀ u))
    )

  b₀Fix : SComp I (B ∘ pcap) φ b₀FixTube b₀FixBase
  b₀Fix =
    strictifyFib B β I pcap φ
      b₀FixTube
      b₀FixBase

  b₀Fixed : B (pcomp r) [ φ ↦ fB ◆ r ]
  b₀Fixed =
    ( subst (λ a → B (p r , a)) (wA .cap .fst .atO)
        (b₀Fix .comp O (I≡IsCofProp O) .fst)
    , λ u →
      adjustSubstEq (λ a → B (p r , a))
        (wA .cap .snd O u) refl
        (wA .comp r .snd u) (wA .cap .fst .atO)
        (b₀Fix .comp O (I≡IsCofProp O) .snd u)
    )

  wB : WComp r (B ∘ pcomp) φ fB b₀Fixed
  wB = β r pcomp φ fB b₀Fixed

  -- defining the system for the final composition

  csysO : Int → B (pcap O)
  csysO j =
    subst (λ a → B (p r , a)) (symm (wA .cap .fst .atO)) (wB .cap .fst .at j)

  csysI : Int → B (pcap I)
  csysI j = subst (λ a → B (p r , a)) (symm (wA .cap .fst .atI)) b₀

  module _ (u : [ φ ]) where

    csysOCompat : (j : Int) → b₀FixTube u O ≡ csysO j
    csysOCompat j =
      adjustSubstEq (λ a → B (p r , a))
        (wA .comp r .snd u) refl
        (wA .cap .snd O u) (symm (wA .cap .fst .atO))
        (wB .cap .snd j u)

    csysICompat : (j : Int) → b₀FixTube u I ≡ csysI j
    csysICompat j =
      adjustSubstEq (λ a → B (p r , a))
        (Σeq₁ (ex₀ u)) refl
        (wA .cap .snd I u) (symm (wA .cap .fst .atI))
        (Σeq₂ (ex₀ u))

  csys : (t : Int) → [ φ ∨ t ≈O ∨ t ≈I ] → Int → B (pcap t)
  csys =
    enlargeSys φ
      (λ t u _ → b₀FixTube u t)
      (csysO , λ u → funext (csysOCompat u))
      (csysI , λ u → funext (csysICompat u))

  c : (t : Int) → B (pcap t) [ φ ∨ t ≈O ∨ t ≈I ↦ csys t ◆ O ]
  c t =
    β I (λ _ → pcap t) (φ ∨ t ≈O ∨ t ≈I) (csys t)
      ( b₀Fix .comp t (I≡IsCofProp t) .fst
      , enlargedExtends φ csys I (λ t → b₀Fix .comp t (I≡IsCofProp t) .fst)
          (λ t → b₀Fix .comp t (I≡IsCofProp t) .snd)
          (adjustSubstEq (λ a → B (p r , a))
            refl (wA .cap .fst .atO)
            (symm (wA .cap .fst .atO)) refl
            (wB .cap .fst .atI))
          (adjustSubstEq (λ a → B (p r , a))
            (symm (wA .cap .fst .atI)) refl
            (symm (wA .cap .fst .atI)) refl
            (symm (b₀Fix .cap (I≡IsCofProp I))))
          t
      )
      .comp O

-- trick to get Agda to check reindexing stability quickly
private
  abstract
    FibΣidAbstract = FibΣid

FibΣ : ∀ {ℓ}
  {Γ : Set ℓ}
  {A : Γ → Set}
  {B : (Σ x ∈ Γ , A x) → Set}
  (α : isFib A)
  (β : isFib B)
  → -----------
  isFib (Σ' A B)
FibΣ {Γ = Γ} {A} {B} α β r p =
  FibΣidAbstract (reindex A α p) (reindex B β (p ×id)) r id

FibΣ' :
  {Γ : Set}
   (A : Fib Γ)
  (B : Fib (Σ x ∈ Γ , fst A x))
  → -----------
  Fib Γ
FibΣ' (A , α) (B , β) = Σ' A B , FibΣ {A = A} {B = B} α β

----------------------------------------------------------------------
-- Forming Σ-types is stable under reindexing
----------------------------------------------------------------------
reindexΣ :
  {Δ Γ : Set}
  (A : Γ → Set)
  (B : Σ Γ A → Set)
  (α : isFib A)
  (β : isFib B)
  (ρ : Δ → Γ)
  → ----------------------
  reindex (Σ' A B) (FibΣ {B = B} α β) ρ ≡ FibΣ {B = B ∘ (ρ ×id)} (reindex A α ρ) (reindex B β (ρ ×id))
reindexΣ A B α β ρ = refl
