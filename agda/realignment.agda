{-

Realign a fibration structure.

-}
{-# OPTIONS --rewriting #-}
module realignment where 

open import prelude
open import interval
open import cof
open import fibrations

module Realign {ℓ}{Γ : Set ℓ}
  (Φ : Γ → Cof) (A : Γ → Set)
  (β : isFib {Γ = res Γ Φ} (A ∘ fst)) (α : isFib A)
  (r : Int) (p : Int → Γ) (ψ : Cof) (f : [ ψ ] → Π (A ∘ p))
  (a₀ : A (p r) [ ψ ↦ f ◆ r ])
  where
  wB : [ ∀I (Φ ∘ p) ] → WComp r (A ∘ p) ψ f a₀
  wB u = β r (λ i → p i , u i) ψ f a₀

  f' : [ ψ ∨ ∀I (Φ ∘ p) ] → (i : Int) → A (p i)
  f' =
    ∨-rec ψ (∀I (Φ ∘ p))
      f
      (λ u i → wB u .comp i .fst)
      (λ v u → funext λ i → wB u .comp i .snd v)

  a₀FixTube : [ ψ ∨ ∀I (Φ ∘ p) ] → Int → A (p r)
  a₀FixTube =
    ∨-rec ψ (∀I (Φ ∘ p))
      (λ v _ → f v r)
      (λ u j → wB u .cap .fst .at j)
      (λ v u → funext λ j → wB u .cap .snd j v)

  a₀FixBase : A (p r) [ ψ ∨ ∀I (Φ ∘ p) ↦ a₀FixTube ◆ I ]
  a₀FixBase =
    ( a₀ .fst
    , ∨-elimEq ψ (∀I (Φ ∘ p))
      (a₀ .snd)
      (λ u → wB u .cap .fst .atI)
    )

  a₀Fix = strictifyFib A α I (λ _ → p r) (ψ ∨ ∀I (Φ ∘ p)) a₀FixTube a₀FixBase

  a₀' : A (p r) [ ψ ∨ ∀I (Φ ∘ p) ↦ f' ◆ r ]
  a₀' =
    ( a₀Fix .comp O (I≡IsCof O) .fst
    , ∨-elimEq ψ (∀I (Φ ∘ p))
      (λ v → a₀Fix .comp O (I≡IsCof O) .snd ∣ inl v ∣)
      (λ u →
        trans
          (a₀Fix .comp O (I≡IsCof O) .snd ∣ inr u ∣)
          (symm (wB u .cap .fst .atO)))
    )

  wA = α r p (ψ ∨ ∀I (Φ ∘ p)) f' a₀'

  module _ (t : Int) where

    capTube : [ ψ ∨ ∀I (Φ ∘ p) ∨ t ≈O ∨ t ≈I ] → Int → A (p r)
    capTube =
      ∨-rec ψ (∀I (Φ ∘ p) ∨ t ≈O ∨ t ≈I)
        (λ v _ → f v r)
        (∨-rec (∀I (Φ ∘ p)) (t ≈O ∨ t ≈I)
          (λ u j → wB u .cap .fst .at t)
          (OI-rec t
            (λ {refl j → wA .cap .fst .at j})
            (λ {refl j → a₀ .fst}))
          (λ u → ∨-elimEq (t ≈O) (t ≈I)
            (λ {refl → funext λ j → trans (wA .cap .snd j ∣ inr u ∣) (wB u .cap .fst .atO)})
            (λ {refl → funext λ j → wB u .cap .fst .atI})))
        (λ v → ∨-elimEq (∀I (Φ ∘ p)) (t ≈O ∨ t ≈I)
          (λ u → funext λ _ → wB u .cap .snd t v)
          (∨-elimEq (t ≈O) (t ≈I)
            (λ {refl → funext λ j → wA .cap .snd j ∣ inl v ∣})
            (λ {refl → funext λ _ → a₀ .snd v})))

    capBase : A (p r) [ ψ ∨ ∀I (Φ ∘ p) ∨ t ≈O ∨ t ≈I ↦ capTube ◆ I ]
    capBase =
      ( a₀Fix .comp t (I≡IsCof t) .fst
      , ∨-elimEq ψ (∀I (Φ ∘ p) ∨ t ≈O ∨ t ≈I)
        (λ v → a₀Fix .comp t (I≡IsCof t) .snd ∣ inl v ∣)
        (∨-elimEq (∀I (Φ ∘ p)) (t ≈O ∨ t ≈I)
          (λ u → a₀Fix .comp t (I≡IsCof t) .snd ∣ inr u ∣)
          (∨-elimEq (t ≈O) (t ≈I)
            (λ {refl → wA .cap .fst .atI})
            (λ {refl → symm (a₀Fix .cap (I≡IsCof I))})))
      )

    capComp = α I (λ _ → p r) (ψ ∨ ∀I (Φ ∘ p) ∨ t ≈O ∨ t ≈I) capTube capBase .comp O

abstract
  realignId :
    (Φ : Int → Cof)
    (A : Int → Set)
    (β : isFib {Γ = res Int Φ} (A ∘ fst))
    (α : isFib A)
    → ---------------
    isFib A
  realignId Φ A β α r p ψ f a₀ =
    record
    { comp = λ s →
      ( wA .comp s .fst
      , λ v → wA .comp s .snd ∣ inl v ∣
      )
    ; cap =
      ( path
        (λ t → capComp t .fst)
        (trans
          (wA .cap .fst .atO)
          (symm (capComp O .snd ∣ inr ∣ inr ∣ inl refl ∣ ∣ ∣)))
        (symm (capComp I .snd ∣ inr ∣ inr ∣ inr refl ∣ ∣ ∣))
      , (λ t v → capComp t .snd ∣ inl v ∣)
      )
    }
    where
    open Realign Φ A β α r p ψ f a₀

  isRealignedId :
    (Φ : Int → Cof)
    (A : Int → Set)
    (β : isFib {Γ = res Int Φ} (A ∘ fst))
    (α : isFib A)
    → ---------------
    reindex A (realignId Φ A β α) fst ≡ β
  isRealignedId Φ A β α =
    fibExt {A = A ∘ fst} λ r p ψ f a₀ →
      let
        open Realign Φ A β α r (fst ∘ p) ψ f a₀
      in
      ( (λ s → symm (wA .comp s .snd ∣ inr (λ i → p i .snd) ∣))
      , λ t → symm (capComp t .snd ∣ inr ∣ inl (λ i → p i .snd) ∣ ∣)
      )

realign :
  ∀{ℓ}{Γ : Set ℓ}
  (Φ : Γ → Cof)
  (A : Γ → Set)
  (β : isFib {Γ = res Γ Φ} (A ∘ fst))
  (α : isFib A)
  → ---------------
  isFib A
realign Φ A β α r p =
  realignId (Φ ∘ p)
    (A ∘ p)
    (reindex (A ∘ fst) β (p ×id))
    (reindex A α p)
    r
    id

isRealigned :
  ∀{ℓ}{Γ : Set ℓ}
  (Φ : Γ → Cof)
  (A : Γ → Set)
  (β : isFib {Γ = res Γ Φ} (A ∘ fst))
  (α : isFib A)
  → ---------------
  reindex A (realign Φ A β α) fst ≡ β
isRealigned {ℓ} {Γ} Φ A β α =
  funext λ r → funext λ pu →
    let
      p = fst ∘ pu
    in
    appCong {x = λ i → (i , pu i .snd)}
      (appCong {x = r}
        (isRealignedId
          (Φ ∘ p)
          (A ∘ p)
          (reindex (A ∘ fst) β (p ×id))
          (reindex A α p)))

reindexRealign :
  ∀{ℓ ℓ'} {Δ : Set ℓ} {Γ : Set ℓ'}
  (Φ : Γ → Cof)
  (A : Γ → Set)
  (β : isFib {Γ = res Γ Φ} (A ∘ fst))
  (α : isFib A)
  (ρ : Δ → Γ)
  → ---------------
  reindex A (realign Φ A β α) ρ
  ≡ realign (Φ ∘ ρ) (A ∘ ρ) (reindex (A ∘ fst) β (ρ ×id)) (reindex A α ρ)
reindexRealign  Φ A β α ρ = refl
