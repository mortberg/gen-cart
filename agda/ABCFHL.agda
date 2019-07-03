{-

Proof that ABCFHL fibrations as defined in

  https://github.com/dlicata335/cart-cube

are equivalent to weak fibrations when the diagonal is a cofibration.

We also prove that ABCFHL fibrations are equivalent to the variation
in

  https://github.com/riaqn/orton/blob/master/src/fibrations.agda

This correspond to the "unbiased fibrations" of

  https://github.com/awodey/math/tree/master/QMS

-}
{-# OPTIONS --rewriting #-}
module ABCFHL where

open import prelude
open import interval
open import cofprop
open import fibrations

-- Assume that r≡s is a cofibration
postulate
  diagCof : (r s : Int) → CofProp
  [diagCof] : (r s : Int) → [ diagCof r s ] ≡ (r ≡ s)

  {-# REWRITE [diagCof] #-}

diagIsCofProp : (r s : Int) → isCofProp (r ≡ s)
diagIsCofProp r s = (diagCof r s , id , id)

-- ABCFHL fibrations
record ABCFHLComp (r : Int) (A : Int → Set) (φ : CofProp) (f : [ φ ] → Π A)
  (x₀ : A r [ φ ↦ f ◆ r ]) : Set
  where
  field
    comp : (s : Int) → A s [ φ ↦ f ◆ s ]
    cap : comp r .fst ≡ x₀ .fst

open ABCFHLComp public

isABCFHLFib : ∀ {ℓ} {Γ : Set ℓ} (A : Γ → Set) → Set ℓ
isABCFHLFib {Γ = Γ} A = ∀ r p φ f x₀ → ABCFHLComp r (A ∘ p) φ f x₀

isFib→isABCFHLFib : ∀ {ℓ} {Γ : Set ℓ} (A : Γ → Set) → isFib A → isABCFHLFib A
isFib→isABCFHLFib A α r p ϕ f x₀ = record
  { comp = λ s → strictifyFib A α r p ϕ f x₀ .comp s (diagIsCofProp r s)
  ; cap  = strictifyFib A α r p ϕ f x₀ .cap (diagIsCofProp r r)
  }

isABCFHLFib→isFib : ∀ {ℓ} {Γ : Set ℓ} (A : Γ → Set) → isABCFHLFib A → isFib A
isABCFHLFib→isFib A α r p ϕ f x₀ = record
  { comp = α r p ϕ f x₀ .comp
  ; cap  = path (λ i → x₀ .fst) (symm (α r p ϕ f x₀ .cap)) refl
         , λ _ → x₀ .snd
  }

-- Proof that ABCFHL fibrations are equivalent to the notion of fibration in
-- https://github.com/riaqn/orton/blob/master/src/fibrations.agda
private
  Comp : (Int → Set) → Set
  Comp A = (φ : CofProp) (f : [ φ ] → Π A) → (e₀ e₁ : Int)
           (h₀ : A e₀ [ φ ↦ f ◆ e₀ ])
           → A e₁ [ φ ↦ f ◆ e₁ ]

  -- This definition of the cap condition is a bit messy to work with
  -- compared to ABCFHL fibrations as it involves equality in a Σ-type
  Reduce : {A : Int → Set} → (c : Comp A) → Set
  Reduce {A = A} c = (φ : CofProp) (f : [ φ ] → Π A) (e : Int) →
                     (h : A e [ φ ↦ f ◆ e ]) →
                     c φ f e e h ≡ h

  isFib' : ∀{a} {Γ : Set a} (A : Γ → Set) → Set a
  isFib' {a = a} {Γ = Γ} A = (p : Int → Γ) → Σ c ∈ Comp (A ∘ p) , Reduce c

  isABCFHLFib→isFib' : ∀ {ℓ} {Γ : Set ℓ} (A : Γ → Set) → isABCFHLFib A → isFib' A
  isABCFHLFib→isFib' A α p = (λ ϕ f r s x₀ → α r p ϕ f x₀ .comp s)
                            , λ ϕ f r x₀ → Σext (α r p ϕ f x₀ .cap) (funext (λ _ → uipImp))

  isFib'→isABCFHLFib : ∀ {ℓ} {Γ : Set ℓ} (A : Γ → Set) → isFib' A → isABCFHLFib A
  isFib'→isABCFHLFib A c r p ϕ f x₀ = record
    { comp = λ s → c p .fst ϕ f r s x₀
    ; cap  = cong fst (c p .snd ϕ f r x₀)
    }
