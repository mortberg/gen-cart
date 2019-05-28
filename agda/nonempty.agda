{-# OPTIONS --rewriting #-}
module nonempty where

open import prelude
open import interval
open import cofprop
open import fibrations
open import hcomp-coe

-- homogeneous composition for non-empty systems
isRestrictedHFib : ∀ {ℓ} {Γ : Set ℓ} (A : Γ → Set) → Set ℓ
isRestrictedHFib {Γ = Γ} A = (r : Int) (x : Γ)
  (φ : CofProp) (_ : ¬ ¬ [ φ ]) (f : [ φ ] → Int → A x)
  (a₀ : A x [ φ ↦ f ◆ r ])
  → WComp r (λ _ → A x) φ f a₀

RestrictedHFib : ∀{ℓ}(Γ : Set ℓ) → Set (lsuc lzero ⊔ ℓ)
RestrictedHFib Γ = Σ (Γ → Set) isRestrictedHFib

postulate
  ~ : CofProp → CofProp
  explode : ∀ φ → [ φ ] → [ ~ φ ] → ∅
  ¬¬LEM : ∀ φ → ¬ ¬ [ φ ∨ ~ φ ]

isRestrictedHFib→isHFib : ∀ {ℓ} {Γ : Set ℓ} (A : Γ → Set)
  → isRestrictedHFib A → isHFib A
isRestrictedHFib→isHFib A α r x φ f a₀ =
  record
  { comp = λ s → (fixed .comp s .fst , λ u → fixed .comp s .snd ∣ inl u ∣)
  ; cap =
    ( fixed .cap .fst
    , λ t u → fixed .cap .snd t ∣ inl u ∣
    )
  }
  where
  tube : [ φ ∨ ~ φ ] → Int → A x
  tube =
    ∨-rec φ (~ φ)
      f
      (λ _ _ → a₀ .fst)
      (λ u ~u → ∅-rec (explode φ u ~u))

  base : A x [ φ ∨ ~ φ ↦ tube ◆ r ]
  base =
    ( a₀ .fst
    , ∨-elim φ (~ φ) _
      (a₀ .snd)
      (λ _ → refl)
      (λ _ _ → uipImp)
    )

  fixed = α r x (φ ∨ ~ φ) (¬¬LEM φ) tube base
