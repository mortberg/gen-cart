{-

Equivalent definition of isFib due to Dan Licata

  A : I → Set has weak Kan composition iff
  Π r:I, the map (λ f → f r) : (Π (x : I) → A x) → (A r) is an equivalence

-}
{-# OPTIONS --rewriting #-}
module equivscontrfib where

open import prelude
open import interval
open import cofprop
open import fibrations
open import equivs using (SContr ; Fiber ; FiberExt ; EquivSContr)

isEquivSContrFib : ∀ {ℓ} {Γ : Set ℓ} (A : Γ → Set) → Set ℓ
isEquivSContrFib {Γ = Γ} A =
  (r : Int) (p : Int → Γ) → EquivSContr (λ (f : (i : Int) → A (p i)) → f r)

isEquivSContrFib→isFib : (A : Int → Set) (h : isEquivSContrFib A) → isFib A
isEquivSContrFib→isFib A h r p φ f x₀ = record
  { comp = λ s → fib1 .fst s
         , λ u → appCong (cong fst (fib .snd u))
  ; cap  = fib1 .snd
         , λ k u → trans (cong (λ w → w .snd .at k) (fib .snd u)) (symm (eqToPathAtO (x₀ .snd u) k)) }
  where
  fib : Fiber (λ f → f r) (x₀ .fst) [ φ ↦ (λ x → (f x , eqToPath (x₀ .snd x))) ]
  fib = h r p (x₀ .fst) φ (λ x → (f x , eqToPath (x₀ .snd x)))

  fib1 : Fiber (λ f → f r) (x₀ .fst)
  fib1 = fib .fst

isFib→isEquivSContrFib : ∀ {ℓ} {Γ : Set ℓ} (A : Γ → Set) (α : isFib A) → isEquivSContrFib A
isFib→isEquivSContrFib A α r p a₀ φ t =
  ( ( (λ i → f+ .comp i .fst)
    , path
      (λ s → q+ s .fst)
      (trans
        (f+ .cap .fst .atO)
        (symm (q+ O .snd ∣ inr ∣ inl refl ∣ ∣)))
      (symm (q+ I .snd ∣ inr ∣ inr refl ∣ ∣))
    )
  , λ u →
    FiberExt
      (funext λ i → f+ .comp i .snd u)
      (funext λ s → q+ s .snd ∣ inl u ∣)
  )
  where
  f : [ φ ] → Π (A ∘ p)
  f u = t u .fst

  q : (u : [ φ ]) → f u r ~ a₀
  q u = t u .snd

  a₀Fix =
    strictifyFib A α I (λ _ → p r) φ (λ u → q u .at) (a₀ , λ u → q u .atI)

  f+ = α r p φ f
    ( a₀Fix .comp O (I≡IsCofProp O) .fst
    , λ u →
      trans
        (a₀Fix .comp O (I≡IsCofProp O) .snd u)
        (symm (q u .atO)))

  module _ (s : Int) where
    q+Tube : [ φ ∨ s ≈O ∨ s ≈I ] → Int → A (p r)
    q+Tube =
      ∨-rec φ (s ≈O ∨ s ≈I)
        (λ u _ → q u .at s)
        (OI-rec s
          (λ {refl j → f+ .cap .fst .at j})
          (λ {refl _ → a₀}))
        (λ u → ∨-elimEq (s ≈O) (s ≈I)
          (λ {refl → funext λ j →
            trans (f+ .cap .snd j u) (t u .snd .atO)})
          (λ {refl → funext λ j → t u .snd .atI}))

    q+Base : A (p r) [ φ ∨ s ≈O ∨ s ≈I ↦ q+Tube ◆ I ]
    q+Base =
      ( a₀Fix .comp s (I≡IsCofProp s) .fst
      , ∨-elimEq φ (s ≈O ∨ s ≈I)
        (λ u → a₀Fix .comp s (I≡IsCofProp s) .snd u)
        (∨-elimEq (s ≈O) (s ≈I)
          (λ {refl → f+ .cap .fst .atI})
          λ {refl → symm (a₀Fix .cap (I≡IsCofProp I))})
      )

    q+ = α I (λ _ → p r) (φ ∨ s ≈O ∨ s ≈I) q+Tube q+Base .comp O
