{-

Definition of weak homogeneous composition and coercion. Proof that
these imply weak composition.

-}
{-# OPTIONS --rewriting #-}
module hcomp-coe where

open import prelude
open import interval
open import cof
open import fibrations

isHFib : ∀ {ℓ} {Γ : Set ℓ} (A : Γ → Set) → Set ℓ
isHFib {Γ = Γ} A = ∀ r x φ f a₀ → WComp r (λ _ → A x) φ f a₀

record WCoe (r : Int) (A : Int → Set) (a₀ : A r) : Set
  where
  field
    comp : (s : Int) → A s
    cap : comp r ~ a₀

open WCoe public

isCoeFib : ∀ {ℓ} {Γ : Set ℓ} (A : Γ → Set) → Set ℓ
isCoeFib A = ∀ r p a₀ → WCoe r (A ∘ p) a₀

----------------------------------------------------------------------
-- Strict homogeneous composition
----------------------------------------------------------------------

isSHFib : ∀ {ℓ} {Γ : Set ℓ} (A : Γ → Set) → Set ℓ
isSHFib {Γ = Γ} A = ∀ r x φ f a₀ → SComp r (λ _ → A x) φ f a₀

strictifyHFib : ∀{a}{Γ : Set a}(A : Γ → Set) → isHFib A → isSHFib A
strictifyHFib A α r y φ f x₀ =
  strictifyFib {Γ = Unit}
    (λ _ → A y)
    (λ r _ φ f x₀ → α r _ φ f x₀)
    r _ φ f x₀

----------------------------------------------------------------------
-- We can derive a fibration structure from homogeneous composition + coercion 
----------------------------------------------------------------------

H+Coe→Fib : ∀ {ℓ} {Γ : Set ℓ} (A : Γ → Set) → isHFib A → isCoeFib A → isFib A
H+Coe→Fib A η κ r p φ f a₀ = record
  { comp = λ s →
    ( fixedComp s .fst
    , λ u → trans (fixedComp s .snd u) (symm (κ s p (f u s) .cap .atI))
    )
  ; cap =
    ( path
      (λ t → fixedCap t .fst)
      (symm (fixedCap O .snd ∣ inr ∣ inl refl ∣ ∣))
      (trans
        (trans
          (κ r p (a₀ .fst) .cap .atI)
          (d I .cap (≡IIsCof I)))
        (symm (fixedCap I .snd ∣ inr ∣ inr refl ∣ ∣)))
    , λ t u → fixedCap t .snd ∣ inl u ∣
    )
  }
  where
  strictη = strictifyHFib A η

  module _ (k : Int) where

    capTube : [ φ ] → Int → A (p k)
    capTube u j = κ k p (f u k) .cap .at j

  module _ (s : Int) where

    compTube : [ φ ] → Int → A (p s)
    compTube u i = κ i p (f u i) .comp s

    compBase : A (p s) [ φ ↦ compTube ◆ r ]
    compBase =
      ( κ r p (a₀ .fst) .comp s
      , λ u → cong (λ a → κ r p a .comp s) (a₀ .snd u)
      )

    h = η r (p s) φ compTube compBase

    fixedBase : A (p s) [ φ ↦ capTube s ◆ O ]
    fixedBase =
      ( h .comp s .fst
      , λ u → trans (h .comp s .snd u) (κ s p (f u s) .cap .atO)
      )

    fixedComp = strictη O (p s) φ (capTube s) fixedBase .comp I (≡IIsCof O)

  module _ (k : Int) where

    dBase : A (p r) [ φ ↦ capTube r ◆ k ]
    dBase =
      ( κ r p (a₀ .fst) .cap .at k
      , λ u → cong (λ a → κ r p a .cap .at k) (a₀ .snd u)
      )

    d = strictη k (p r) φ (capTube r) dBase

  module _ (t : Int) where

    cBase : A (p r) [ φ ↦ capTube r ◆ O ]
    cBase =
      ( h r .cap .fst .at t
      , λ u → trans (h r .cap .snd t u) (κ r p (f u r) .cap .atO)
      )

    c = strictη O (p r) φ (capTube r) cBase .comp I (≡IIsCof O)

    fixedCapTube : [ φ ∨ t ≈O ∨ t ≈I ] → Int → A (p r)
    fixedCapTube =
      ∨-rec φ (t ≈O ∨ t ≈I)
        (λ u _ → f u r)
        (OI-rec t
          (λ {refl k → fixedComp r .fst})
          (λ {refl k → d k .comp I (≡IIsCof k) .fst}))
        (λ u → ∨-elimEq (t ≈O) (t ≈I)
          (λ {refl → funext λ k →
            trans (fixedComp r .snd u) (symm (κ r p (f u r) .cap .atI))})
          (λ {refl → funext λ k →
            trans (d k .comp I (≡IIsCof k) .snd u) (symm (κ r p (f u r) .cap .atI))}))

    fixedCapBase : A (p r) [ φ ∨ t ≈O ∨ t ≈I ↦ fixedCapTube ◆ O ]
    fixedCapBase =
      ( c .fst
      , ∨-elimEq φ (t ≈O ∨ t ≈I)
        (λ u → trans (c .snd u) (symm (κ r p (f u r) .cap .atI)))
        (∨-elimEq (t ≈O) (t ≈I)
          (λ {refl →
            cong (λ a → strictη O (p r) φ (capTube r) a .comp I (≡IIsCof O) .fst)
              (Σext (symm (h r .cap .fst .atO)) (funext λ _ → uipImp))})
          (λ {refl →
            cong (λ a → strictη O (p r) φ (capTube r) a .comp I (≡IIsCof O) .fst)
              (Σext
                (trans (symm (h r .cap .fst .atI)) (κ r p (a₀ .fst) .cap .atO))
                (funext λ _ → uipImp))}))
      )

    fixedCap = η O (p r) (φ ∨ t ≈O ∨ t ≈I) fixedCapTube fixedCapBase .comp I


------------------------------
-- More lemmas about isHFib --
------------------------------

-- A constant type with homogeneous fibration structure is fibrant
constHFib→isFib : ∀ {ℓ} {Γ : Set ℓ} (A : Set) → isHFib {Γ = Γ} (λ _ → A) → isFib {Γ = Γ} (λ _ → A)
constHFib→isFib A h r p φ f x₀ = record
  { comp = λ s → h r (p r) φ f x₀ .comp s
  ; cap  = h r (p r) φ f x₀ .cap }

-- Types with decidable equality has a homogeneous fibration structure
decEq→isHFib : ∀ {ℓ} {Γ : Set ℓ} (A : Γ → Set) (dec : {γ : Γ} (x y : A γ) → (x ≡ y) ⊎ (x ≡ y → ∅)) → isHFib A
decEq→isHFib {Γ = Γ} A dec r x φ f a₀ = record
  { comp = λ s → a₀ .fst , λ u → trans (a₀ .snd u) (constant (f u) s r)
  ; cap  = refl~ _ , λ _ → a₀ .snd }
   where
   constant : ∀ {γ : Γ} (t : Int → A γ) (r s : Int) → t r ≡ t s
   constant t r s = cntd (λ i → t r ≡ t i) (λ i → dec (t r) (t i)) r s refl
