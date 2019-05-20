{-# OPTIONS --rewriting #-}
module Data.paths where

open import prelude
open import interval
open import cof
open import fibrations

----------------------------------------------------------------------
-- Path types
----------------------------------------------------------------------

enlargeSys : {A : Int → Set} (φ : Cof)
  (f : (t : Int) → [ φ ] → A t)
  (a₀ : A O [ φ ↦ f O ]) (a₁ : A I [ φ ↦ f I ])
  (t : Int) → [ φ ∨ t ≈O ∨ t ≈I ] → A t
enlargeSys φ f (a₀ , ex₀) (a₁ , ex₁) t =
  ∨-rec φ (t ≈O ∨ t ≈I)
    (f t)
    (OI-rec t (λ {refl → a₀}) (λ {refl → a₁}))
    (λ u →
      ∨-elimEq (t ≈O) (t ≈I)
        (λ {refl → ex₀ u})
        (λ {refl → ex₁ u}))

enlargedExtends : {A : Int → Int → Set} (φ : Cof)
  (f : (t : Int) → [ φ ∨ t ≈O ∨ t ≈I ] → (i : Int) → A t i)
  (r : Int) (a : (t : Int) → A t r)
  (pφ : (t : Int) → (λ u → f t ∣ inl u ∣ r) ↗ a t)
  (pO : f O ∣ inr ∣ inl refl ∣ ∣ r ≡ a O)
  (pI : f I ∣ inr ∣ inr refl ∣ ∣ r ≡ a I)
  (t : Int) → f t ◆ r ↗ a t
enlargedExtends φ f r a pφ pO pI t =
  ∨-elimEq φ (t ≈O ∨ t ≈I)
    (pφ t)
    (∨-elimEq (t ≈O) (t ≈I)
      (λ {refl → pO})
      (λ {refl → pI}))

Path : ∀{ℓ}{Γ : Set ℓ}(A : Γ → Set) → Σ x ∈ Γ , A x × A x → Set
Path A (x , (a , a')) = a ~ a'

FibPathId :
  {A : Int → Set}
  (α : isFib A)
  → -----------
  isFib (Path A)
FibPathId {A} α r p φ f (q , ex) =
  record
  { comp = λ s →
    ( path
      (λ j → compA j .comp s .fst)
      (symm (compA O .comp s .snd ∣ inr ∣ inl refl ∣ ∣))
      (symm (compA I .comp s .snd ∣ inr ∣ inr refl ∣ ∣))
    , λ u → PathExt (funext λ j → compA j .comp s .snd ∣ inl u ∣)
    )
  ; cap =
    ( path
      (λ k →
        path
          (λ j → compA j .cap .fst .at k)
          (symm (compA O .cap .snd k ∣ inr ∣ inl refl ∣ ∣))
          (symm (compA I .cap .snd k ∣ inr ∣ inr refl ∣ ∣)))
      (PathExt (funext λ j → compA j .cap .fst .atO))
      (PathExt (funext λ j → compA j .cap .fst .atI))
    , λ k u → PathExt (funext λ j → compA j .cap .snd k ∣ inl u ∣)
    )
  }
  where
  sysA : (j : Int) → [ φ ∨ j ≈O ∨ j ≈I ] → Π (λ i → A (p i .fst))
  sysA =
    enlargeSys φ
      (λ j u i → f u i .at j)
      ((λ i → p i .snd .fst) , λ u → funext (λ i → f u i .atO))
      ((λ i → p i .snd .snd) , λ u → funext (λ i → f u i .atI))

  module _ (j : Int) where

    baseA : A (p r .fst) [ (φ ∨ j ≈O ∨ j ≈I) ↦ (sysA j) ◆ r ]
    baseA =
      ( q .at j
      , enlargedExtends φ sysA r (q .at)
          (λ j u → cong (λ z → z .at j) (ex u))
          (symm (q .atO))
          (symm (q .atI))
          j
      )

    compA : WComp r (λ i → A (p i .fst)) (φ ∨ j ≈O ∨ j ≈I) (sysA j) baseA
    compA = α r (λ i → p i .fst) (φ ∨ j ≈O ∨ j ≈I) (sysA j) baseA

-- trick to get Agda to check reindexing stability quickly
private
  abstract
    FibPathId' = FibPathId

FibPath :
  ∀{ℓ}{Γ : Set ℓ}
  {A : Γ → Set}
  (α : isFib A)
  → -----------
  isFib (Path A)
FibPath {_} {Γ} {A} α e p = FibPathId' (reindex A α (fst ∘ p)) e (id× p) where
  id×_ : (p : Int → Σ Γ (λ x → A x × A x)) → Int → Σ Int (λ i → A (fst (p i)) × A (fst (p i)))
  (id× p) i = (i , snd (p i))

FibPath' :
  ∀{ℓ}{Γ : Set ℓ}
  (A : Fib Γ)
  → -----------
  Fib (Σ x ∈ Γ , fst A x × fst A x)
FibPath' (A , α) = (Path A , FibPath {A = A} α)

----------------------------------------------------------------------
-- Forming Path types is stable under reindexing
----------------------------------------------------------------------
reindexPath :
  ∀{ℓ ℓ'}{Δ : Set ℓ}{Γ : Set ℓ'}
  (A : Γ → Set)
  (α : isFib A)
  (ρ : Δ → Γ)
  → ----------------------
  reindex (Path A) (FibPath α) (ρ ×id) ≡ FibPath (reindex A α ρ)
reindexPath A α ρ = refl
