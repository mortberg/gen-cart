{-# OPTIONS --rewriting #-}

open import prelude
open import interval
open import cof
open import fibrations
open import hcomp-coe

module retract where

homotopyRetractIsFib : ∀ {ℓ} {Γ : Set ℓ}
  (A B : Γ → Set) (α : isHFib A) (β : isFib B)
  (f : ∀ x → A x → B x) (g : ∀ x → B x → A x)
  (ret : ∀ x a → g x (f x a) ~ a)
  → isFib A
homotopyRetractIsFib A B α β f g ret r p φ h (a₀ , ext) =
  record
  { comp = λ s →
    ( mainComp s O (gCompBase s) .comp I (≡IIsCof O) .fst
    , λ u →
      trans
        (mainComp s O (gCompBase s) .comp I (≡IIsCof O) .snd u)
        (symm (ret (p s) (h u s) .atI))
    )
  ; cap =
    ( path
      (λ t → mainCap t .comp I .fst)
      (symm (mainCap O .comp I .snd ∣ inr ∣ inl refl ∣ ∣))
      (trans
        (trans
          (ret (p r) a₀ .atI)
          (mainComp r I (bRetBase I I) .cap (≡IIsCof I)))
        (symm (mainCap I .comp I .snd ∣ inr ∣ inr refl ∣ ∣)))
    , λ t u → mainCap t .comp I .snd ∣ inl u ∣
    )
  }
  where
  bTube : [ φ ] → (i : Int) → B (p i)
  bTube u i = f (p i) (h u i)

  bBase : B (p r) [ φ ↦ bTube ◆ r ]
  bBase = (f (p r) a₀ , λ u → cong (f (p r)) (ext u))

  bComp = β r p φ bTube bBase

  module _ (s : Int) where

    compTube : [ φ ] → (j : Int) → A (p s)
    compTube u = ret (p s) (h u s) .at

    gCompBase : A (p s) [ φ ↦ compTube ◆ O ]
    gCompBase =
      ( g (p s) (bComp .comp s .fst)
      , λ u →
        trans
          (cong (g (p s)) (bComp .comp s .snd u))
          (ret (p s) (h u s) .atO)
      )

    mainComp : (i : Int) → _
    mainComp i = strictifyHFib A α i (p s) φ compTube

  module _ (t : Int) where

    gCapBase : A (p r) [ φ ↦ compTube r ◆ O ]
    gCapBase =
      ( g (p r) (bComp .cap .fst .at t)
      , λ u →
        trans
          (cong (g (p r)) (bComp .cap .snd t u))
          (ret (p r) (h u r) .atO)
      )

    bRetBase : (k : Int) → A (p r) [ φ ↦ compTube r ◆ k ]
    bRetBase k =
      ( ret (p r) a₀ .at k
      , λ u → cong (λ a → ret (p r) a .at k) (ext u)
      )

    capTube : [ φ ∨ t ≈O ∨ t ≈I ] → Int → A (p r)
    capTube =
      ∨-rec φ (t ≈O ∨ t ≈I)
        (λ u _ → h u r)
        (OI-rec t
          (λ {refl k → mainComp r O (gCompBase r) .comp I (≡IIsCof O) .fst})
          (λ {refl k → mainComp r k (bRetBase k) .comp I (≡IIsCof k) .fst}))
        (λ u → ∨-elimEq (t ≈O) (t ≈I)
          (λ {refl → funext λ k →
            trans
              (mainComp r O (gCompBase r) .comp I (≡IIsCof O) .snd u)
              (symm (ret (p r) (h u r) .atI))})
          λ {refl → funext λ k →
            trans
              (mainComp r k (bRetBase k) .comp I (≡IIsCof k) .snd u)
              (symm (ret (p r) (h u r) .atI))})

    capBase : A (p r) [ φ ∨ t ≈O ∨ t ≈I ↦ capTube ◆ O ]
    capBase =
      ( mainComp r O gCapBase .comp I (≡IIsCof O) .fst
      , ∨-elimEq φ (t ≈O ∨ t ≈I)
        (λ u →
          trans
            (mainComp r O gCapBase .comp I (≡IIsCof O) .snd u)
            (symm (ret (p r) (h u r) .atI)))
        (OI-elim t _
          (λ {refl →
            cong (λ base → mainComp r O base .comp I (≡IIsCof O) .fst)
              (Σext
                (cong (g (p r)) (symm (bComp .cap .fst .atO)))
                (funext λ _ → uipImp))})
          λ {refl →
            cong (λ base → mainComp r O base .comp I (≡IIsCof O) .fst)
              (Σext
                (trans
                  (cong (g (p r)) (symm (bComp .cap .fst .atI)))
                  (ret (p r) a₀ .atO))
                (funext λ _ → uipImp))})
      )

    mainCap = α O (p r) (φ ∨ t ≈O ∨ t ≈I) capTube capBase
