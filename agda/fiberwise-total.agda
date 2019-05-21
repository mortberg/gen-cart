{-# OPTIONS --rewriting #-}
module fiberwise-total where

open import prelude
open import interval
open import cofprop
open import fibrations
open import wtypesred
open import Data.products

fiberwise+total→isFib : ∀ {ℓ} {Γ : Set ℓ} (A : Γ → Set) (B : (x : Γ) → A x → Set)
  (α : isFib A)
  (fβ : ∀ x → isFib (B x))
  (tβ : isFib (Σ' A (uncurry B)))
  → isFib (uncurry B)
fiberwise+total→isFib A B α fβ tβ r pa φ f (b₀ , ext) = record
  { comp = λ s →
    ( subst (B (p s))
        (symm (aFix I .comp s .snd ∣ inr ∣ inr refl ∣ ∣))
        (actual s .comp I (O≡IsCofProp I) .fst)
    , λ u →
      adjustSubstEq (B (p s))
        (aFix I .comp s .snd ∣ inl u ∣) refl
        refl (symm (aFix I .comp s .snd ∣ inr ∣ inr refl ∣ ∣))
        (actual s .comp I (O≡IsCofProp I) .snd u)
    )
  ; cap =
    ( path
      (λ t →
        subst (B (p r))
          (symm (aFix I .cap .snd t ∣ inr ∣ inr refl ∣ ∣))
          (capPath t .fst))
      (adjustSubstEq (B (p r))
        refl (symm (aFix I .cap .fst .atO))
        (symm (aFix I .cap .snd O ∣ inr ∣ inr refl ∣ ∣))
        (symm (aFix I .comp r .snd ∣ inr ∣ inr refl ∣ ∣))
        (symm (capPath O .snd ∣ inr ∣ inl refl ∣ ∣)))
      (trans
        (trans
          (congdep snd (total .cap .fst .atI))
          (appCong (symm (subst-cong-assoc (B (p r)) fst (total .cap .fst .atI)))))
        (adjustSubstEq (B (p r))
          refl (symm (aFix I .cap .fst .atI))
          (symm (aFix I .cap .snd I ∣ inr ∣ inr refl ∣ ∣)) (cong fst (total .cap .fst .atI))
          (symm (capPath I .snd ∣ inr ∣ inr refl ∣ ∣))))
    , λ t u →
      adjustSubstEq (B (p r))
        (aFix I .cap .snd t ∣ inl u ∣) refl
        refl (symm (aFix I .cap .snd t ∣ inr ∣ inr refl ∣ ∣))
        (capPath t .snd ∣ inl u ∣)
    )
  }
  where
  p = fst ∘ pa
  a = snd ∘ pa

  total = tβ r p φ
    (λ u i → (a i , f u i))
    ((a r , b₀) , λ u → cong (_,_ _) (ext u))

  module _ (j : Int) where

    aFixTube : [ φ ∨ j ≈O ∨ j ≈I ] → Π (A ∘ p)
    aFixTube =
      ∨-rec φ (j ≈O ∨ j ≈I)
        (λ _ i → a i)
        (OI-rec j
          (λ _ i → total .comp i .fst .fst)
          (λ _ i → a i))
        (λ u → ∨-elimEq (j ≈O) (j ≈I)
          (λ {refl → funext λ i → cong fst (total .comp i .snd u)})
          (λ _ → refl))

    aFixBase : A (p r) [ φ ∨ j ≈O ∨ j ≈I ↦ aFixTube ◆ r ]
    aFixBase =
      ( total .cap .fst .at j .fst
      , ∨-elimEq φ (j ≈O ∨ j ≈I)
        (λ u → cong fst (total .cap .snd j u))
        (∨-elimEq (j ≈O) (j ≈I)
          (λ {refl → cong fst (symm (total .cap .fst .atO))})
          (λ {refl → cong fst (symm (total .cap .fst .atI))}))
      )
  
    aFix = α r p (φ ∨ j ≈O ∨ j ≈I) aFixTube aFixBase

  module _ (s : Int) where

    actualTube : [ φ ] → (j : Int) → B (p s) (aFix j .comp s .fst)
    actualTube u j =
      subst (B (p s))
        (aFix j .comp s .snd ∣ inl u ∣)
        (f u s)

    actualBase : B (p s) (aFix O .comp s .fst) [ φ ↦ actualTube ◆ O ]
    actualBase =
      ( subst (B (p s))
          (aFix O .comp s .snd ∣ inr ∣ inl refl ∣ ∣)
          (total .comp s .fst .snd)
      , λ u →
        adjustSubstEq (B (p s))
          (cong fst (total .comp s .snd u)) refl
          (aFix O .comp s .snd ∣ inl u ∣) (aFix O .comp s .snd ∣ inr ∣ inl refl ∣ ∣)
          (trans
            (congdep snd (total .comp s .snd u))
            (appCong (symm (subst-cong-assoc (B (p s)) fst (total .comp s .snd u)))))
      )

    actual =
      strictifyFib (B (p s)) (fβ (p s))
        O
        (λ j → aFix j .comp s .fst)
        φ
        actualTube
        actualBase

  module _ (t : Int) where

    capTube : [ φ ∨ t ≈O ∨ t ≈I ] → (j : Int) → B (p r) (aFix j .cap .fst .at t)
    capTube =
      ∨-rec φ (t ≈O ∨ t ≈I)
        (λ u j →
          subst (B (p r))
            (aFix j .cap .snd t ∣ inl u ∣)
            (f u r))
        (OI-rec t
          (λ {refl j →
            subst (B (p r))
              (symm (aFix j .cap .fst .atO))
              (actual r .comp j (O≡IsCofProp j) .fst)})
          (λ {refl j →
            subst (B (p r))
              (symm (aFix j .cap .fst .atI))
              (total .cap .fst .at j .snd)}))
        (λ u → ∨-elimEq (t ≈O) (t ≈I)
          (λ {refl → funext λ j →
            adjustSubstEq (B (p r))
              (aFix j .comp r .snd ∣ inl u ∣) refl
              (aFix j .cap .snd O ∣ inl u ∣) (symm (aFix j .cap .fst .atO))
              (actual r .comp j (O≡IsCofProp j) .snd u)})
          (λ {refl → funext λ j →
            adjustSubstEq (B (p r))
              (cong fst (total .cap .snd j u)) refl
              (aFix j .cap .snd I ∣ inl u ∣) (symm (aFix j .cap .fst .atI))
              (trans
                (congdep snd (total .cap .snd j u))
                (appCong (symm (subst-cong-assoc (B (p r)) fst (total .cap .snd j u)))))}))

    capBase : B (p r) (aFix O .cap .fst .at t) [ φ ∨ t ≈O ∨ t ≈I ↦ capTube ◆ O ]
    capBase =
      ( subst (B (p r))
        (aFix O .cap .snd t ∣ inr ∣ inl refl ∣ ∣)
        (total .comp r .fst .snd)
      , ∨-elimEq φ (t ≈O ∨ t ≈I)
        (λ u →
          adjustSubstEq (B (p r))
            (cong fst (total .comp r .snd u)) refl
            (aFix O .cap .snd t ∣ inl u ∣) (aFix O .cap .snd t ∣ inr ∣ inl refl ∣ ∣)
            (trans
              (congdep snd (total .comp r .snd u))
              (appCong (symm (subst-cong-assoc (B (p r)) fst (total .comp r .snd u))))))
        (∨-elimEq (t ≈O) (t ≈I)
          (λ {refl →
            adjustSubstEq (B (p r))
              refl (aFix O .comp r .snd ∣ inr ∣ inl refl ∣ ∣)
              (symm (aFix O .cap .fst .atO)) (aFix O .cap .snd O ∣ inr ∣ inl refl ∣ ∣)
              (actual r .cap (O≡IsCofProp O))})
          λ {refl →
            adjustSubstEq (B (p r))
              (cong fst (total .cap .fst .atO)) refl
              (symm (aFix O .cap .fst .atI)) (aFix O .cap .snd I ∣ inr ∣ inl refl ∣ ∣)
              (trans
                (congdep snd (total .cap .fst .atO))
                (appCong (symm (subst-cong-assoc (B (p r)) fst (total .cap .fst .atO)))))})
      )

    capPath =
      fβ (p r)
        O
        (λ j → aFix j .cap .fst .at t)
        (φ ∨ t ≈O ∨ t ≈I)
        capTube
        capBase
        .comp I
