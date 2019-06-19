{-

Proof of univalence in the form of ua and uaβ.

-}
{-# OPTIONS --rewriting #-}
module univalence where

open import prelude
open import interval
open import cofprop
open import fibrations
open import Data.functions
open import Data.paths
open import equivs
open import glueing

record PathU {ℓ} {Γ : Set ℓ} (Aα Bβ : Fib Γ) : Set (lsuc lzero ⊔ ℓ) where
  constructor pathU
  field
    line : Fib (Γ × Int)
    atO : reindex' line (λ x → x , O) ≡ Aα
    atI : reindex' line (λ x → x , I) ≡ Bβ

open PathU public

record PathD {ℓ} {Γ : Set ℓ} (Aα Bβ : Fib Γ) (P : PathU Aα Bβ) (x : Γ) (a : Aα .fst x) (b : Bβ .fst x)
  : Set (lsuc lzero ⊔ ℓ) where
  constructor pathD
  field
    line : ∀ i → P .line .fst (x , i)
    atO : subst (λ F → F .fst x) (P .atO) (line O) ≡ a
    atI : subst (λ F → F .fst x) (P .atI) (line I) ≡ b

open PathD public

module _ {ℓ} {Γ : Set ℓ} {A B : Fib Γ} (P : PathU A B) (x : Γ) (a : A .fst x) where

  private
    H = P .line .fst
    η = P .line .snd

    com =
      strictifyFib H η O (λ i → x , i) ⊥ (∅-rec ∘ O≠I)
        ( subst (λ F → F .fst x) (symm (P .atO)) a
        , λ u → O≠I u
        )

  abstract
    coerce : B .fst x
    coerce = subst (λ F → F .fst x) (P .atI) (com .comp I (O≡IsCofProp I) .fst)

    coerceFill : PathD A B P x a coerce
    coerceFill =
      pathD
        (λ i → com .comp i (O≡IsCofProp i) .fst)
        (adjustSubstEq (λ F → F .fst x)
          refl (symm (P .atO))
          (P .atO) refl
          (com .cap (O≡IsCofProp O)))
        refl

private
  ∈OI : ∀ {ℓ} {Γ : Set ℓ} → Γ × Int → CofProp
  ∈OI (_ , i) = (i ≈O) ∨ (i ≈I)

  extractOI : (i : Int) → [ i ≈O ∨ i ≈I ] → i ≡ O ⊎ i ≡ I
  extractOI i = OI-rec i inl inr

  discriminate : (f : Int → Int)
    → (∀ i → f i ≡ O ⊎ f i ≡ I)
    → (∀ i → f i ≡ O) ⊎ (∀ i → f i ≡ I)
  discriminate f inOI with inOI O
  discriminate f inOI | inl fO≡O =
    inl (λ i → cntd (λ j → f j ≡ O) dec O i fO≡O)
    where
    dec : (i : Int) → f i ≡ O ⊎ ¬ (f i ≡ O)
    dec i with inOI i
    dec i | inl fi≡O = inl fi≡O
    dec i | inr fi≡I = inr λ fi≡O → O≠I (trans fi≡I (symm fi≡O))
  discriminate f inOI | inr fO≡I =
    inr (λ i → cntd (λ j → f j ≡ I) dec O i fO≡I)
    where
    dec : (i : Int) → f i ≡ I ⊎ ¬ (f i ≡ I)
    dec i with inOI i
    dec i | inl fi≡O = inr λ fi≡I → O≠I (trans fi≡I (symm (fi≡O)))
    dec i | inr fi≡I = inl fi≡I

module _ {ℓ} {Γ : Set ℓ} (Aα Bβ : Fib Γ)
  (f : (x : Γ) → Aα .fst x → Bβ .fst x) (fEquiv : Equiv' f)
  where

  private
    T : res (Γ × Int) ∈OI → Set
    T ((x , i) , u) =
      OI-rec i
        (λ {refl → Aα .fst x})
        (λ {refl → Bβ .fst x})
        u

    Options : (p : Int → res (Γ × Int) ∈OI) → Set ℓ
    Options p =
      ((λ i → (p i .fst .fst , O) , ∣ inl refl ∣)) ≡ p
      ⊎ ((λ i → (p i .fst .fst , I) , ∣ inr refl ∣)) ≡ p

    extendedDiscr : (p : Int → res (Γ × Int) ∈OI) → Options p
    extendedDiscr p with discriminate (snd ∘ fst ∘ p) (λ i → extractOI _ (p i .snd))
    extendedDiscr p | inl pO =
      inl (funext λ i → Σext (Σext refl (symm (pO i))) (trunc _ _))
    extendedDiscr p | inr pI =
      inr (funext λ i → Σext (Σext refl (symm (pI i))) (trunc _ _))


    τHelper : (r : Int) (p : Int → res (Γ × Int) ∈OI)
      → Options p → ∀ φ f x₀ → WComp r (λ x → T (p x)) φ f x₀
    τHelper r p (inl pO) =
      subst (λ p → ∀ φ f x₀ → WComp r (T ∘ p) φ f x₀) pO (Aα .snd r (fst ∘ fst ∘ p))
    τHelper r p (inr pI) =
      subst (λ p → ∀ φ f x₀ → WComp r (T ∘ p) φ f x₀) pI (Bβ .snd r (fst ∘ fst ∘ p))

    τ : isFib T
    τ r p = τHelper r p (extendedDiscr _)

    τOHelper : (r : Int) (p : Int → Γ) (op : Options (λ i → (p i , O) , ∣ inl refl ∣))
      → τHelper r (λ i → (p i , O) , ∣ inl refl ∣) op ≡ Aα .snd r p
    τOHelper r p (inl pO) =
      cong
        (λ q → subst (λ p → ∀ φ f x₀ → WComp r (T ∘ p) φ f x₀) q (Aα .snd r p))
        (uip pO refl)
    τOHelper r p (inr pI) =
      O≠I (symm (cong (λ f → f O .fst .snd) pI))

    τO : reindex T τ (λ x → (x , O) , ∣ inl refl ∣) ≡ Aα .snd
    τO = funext λ r → funext λ p → τOHelper r p (extendedDiscr _)

    τIHelper : (r : Int) (p : Int → Γ) (op : Options (λ i → (p i , I) , ∣ inr refl ∣))
      → τHelper r (λ i → (p i , I) , ∣ inr refl ∣) op ≡ Bβ .snd r p
    τIHelper r p (inl pO) =
      O≠I (cong (λ f → f I .fst .snd) pO)
    τIHelper r p (inr pI) =
      cong
        (λ q → subst (λ p → ∀ φ f x₀ → WComp r (T ∘ p) φ f x₀) q (Bβ .snd r p))
        (uip pI refl)

    τI : reindex T τ (λ x → (x , I) , ∣ inr refl ∣) ≡ Bβ .snd
    τI = funext λ r → funext λ p → τIHelper r p (extendedDiscr _)

    g : (xiu : res (Γ × Int) ∈OI) → T xiu → Bβ .fst (xiu .fst .fst)
    g ((x , i) , u) =
      ∨-elim (i ≈O) (i ≈I)
        (λ u → T ((x , i) , u) → Bβ .fst x)
        (λ {refl → f x})
        (λ {refl → id})
        (λ {refl i≡I → O≠I i≡I})
        u

    gEquiv : Equiv' g
    gEquiv ((x , i) , u) =
      ∨-elim (i ≈O) (i ≈I)
        (λ u → Equiv (g ((x , i) , u)))
        (λ {refl → fEquiv x})
        (λ {refl → idEquiv (Bβ .snd) x})
        (λ {refl i≡I → O≠I i≡I})
        u

  ua : PathU Aα Bβ
  ua =
    pathU
      (SGlueFib ∈OI (T , τ) (reindex' Bβ fst) g gEquiv)
      (trans
        (Σext refl τO)
        (cong (λ Hη → reindex' Hη (λ x → ((x , O) , ∣ inl refl ∣)))
          (symm (SGlueFibStrictness ∈OI (T , τ) (reindex' Bβ fst) g gEquiv))))
      (trans
        (Σext refl τI)
        (cong (λ Hη → reindex' Hη (λ x → ((x , I) , ∣ inr refl ∣)))
          (symm (SGlueFibStrictness ∈OI (T , τ) (reindex' Bβ fst) g gEquiv))))

  uaβ : (x : Γ) (a : Aα .fst x) → f x a ~ coerce ua x a
  uaβ x a =
    path
      (λ k → sunglue (λ u → g ((x , k) , u)) (coerceFill ua x a .line k))
      (trans
        (sunglue-boundary (∈OI (x , O)) (λ u → g ((x , O) , u)) ∣ inl refl ∣ a)
        (cong (sunglue (λ u → g ((x , O) , u))) lemO))
      (trans
        (sunglue-boundary (∈OI (x , I)) (λ u → g ((x , I) , u)) ∣ inr refl ∣ (coerce ua x a))
        (cong (sunglue (λ u → g ((x , I) , u))) lemI))
    where
    lemO :
      coerceFill ua x a .line O
      ≡ coe (SGlueStrictness (∈OI (x , O)) (λ u → g ((x , O) , u)) ∣ inl refl ∣) a
    lemO =
      adjustSubstEq id
        (cong (λ F → F .fst x) (ua .atO)) refl
        refl (SGlueStrictness (∈OI (x , O)) (λ u → g ((x , O) , u)) ∣ inl refl ∣)
        (trans
          (coerceFill ua x a .atO)
          (symm (appCong (subst-cong-assoc id (λ F → F .fst x) (ua .atO)))))

    lemI :
      coerceFill ua x a .line I
      ≡ coe (SGlueStrictness (∈OI (x , I)) (λ u → g ((x , I) , u)) ∣ inr refl ∣) (coerce ua x a)
    lemI =
      adjustSubstEq id
        (cong (λ F → F .fst x) (ua .atI)) refl
        refl (SGlueStrictness (∈OI (x , I)) (λ u → g ((x , I) , u)) ∣ inr refl ∣)
        (trans
          (coerceFill ua x a .atI)
          (symm (appCong (subst-cong-assoc id (λ F → F .fst x) (ua .atI)))))
