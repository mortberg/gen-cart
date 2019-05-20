{-# OPTIONS --rewriting #-}

open import prelude
open import cof
open import fibrations
open import interval
open import trivialfib
open import wtypesred
open import equivs

module cofreplacement where

crpoly : (A : Set) → Poly
crpoly A = record { Constr = A ⊎ Cof
                  ; Arity = λ {(inl a) → ∅ ; (inr φ) → [ φ ]}
                  ; Red = λ {(inl a) → (O  ≈I) ; (inr φ) → φ }
                  ; ev = λ {(inl a) → O≠I ; (inr φ) → λ x → x} }


CR : (A : Set) → Set
CR A = WR (crpoly A)

incl : {A : Set} → A → CR A
incl a = sup _ (inl a) ∅-elim

fill : {A : Set} (φ : Cof) → (u : [ φ ] → CR A) → CR A
fill φ u = sup _ (inr φ) u

CR-red : {A : Set} {φ : Cof} (u : [ φ ] → CR A) →
         (x : [ φ ]) → (fill φ u) ≡ u x
CR-red u x = red _ (inr _) u x

CR-elim : ∀ {ℓ'} {A : Set} (B : CR A → Set ℓ')
           (b₀ : (a : A) → (B (incl a)))
           (h : (φ : Cof) → (u : [ φ ] → CR A) →
                (f : (x : [ φ ]) → B (u x)) → B (fill φ u)) →
           (p : (φ : Cof) → (u : [ φ ] → CR A) →
                (f : (x : [ φ ]) → B (u x)) →
                (x : [ φ ]) → (subst B (CR-red u x) (h φ u f)) ≡ f x) →
           (z : CR A) → (B z)
CR-elim B b₀ h p = WR-elim _ B
  (λ { (inl a) → λ _ _ → subst B (cong (sup _ (inl a)) (funext ∅-elim)) (b₀ a)
     ; (inr φ) → h φ})
  λ { (inl a) → λ α u x → O≠I x
    ; (inr φ) → p φ}

CR-β : ∀ {ℓ'} {A : Set} (B : CR A → Set ℓ')
             {b₀ : (a : A) → (B (incl a))}
             {h : (φ : Cof) → (u : [ φ ] → CR A) →
                  (f : (x : [ φ ]) → B (u x)) → B (fill φ u)} →
             {p : (φ : Cof) → (u : [ φ ] → CR A) →
                  (f : (x : [ φ ]) → B (u x)) →
                  (x : [ φ ]) → (subst B (CR-red u x) (h φ u f)) ≡ f x} →
             (a : A) → (CR-elim B b₀ h p (incl a) ≡ b₀ a)
CR-β B {b₀ = b₀} a = trans (cong (λ p → subst B p (b₀ a)) (uip ((cong (sup _ (inl a)) (funext ∅-elim))) refl)) (WR-elim-β _ B _ _ _ _ ∅-elim)


CR-iscontr : {A : Set} → (SContr (CR A))
CR-iscontr {A = A} φ u = fill φ u , λ x → symm (CR-red u x)

CR-isfib : ∀ {ℓ} (Γ : Set ℓ) (A : Γ → Set) → (isFib (CR ∘ A))
CR-isfib Γ A = TrivialFib-isFib (CR ∘ A) (λ a → CR-iscontr)

record cofibration {A B : Set} (f : A → B) : Set₁ where
  field
    j : (X : B → Set) (xfib : isTrivialFib X) (x₀ : (a : A) → X (f a)) → (b : B) → X b
    upper-tri : (X : B → Set) (xfib : isTrivialFib X) (x₀ : (a : A) → X (f a)) → (a : A) →
                   j X xfib x₀ (f a) ≡ x₀ a

record triv-cofibration {A B : Set} (f : A → B) : Set₁ where
  field
    j : (X : B → Set) (xfib : isFib X) (x₀ : (a : A) → X (f a)) → (b : B) → X b
    upper-tri : (X : B → Set) (xfib : isFib X) (x₀ : (a : A) → X (f a)) → (a : A) →
                   j X xfib x₀ (f a) ≡ x₀ a

module cof-replace {A B : Set} (f : A → B) where
  M₀ : B → Set
  M₀ b = CR (SFiber f b)

  M₀-isTrivialFib : isTrivialFib M₀
  M₀-isTrivialFib b = CR-iscontr

  M : Set
  M = Σ B M₀

  L₀ : (a : A) → (M₀ (f a))
  L₀ a = incl (a , refl)

  L : A → M
  L a = f a , L₀ a

  L-cof : cofibration L
  L-cof =
      record { j = j
             ; upper-tri = ut }
      where
        module _ (X : M → Set) (xtf : isTrivialFib X) (x₀ : (a : A) → X (L a)) where
          X' : (b : B) → CR (SFiber f b) → Set
          X' b z = X (b , z)
  
          lemma1 : (a : A) (b : B) (p : f a ≡ b) → (f a , incl (a , refl)) ≡ (b , incl (a , p))
          lemma1 a .(f a) refl = refl

          j : (m : M) → X m
          j (b , z) = CR-elim (X' b) (λ {(a , p) → subst X (lemma1 a b p) (x₀ a)})
                             (λ φ u g → fst (h φ u g))
                             (λ φ u g x → lemma2 (CR-red u x) (g x) (fst (h φ u g)) (snd (h φ u g) x))
                             z
            where
              lemma2 : {x y : CR (SFiber f b)} (q : y ≡ x) (z : X' b x) (w : X' b y) →
                       (subst (X' b) (symm q) z ≡ w) → (subst (X' b) q w ≡ z)
              lemma2 refl x y = symm
                            
              h : (φ : Cof) (u : [ φ ] → CR (SFiber f b)) →
                  (s : (x : [ φ ]) → X' b (u x)) →
                  X' b (fill φ u) [ φ ↦ (λ x → subst (λ c' → X' b c') (symm (CR-red u x)) (s x)) ]
              h φ u s = xtf (b , fill φ u) φ _

          ut : (a : A) → j (L a) ≡ x₀ a
          ut a = CR-β (X' (f a)) (a , refl)


  R : M → B
  R = fst

  R-tf : map-isTrivialFib R
  R-tf = TrivialFib-tomap _ M₀-isTrivialFib