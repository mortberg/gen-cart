{-

Definition of the universe of cofibrant propositions and basic
operations on these.

-}
{-# OPTIONS --rewriting #-}

module cofprop where

open import prelude
open import interval

infixr 4 _∨_
infix  5 _↗_

----------------------------------------------------------------------
-- Cofibrant propositions
----------------------------------------------------------------------

postulate
  CofProp : Set
  [_] : CofProp → Set

  _≈O _≈I O≈_ I≈_ : (i : Int) → CofProp
  [≈O] : ∀ i → [ i ≈O ] ≡ (i ≡ O)
  [≈I] : ∀ i → [ i ≈I ] ≡ (i ≡ I)

  _∨_ : CofProp → CofProp → CofProp
  [∨] : ∀ φ ψ → [ φ ∨ ψ ] ≡ ∥ [ φ ] ⊎ [ ψ ] ∥

  ∀I : (Int → CofProp) → CofProp
  [∀I] : ∀ φ → [ ∀I φ ] ≡ ((i : Int) → [ φ i ])

  {-# REWRITE [≈O] [≈I] [∨] [∀I] #-}

  cofIsProp : (φ : CofProp) → (u v : [ φ ]) → u ≡ v

⊥ : CofProp
⊥ = O ≈I

⊥→ : ∀ {ℓ} {A : Set ℓ} → [ ⊥ ] → A
⊥→ x = O≠I x

----------------------------------------------------------------------
-- Cofibrant-partial function classifier
----------------------------------------------------------------------

_↗_ : ∀ {ℓ} {A : Set ℓ} {ϕ : Set} → (ϕ → A) → A → Set ℓ
f ↗ x = (u : _) → f u ≡ x

_◆_ : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Int → Set ℓ'}
       → (A → (i : Int) → B i) → (i : Int) → A → B i
(f ◆ i) a = f a i

_[_↦_] : ∀ {ℓ} (A : Set ℓ) (φ : CofProp) → ([ φ ] → A) → Set ℓ
A [ φ ↦ f ] = Σ a ∈ A , f ↗ a

----------------------------------------------------------------------
-- Restricting a context by a cofibrant propositions
----------------------------------------------------------------------
res : ∀ {ℓ} (Γ : Set ℓ) (Φ : Γ → CofProp) → Set ℓ
res Γ Φ = Σ x ∈ Γ , [ Φ x ]

----------------------------------------------------------------------
-- Property of being a cofibration
----------------------------------------------------------------------
isCofProp : ∀ {ℓ} (A : Set ℓ) → Set ℓ
isCofProp A = Σ φ ∈ CofProp , ([ φ ] → A) × (A → [ φ ])

≡OIsCofProp : (i : Int) → isCofProp (i ≡ O)
≡OIsCofProp i = i ≈O , id , id

≡IIsCofProp : (i : Int) → isCofProp (i ≡ I)
≡IIsCofProp i = i ≈I , id , id

O≡IsCofProp : (i : Int) → isCofProp (O ≡ i)
O≡IsCofProp i = i ≈O , symm , symm

I≡IsCofProp : (i : Int) → isCofProp (I ≡ i)
I≡IsCofProp i = i ≈I , symm , symm

----------------------------------------------------------------------
-- Compatible partial functions
----------------------------------------------------------------------
□ : ∀ {ℓ} → Set ℓ → Set ℓ
□ A = Σ φ ∈ CofProp , ([ φ ] → A)

_⌣_ : ∀ {ℓ} {A : Set ℓ} → □ A → □ A → Set ℓ
(φ , f) ⌣ (ψ , g) = (u : [ φ ]) (v : [ ψ ]) → f u ≡ g v

∨-rec : ∀ {ℓ}
  (φ ψ : CofProp)
  {A : Set ℓ}
  (f : [ φ ] → A)
  (g : [ ψ ] → A)
  (p : (φ , f) ⌣ (ψ , g))
  → ---------------------------
  [ φ ∨ ψ ] → A
∨-rec φ ψ {A = A} f g p = ∥∥-rec _ h q where

  h : [ φ ] ⊎ [ ψ ] → A
  h (inl u) = f u
  h (inr v) = g v

  q : (z z' : [ φ ] ⊎ [ ψ ]) → h z ≡ h z'
  q (inl _) (inl _) = cong f (cofIsProp φ _ _)
  q (inl u) (inr v) = p u v
  q (inr v) (inl u) = symm (p u v)
  q (inr _) (inr _) = cong g (cofIsProp ψ _ _)

OI-rec : ∀ {ℓ}
  (r : Int)
  {A : Set ℓ}
  → ([ r ≈O ] → A)
  → ([ r ≈I ] → A)
  → ---------------------------
  [ r ≈O ∨ r ≈I ] → A
OI-rec r f g =
  ∨-rec (r ≈O) (r ≈I) f g (λ {refl r≡I → O≠I r≡I})

∨-elim : ∀ {ℓ}
  (φ ψ : CofProp)
  (P : [ φ ∨ ψ ] → Set ℓ)
  (f : (u : [ φ ]) → P ∣ inl u ∣)
  (g : (v : [ ψ ]) → P ∣ inr v ∣)
  (p : (u : [ φ ]) (v : [ ψ ]) → subst P (trunc _ _) (f u) ≡ g v)
  → ---------------------------
  (w : [ φ ∨ ψ ]) → P w
∨-elim φ ψ P f g p = ∥∥-elim _ h q
  where
  h : (z : [ φ ] ⊎ [ ψ ]) → P ∣ z ∣
  h (inl u) = f u
  h (inr v) = g v

  q : (z z' :  [ φ ] ⊎ [ ψ ]) → subst P (trunc _ _) (h z) ≡ h z'
  q (inl u) (inl u') =
    trans
      (congdep f (cofIsProp φ u u'))
      (trans
        (appCong (symm (subst-cong-assoc P (∣_∣ ∘ inl) (cofIsProp φ u u'))))
        (cong (λ r → subst P r (f u))
          (uip (trunc ∣ inl u ∣ ∣ inl u' ∣) (cong (∣_∣ ∘ inl) (cofIsProp φ u u')))))
  q (inl u) (inr v) = p u v
  q (inr v) (inl u) =
    adjustSubstEq P
      refl (trunc ∣ inl u ∣ ∣ inr v ∣)
      (trunc ∣ inr v ∣ ∣ inl u ∣) refl
      (symm (p u v))
  q (inr v) (inr v') =
    trans
      (congdep g (cofIsProp ψ v v'))
      (trans
        (appCong (symm (subst-cong-assoc P (∣_∣ ∘ inr) (cofIsProp ψ v v'))))
        (cong (λ r → subst P r (g v))
          (uip (trunc ∣ inr v ∣ ∣ inr v' ∣) (cong (∣_∣ ∘ inr) (cofIsProp ψ v v')))))

OI-elim : ∀ {ℓ}
  (r : Int)
  (A : [ r ≈O ∨ r ≈I ] → Set ℓ)
  → ((rO : [ r ≈O ]) → A ∣ inl rO ∣)
  → ((rI : [ r ≈I ]) → A ∣ inr rI ∣)
  → ---------------------------
  (rOI : [ r ≈O ∨ r ≈I ]) → A rOI
OI-elim r A f g =
  ∨-elim (r ≈O) (r ≈I) A f g (λ {refl r≡I → O≠I r≡I})

∨-elimEq : ∀ {ℓ}
  (φ ψ : CofProp) {A : Set ℓ}
  {f g : [ φ ∨ ψ ] → A}
  → ((u : [ φ ]) → f ∣ inl u ∣ ≡ g ∣ inl u ∣)
  → ((v : [ ψ ]) → f ∣ inr v ∣ ≡ g ∣ inr v ∣)
  → ---------------------------
  (w : [ φ ∨ ψ ]) → f w ≡ g w
∨-elimEq φ ψ p q =
  ∨-elim φ ψ _ p q (λ _ _ → uipImp)
