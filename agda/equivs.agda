{-

Definitions of contractible, extensible (SContr), fibers, equivalences
and quasi-invertible maps.

-}
{-# OPTIONS --rewriting #-}
module equivs where

open import prelude
open import interval
open import cofprop
open import fibrations
open import hcomp-coe

----------------------------------------------------------------------
-- Contr and Ext (now called SContr)
----------------------------------------------------------------------

Contr : Set → Set
Contr A = Σ a₀ ∈ A , ((a : A) → a ~ a₀)

Contr' : ∀ {ℓ} {Γ : Set ℓ} → (Γ → Set) → Set ℓ
Contr' A = (x : _) → Contr (A x)

SContr : ∀ {ℓ} (A : Set ℓ) → Set ℓ
SContr A = (φ : CofProp) → (t : [ φ ] → A) → A [ φ ↦ t ]

SContr→Contr : {A : Set} → SContr A → Contr A
SContr→Contr h = x , λ y → path (λ i → α y i .fst)
                                (symm (α y O .snd ∣ inl refl ∣))
                                (symm (α y I .snd ∣ inr refl ∣))
  where
  x = h ⊥ O≠I .fst
  α = λ y i → h (i ≈O ∨ i ≈I) (∨-rec (i ≈O) (i ≈I) (λ _ → y) (λ _ → x) (λ {refl h → O≠I h}))

-- TODO: We need to assume that A has hcomp to finish this
-- Contr→SContr : (A : Set) → Contr A → SContr A
-- Contr→SContr A h = λ φ t → h .fst , λ u → {!h .snd (t u)!}

----------------------------------------------------------------------
-- Equivalences and quasi-inverses
----------------------------------------------------------------------

Fiber : {A B : Set} (f : A → B) (b : B) → Set
Fiber {A} f b = Σ a ∈ A , f a ~ b

Equiv : {A B : Set} (f : A → B) → Set
Equiv {B = B} f = (b : B) → Contr (Fiber f b)

EquivSContr : {A B : Set} (f : A → B) → Set
EquivSContr {B = B} f = (b : B) → SContr (Fiber f b)

EquivSContr→Equiv : {A B : Set} {f : A → B} → EquivSContr f → Equiv f
EquivSContr→Equiv h b = SContr→Contr (h b)

Equiv' : ∀ {ℓ} {Γ : Set ℓ} {A B : Γ → Set} (f : (x : Γ) → A x → B x) → Set ℓ
Equiv' {Γ = Γ} f = (x : Γ) → Equiv (f x)

Qinv : {A B : Set} (f : A → B) → Set
Qinv {A} {B} f = Σ g ∈ (B → A) , ((b : B) → f (g b) ~ b) × ((a : A) → g (f a) ~ a)

FiberExt : {A B : Set} {f : A → B} {b : B} {x y : Fiber f b}
  → x .fst ≡ y .fst → x .snd .at ≡ y .snd .at → x ≡ y
FiberExt refl refl = Σext refl (PathExt refl)

FiberExtDep : {A B : Set} {f : A → B} {b b' : B} (p : b ≡ b') {x : Fiber f b} {y : Fiber f b'}
  → x .fst ≡ y .fst → x .snd .at ≡ y .snd .at → subst (Fiber f) p x ≡ y
FiberExtDep refl = FiberExt

fiberPathEq : {A B : Set} {f : A → B} {b : B} {x y : Fiber f b}
  → x ≡ y → ∀ k → x .snd .at k ≡ y .snd .at k
fiberPathEq refl _ = refl

fiberPathEqDep : {A B : Set} {f : A → B} {b b' : B} (p : b ≡ b') {x : Fiber f b} {y : Fiber f b'}
  → subst (Fiber f) p x ≡ y → ∀ k → x .snd .at k ≡ y .snd .at k
fiberPathEqDep refl refl _ = refl

fiberDomEqDep :  {A B : Set} {f : A → B} {b b' : B} (p : b ≡ b') {x : Fiber f b} {y : Fiber f b'}
  → subst (Fiber f) p x ≡ y → x .fst ≡ y .fst
fiberDomEqDep refl refl = refl

-- The identity map on a fibration is an equivalence
idEquiv : ∀ {ℓ} {Γ : Set ℓ} {A : Γ → Set} → isFib A → Equiv' {A = A} (λ _ → id)
idEquiv {A = A} α x a .fst = (a , refl~ a)
idEquiv {A = A} α x a .snd (a' , p) =
  path
    (λ i →
      ( q i .comp O (I≡IsCofProp O) .fst
      , path
        (λ j → q i .comp j (I≡IsCofProp j) .fst)
        refl
        (q i .cap (I≡IsCofProp I))
      ))
    (FiberExt
      (trans (p .atO) (symm (q O .comp O (I≡IsCofProp O) .snd ∣ inl refl ∣)))
      (funext λ j → symm (q O .comp j (I≡IsCofProp j) .snd ∣ inl refl ∣)))
    (FiberExt
      (symm (q I .comp O (I≡IsCofProp O) .snd ∣ inr refl ∣))
      (funext λ j → symm (q I .comp j (I≡IsCofProp j) .snd ∣ inr refl ∣)))
  where
  q : (i : Int) → _
  q i =
    strictifyFib A α I (λ _ → x) (i ≈O ∨ i ≈I)
      (OI-rec i
        (λ {refl → p .at})
        (λ {refl _ → a}))
      ( a
      , ∨-elimEq (i ≈O) (i ≈I)
        (λ {refl → p .atI})
        (λ {refl → refl})
      )
