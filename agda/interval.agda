{-

Definition of the interval and Path types.

-}
{-# OPTIONS --rewriting #-}
module interval where

open import prelude

----------------------------------------------------------------------
-- Interval
----------------------------------------------------------------------
postulate
  Int  : Set
  O    : Int
  I    : Int
  O≠I  : ∀ {ℓ} {A : Set ℓ} → O ≡ I → A
  cntd : (P : Int → Set) → ((i : Int) → P i ⊎ ¬ (P i)) → (i j : Int) → P i → P j


¬O≡I : ¬ (O ≡ I)
¬O≡I = O≠I

¬O≡I→O≠I : ¬ (O ≡ I) → (∀ {ℓ} {A : Set ℓ} → O ≡ I → A)
¬O≡I→O≠I H x = ∅-rec (H x)

----------------------------------------------------------------------
-- Dependently typed paths
----------------------------------------------------------------------
Π : ∀ {ℓ} → (Int → Set ℓ) → Set ℓ
Π A = (i : Int) → A i

Π′ : ∀ {ℓ}
  {A B : Int → Set ℓ}
  → ---------------------------------
  ((i : Int) → A i → B i) → Π A → Π B
Π′ F p i = F i (p i)

----------------------------------------------------------------------
-- Path types
----------------------------------------------------------------------

record _~~_ {A : Int → Set}(a : A O)(a' : A I) : Set where
  constructor path
  field
    at : Π A
    atO : at O ≡ a
    atI : at I ≡ a'

open _~~_ public

_~_ : {A : Set}(a a' : A) → Set
_~_ {A} a a' = _~~_ {A = λ _ → A} a a'

refl~ : {A : Set}(a : A) → a ~ a
refl~ a = path (λ _ → a) refl refl

PathExt : {A : Set}{a a' : A}{p q : a ~ a'} → p .at ≡ q .at → p ≡ q
PathExt {p = p} refl = cong₂ (path (p .at)) uipImp uipImp

PathExtDep : {I : Set} {A : Set} {a₀ a₁ : I → A}
  {i i' : I} (r : i ≡ i')
  {p : a₀ i ~ a₁ i} {q : a₀ i' ~ a₁ i'}
  → p .at ≡ q .at
  → subst (λ i → a₀ i ~ a₁ i) r p ≡ q
PathExtDep refl {p = p} refl = cong₂ (path (p .at)) uipImp uipImp

eqToPath : {A : Set} {x y : A} → x ≡ y → x ~ y
eqToPath refl = refl~ _

eqToPathAtO : {A : Set} {x y : A} (e : x ≡ y) (k : Int) → eqToPath e .at k ≡ x
eqToPathAtO refl k = refl
