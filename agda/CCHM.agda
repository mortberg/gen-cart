{-

Proof that CCHM fibrations defined in

  https://arxiv.org/abs/1611.02108

are equivalent to weak fibrations in the presence of a connection
algebra à la Orton-Pitts:

  https://lmcs.episciences.org/5028/pdf
  https://github.com/IanOrton/cubical-topos-experiments

We also prove that CCHM composition implies filling and squeeze
operations.

-}
{-# OPTIONS --rewriting #-}
module CCHM where

-- Use Bool to represent the endpoints O and I
open import Agda.Builtin.Bool renaming ( Bool to OI ; false to O' ; true to I' )

open import prelude
open import interval
open import cofprop
open import fibrations

! : OI → OI
! O' = I'
! I' = O'

⟨_⟩ : OI → Int
⟨ O' ⟩ = O
⟨ I' ⟩ = I

----------------------------------------------------------------------
-- CCHM Fibrations
----------------------------------------------------------------------

Comp : OI → (Int → Set) → Set
Comp e A = (φ : CofProp) (f : [ φ ] → Π A) →
  A ⟨ e ⟩ [ φ ↦ f ◆ ⟨ e ⟩ ] →
  A ⟨ ! e ⟩ [ φ ↦ f ◆ ⟨ ! e ⟩ ]

isCCHMFib : ∀ {ℓ} {Γ : Set ℓ} (A : Γ → Set) → Set ℓ
isCCHMFib {Γ = Γ} A = (e : OI) (p : Int → Γ) → Comp e (A ∘ p)

isFib→isCCHMFib : ∀ {ℓ} {Γ : Set ℓ} (A : Γ → Set) → isFib A → isCCHMFib A
isFib→isCCHMFib A α e p φ f x₀ = α ⟨ e ⟩ p φ f x₀ .comp ⟨ ! e ⟩


-- We now assume that we have a connection algebra structure
postulate
  min max : Int → Int → Int

  minOi=O : (i : Int) → min O i ≡ O
  minIi=i : (i : Int) → min I i ≡ i
  miniO=O : (i : Int) → min i O ≡ O
  miniI=i : (i : Int) → min i I ≡ i

  {-# REWRITE minOi=O minIi=i miniO=O miniI=i #-}

  maxOi=i : (i : Int) → max O i ≡ i
  maxIi=I : (i : Int) → max I i ≡ I
  maxiO=i : (i : Int) → max i O ≡ i
  maxiI=I : (i : Int) → max i I ≡ I

  {-# REWRITE maxOi=i maxIi=I maxiO=i maxiI=I #-}

----------------------------------------------------------------------
-- Deriving weak composition for a CCHM fibration
----------------------------------------------------------------------

isCCHMFib→isFib : ∀ {ℓ} {Γ : Set ℓ} (A : Γ → Set) → isCCHMFib A → isFib A
isCCHMFib→isFib {Γ = Γ} A α r p φ f x₀ = record
  { comp = λ s → (fil s .fst , λ u → fil s .snd ∣ inl u ∣)
  ; cap  =
    ( path
      (λ t → fil' t .fst)
      (cong
        (λ {(f , ex) → α O' (λ i → p (min i r)) (φ ∨ O ≈I) f (sqz O .fst , ex) .fst})
        (Σext
          (funext
            (∨-elimEq φ (O ≈I)
              (λ _ → refl)
              (λ v → O≠I v)))
          (funext λ _ → uipImp)))
      (symm (fil' I .snd ∣ inr refl ∣))
    , λ t u → fil' t .snd ∣ inl u ∣
    )
  }
  where
  module _ (t : Int) where

    sqzTube : [ φ ∨ t ≈I ] → (i : Int) → A (p (min (max t i) r))
    sqzTube =
      ∨-rec φ (t ≈I)
        (λ u i → f u (min (max t i) r))
        (λ {refl i → x₀ .fst})
        (λ {u refl → funext λ i → x₀ .snd u})

    x₀' : A (p r) [ φ ∨ t ≈I ↦ sqzTube ◆ I ]
    x₀' = x₀ .fst , ∨-elimEq φ (t ≈I) (x₀ .snd) (λ {refl → refl})

    sqz = α I' (λ i → p (min (max t i) r)) (φ ∨ t ≈I) sqzTube x₀'

  module _ (s : Int) where

    filTube : [ φ ∨ O ≈I ] → (i : Int) → A (p (min i s))
    filTube =
      ∨-rec φ (O ≈I)
        (λ u i → f u (min i s))
        O≠I
        (λ _ O≡I → O≠I O≡I)

    filBase : A (p O) [ φ ∨ O ≈I ↦ filTube ◆ O ]
    filBase =
      ( sqz O .fst
      , ∨-elimEq φ (O ≈I)
          (λ u → sqz O .snd ∣ inl u ∣)
          (λ v → O≠I v)
      )

    fil = α O' (λ i → p (min i s)) (φ ∨ O ≈I) filTube filBase

  module _ (t : Int) where

    fil' = α O' (λ i → p (min (max t i) r)) (φ ∨ t ≈I) (sqzTube t) (sqz t)

----------------------------------------------------------------------
-- Deriving fill and squeeze operations from CCHM composition
----------------------------------------------------------------------

!! : ∀ e → ! (! e) ≡ e
!! true = refl
!! false = refl

_≈OI_ : Int → OI → CofProp
r ≈OI O' = r ≈O
r ≈OI I' = r ≈I

[≈OI] : ∀ i e → [ i ≈OI e ] ≡ (i ≡ ⟨ e ⟩)
[≈OI] i false = refl
[≈OI] i true = refl

{-# REWRITE !! [≈OI] #-}

cnx : OI → Int → Int → Int
cnx O' = min
cnx I' = max

cnxeei=e : (e : OI)(i : Int) → cnx e ⟨ e ⟩ i ≡ ⟨ e ⟩
cnxeei=e O' i = refl
cnxeei=e I' i = refl

cnxeie=e : (e : OI)(i : Int) → cnx e i ⟨ e ⟩ ≡ ⟨ e ⟩
cnxeie=e O' i = refl
cnxeie=e I' i = refl

cnx!eei=i : (e : OI)(i : Int) → cnx (! e) ⟨ e ⟩ i ≡ i
cnx!eei=i O' i = refl
cnx!eei=i I' i = refl

cnx!eie=i : (e : OI)(i : Int) → cnx (! e) i ⟨ e ⟩ ≡ i
cnx!eie=i O' i = refl
cnx!eie=i I' i = refl

cnxe!ei=i : (e : OI)(i : Int) → cnx e ⟨ ! e ⟩ i ≡ i
cnxe!ei=i O' i = refl
cnxe!ei=i I' i = refl

cnxei!e=i : (e : OI)(i : Int) → cnx e i ⟨ ! e ⟩ ≡ i
cnxei!e=i O' i = refl
cnxei!e=i I' i = refl

{-# REWRITE cnxeei=e cnxeie=e cnx!eei=i cnx!eie=i cnxe!ei=i cnxei!e=i #-}

record Fill (e : OI) (A : Int → Set) (φ : CofProp) (f : [ φ ] → Π A)
            (x₀ : A ⟨ e ⟩ [ φ ↦ f ◆ ⟨ e ⟩ ]) : Set where
  field
    fill : (r : Int) → A r [ φ ↦ f ◆ r ]
    cap  : fill ⟨ e ⟩ .fst ≡ x₀ .fst

open Fill public

hasFill : ∀ {ℓ} {Γ : Set ℓ} (A : Γ → Set) → Set ℓ
hasFill {Γ = Γ} A = (e : OI) (p : Int → Γ) (φ : CofProp) (f : [ φ ] → Π (A ∘ p))
            (x₀ : A (p ⟨ e ⟩) [ φ ↦ f ◆ ⟨ e ⟩ ]) → Fill e (A ∘ p) φ f x₀

isCCHMFib→Fill : ∀ {ℓ} {Γ : Set ℓ} (A : Γ → Set) → isCCHMFib A → hasFill A
isCCHMFib→Fill A α e p φ f x₀ = record
  { fill = λ r → (a r .fst , λ u → a r .snd ∣ inl u ∣)
  ; cap  = symm (a ⟨ e ⟩ .snd ∣ inr refl ∣)
  }
  where
  module _ (r : Int) where
    φ∨r≡e : CofProp
    φ∨r≡e = φ ∨ (r ≈OI e)
    f' : [ φ∨r≡e ] → (i : Int) → A (p (cnx e i r))
    f' = ∨-rec φ (r ≈OI e)
              (λ x i → f x (cnx e i r))
              (λ {refl → λ _ → x₀ .fst})
              (λ u → λ {refl → funext λ x → x₀ .snd u})
    a = α e (λ i → p (cnx e i r)) φ∨r≡e f'
          (x₀ .fst , ∨-elimEq φ (r ≈OI e) (snd x₀) (λ {refl → refl}))

record Squeeze (r : Int) (A : Int → Set) (φ : CofProp) (f : [ φ ] → Π A)
            (x₀ : A r [ φ ↦ f ◆ r ]) : Set where
  field
    squeeze : (e : OI) → A ⟨ e ⟩ [ φ ↦ f ◆ ⟨ e ⟩ ]
    cap     : (e : OI) (p : ⟨ e ⟩ ≡ r)  → subst A p (squeeze e .fst) ≡ x₀ .fst

open Squeeze public

hasSqueeze : ∀ {ℓ} {Γ : Set ℓ} (A : Γ → Set) → Set ℓ
hasSqueeze {Γ = Γ} A = (r : Int) (p : Int → Γ) (φ : CofProp) (f : [ φ ] → Π (A ∘ p))
            (x₀ : A (p r) [ φ ↦ f ◆ r ]) → Squeeze r (A ∘ p) φ f x₀

isCCHMFib→Squeeze : ∀ {ℓ} {Γ : Set ℓ} (A : Γ → Set) → isCCHMFib A → hasSqueeze A
isCCHMFib→Squeeze A α r p φ f x₀ = record
  { squeeze = λ e → (a e .fst , λ u → a e .snd ∣ inl u ∣)
  ; cap     = λ {e refl → symm (a e .snd ∣ inr refl ∣)}
  }
  where
  module _ (e : OI) where
    f' : [ φ ∨ (r ≈OI e) ] → (i : Int) → A (p (cnx e i r))
    f' = ∨-rec φ (r ≈OI e)
               (λ x i → f x (cnx e i r))
               (λ {refl → λ _ → x₀ .fst})
               (λ u → λ {refl → funext λ x → x₀ .snd u})
    a = α (! e) (λ i → p (cnx e i r)) (φ ∨ (r ≈OI e)) f'
            (x₀ .fst , ∨-elimEq φ (r ≈OI e) (snd x₀) (λ {refl → refl}))
