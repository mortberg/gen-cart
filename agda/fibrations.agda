{-

Definition of weak composition and fibrations. Proof that they are
closed under isomorphism and that weak composition can be strictified.

-}
{-# OPTIONS --rewriting #-}
module fibrations where

open import prelude
open import interval
open import cofprop

----------------------------------------------------------------------
-- Weak composition structure
----------------------------------------------------------------------

record WComp (r : Int) (A : Int → Set) (φ : CofProp) (f : [ φ ] → Π A)
  (x₀ : A r [ φ ↦ f ◆ r ]) : Set
  where
  field
    comp : (s : Int) → A s [ φ ↦ f ◆ s ]
    cap : Σ p ∈ comp r  .fst ~ x₀ .fst , ((k : Int) → f ◆ r ↗ p .at k)

open WComp public

----------------------------------------------------------------------
-- Fibrations
----------------------------------------------------------------------
isFib : ∀{a}{Γ : Set a}(A : Γ → Set) → Set a
isFib {Γ = Γ} A = ∀ r p φ f x₀ → WComp r (A ∘ p) φ f x₀

Fib : ∀{a}(Γ : Set a) → Set (lsuc lzero ⊔ a)
Fib {a} Γ = Σ (Γ → Set) isFib

----------------------------------------------------------------------
-- Fibrations can be reindexed
----------------------------------------------------------------------
reindex : ∀{a a'}{Δ : Set a}{Γ : Set a'}(A : Γ → Set)(α : isFib A)(ρ : Δ → Γ) → isFib (A ∘ ρ)
reindex A α ρ r p = α r (ρ ∘ p)

reindex' : ∀{a a'}{Δ : Set a}{Γ : Set a'}(Aα : Fib Γ)(ρ : Δ → Γ) → Fib Δ
reindex' (A , α) ρ = (A ∘ ρ , reindex A α ρ)

----------------------------------------------------------------------
-- Reindexing is functorial
----------------------------------------------------------------------
reindexAlongId : ∀{a}{Γ : Set a}{A : Γ → Set}{α : isFib A} → α ≡ reindex A α id
reindexAlongId = refl

reindexWComp :
  ∀{a b c}{Γ₁ : Set a}{Γ₂ : Set b}{Γ₃ : Set c}{A : Γ₃ → Set}{α : isFib A}
  (f : Γ₁ → Γ₂)(g : Γ₂ → Γ₃)
  → ----------------------
  reindex A α (g ∘ f) ≡ reindex (A ∘ g) (reindex A α g) f
reindexWComp g f = refl

reindexAlongId' : ∀{a}{Γ : Set a}{A : Fib Γ} → reindex' A id ≡ A
reindexAlongId' = refl

reindexWComp' :
  ∀{a b c}{Γ₁ : Set a}{Γ₂ : Set b}{Γ₃ : Set c}
  {A : Fib Γ₃}
  (f : Γ₁ → Γ₂)(g : Γ₂ → Γ₃)
  → ----------------------
  reindex' A (g ∘ f) ≡ reindex' (reindex' A g) f
reindexWComp' g f = refl

----------------------------------------------------------------------
-- An extensionality principle for fibration structures
----------------------------------------------------------------------
fibExt : ∀{ℓ}{Γ : Set ℓ}{A : Γ → Set}{α α' : isFib A} →
  ((r : Int) (p : Int → Γ) (φ : CofProp) (f : [ φ ] → Π (A ∘ p)) (a₀ : A (p r) [ φ ↦ f ◆ r ])
    → ((s : Int) → α r p φ f a₀ .comp s .fst ≡ α' r p φ f a₀ .comp s .fst)
    × ((t : Int) → α r p φ f a₀ .cap .fst .at t ≡ α' r p φ f a₀ .cap .fst .at t))
  → α ≡ α'
fibExt {Γ = Γ} {A} {α} {α'} ext =
  funext λ r → funext λ p → funext λ φ → funext λ f → funext λ a₀ → full r p φ f a₀
  where
  module _ (r : Int) (p : Int → Γ) (φ : CofProp) (f : [ φ ] → Π (A ∘ p))
    (a₀ : A (p r) [ φ ↦ f ◆ r ])
    where
    pairEqs : {w w' : WComp r (A ∘ p) φ f a₀}
      (q : w .comp ≡ w' .comp)
      → subst (λ c → Σ p ∈ c r  .fst ~ a₀ .fst , ((k : Int) → f ◆ r ↗ p .at k)) q (w .cap) ≡ w' .cap
      → w ≡ w'
    pairEqs refl refl = refl

    compEq : α r p φ f a₀ .comp ≡ α' r p φ f a₀ .comp
    compEq = funext λ s → Σext (ext r p φ f a₀ .fst s) (funext λ _ → uipImp)

    full : α r p φ f a₀ ≡ α' r p φ f a₀
    full =
      pairEqs compEq
        (Σextdep compEq
          (PathExtDep compEq
             (funext λ t → ext r p φ f a₀ .snd t))
          (funext λ _ → funext λ _ → uipImp))

----------------------------------------------------------------------
-- Terminal object is fibrant
----------------------------------------------------------------------
FibUnit : {Γ : Set} → isFib(λ(_ : Γ) → Unit)
FibUnit r p φ f (unit , _) .comp s = (unit , λ _ → refl)
FibUnit r p φ f (unit , _) .cap = (refl~ unit , λ _ _ → refl)

----------------------------------------------------------------------
-- Initial object is fibrant
----------------------------------------------------------------------
Fib∅ : {Γ : Set} → isFib(λ(_ : Γ) → ∅)
Fib∅ r p φ f (() , _)

----------------------------------------------------------------------
-- Fibrations are closed under isomorphism
----------------------------------------------------------------------
record _≅_ (A B : Set) : Set where
 field
  to   : A → B
  from : B → A
  inv₁ : from ∘ to ≡ id
  inv₂ : to ∘ from ≡ id

open _≅_ public

_≅'_ : ∀{a}{Γ : Set a}(A B : Γ → Set) → Set a
_≅'_ {_} {Γ} A B = (x : Γ) → A x ≅ B x

FibIso : ∀{a}{Γ : Set a}(A B : Γ → Set) → (A ≅' B) → isFib B → isFib A
FibIso A B iso β r p φ f (a₀ , ex) =
  record
  { comp = λ s →
    ( iso (p s) .from (inB .comp s .fst)
    , λ u →
      trans
        (cong (iso (p s) .from) (inB .comp s .snd u))
        (symm (appCong (iso (p s) .inv₁)))
    )
  ; cap =
    ( path
      (λ t → iso (p r) .from (inB .cap .fst .at t))
      (cong (iso (p r) .from) (inB .cap .fst .atO))
      (trans
        (appCong (iso (p r) .inv₁))
        (cong (iso (p r) .from) (inB .cap .fst .atI)))
    , λ t u →
      trans
        (cong (iso (p r) .from) (inB .cap .snd t u))
        (symm (appCong (iso (p r) .inv₁)))
    )
  }
  where
  tube : [ φ ] → Π (B ∘ p)
  tube u i = iso (p i) .to (f u i)

  base : B (p r) [ φ ↦ tube ◆ r ]
  base = (iso (p r) .to a₀ , λ u → cong (iso (p r) .to) (ex u))

  inB = β r p φ tube base

----------------------------------------------------------------------
-- Strict composition
----------------------------------------------------------------------
record SComp (r : Int) (A : Int → Set) (φ : CofProp) (f : [ φ ] → Π A)
  (x₀ : A r [ φ ↦ f ◆ r ]) : Set
  where
  field
    comp : (s : Int) → isCofProp (r ≡ s) → A s [ φ ↦ f ◆ s ]
    cap : (c : isCofProp (r ≡ r)) → comp r c .fst ≡ x₀ .fst

open SComp public

isSFib : ∀{ℓ} {Γ : Set ℓ} (A : Γ → Set) → Set ℓ
isSFib {Γ = Γ} A = ∀ r p φ f x₀ → SComp r (A ∘ p) φ f x₀

strictifyFib : ∀ {ℓ} {Γ : Set ℓ} (A : Γ → Set) → isFib A → isSFib A
strictifyFib A α r p φ f x₀ =
  record
  { comp = λ s c →
    (strong s c .fst , λ v → strong s c .snd ∣ inl v ∣)
  ; cap = λ c →
    trans
      (atI (α r p φ f x₀ .cap .fst))
      (trans
        (cong (λ q → fix r c q I) (uip (c .snd .fst (c .snd .snd refl)) refl))
        (symm (strong r c .snd ∣ inr (c .snd .snd refl) ∣)))
  }
  where
  module _ (s : Int) (c : isCofProp (r ≡ s))
    where

    r≡s = c .fst

    weak : A (p s) [ φ ↦ f ◆ s ]
    weak = α r p φ f x₀ .comp s

    f' : [ φ ] → (k : Int) → A (p s)
    f' v k = f v s

    fix : r ≡ s → Int → A (p s)
    fix eq k = subst (A ∘ p) eq (α r p φ f x₀ .cap .fst .at k)

    fixed-f' : [ φ ∨ r≡s ] → Int → A (p s)
    fixed-f' =
      ∨-rec φ r≡s f' (fix ∘ c .snd .fst)
        (λ u eq → funext (λ k →
          trans (cong (subst (A ∘ p) (c .snd .fst eq)) (α r p φ f x₀ .cap .snd k u))
          (symm (substfam (c .snd .fst eq) (f u)))))

    weak' : Σ x₁ ∈ (A (p s)) , (fixed-f' ◆ O ↗ x₁)
    weak' =
      ( weak .fst
      , ∨-elimEq φ r≡s
          (weak .snd)
          (λ eq →
            trans
              (substfam (c .snd .fst eq) (λ k → α r p φ f x₀ .comp k .fst))
              (cong (subst (A ∘ p) (c .snd .fst eq)) (α r p φ f x₀ .cap .fst .atO))
              )
      )

    strong : Σ x₂ ∈ (A (p s)) , (fixed-f' ◆ I ↗ x₂)
    strong = α O (λ _ → p s) (φ ∨ r≡s) fixed-f' weak' .comp I
 
