{-# OPTIONS --rewriting #-}
module Data.id where

open import prelude
open import interval
open import cof
open import fibrations
open import Data.paths
open import Data.products

postulate
  _∧_ : (φ : Cof) → ([ φ ] → Cof) → Cof
  [∧] : ∀ φ ψ → [ φ ∧ ψ ] ≡ Σ [ φ ] ([_] ∘ ψ)

  {-# REWRITE [∧] #-}

  cofExt : {φ ψ : Cof} → ([ φ ] → [ ψ ]) → ([ ψ ] → [ φ ]) → φ ≡ ψ

----------------------------------------------------------------------
-- Id types
----------------------------------------------------------------------

Constancy : ∀{ℓ}{Γ : Set ℓ}(A : Γ → Set)
  → Σ (Σ Γ (λ x → A x × A x)) (Path A) → Set
Constancy A ((x , (a , a')) , p) = Σ φ ∈ Cof , ([ φ ] → (i : Int) → p .at i ≡ a)

Id : ∀{ℓ}{Γ : Set ℓ}(A : Γ → Set) → Σ x ∈ Γ , A x × A x → Set
Id {_} {Γ} A = Σ' (Path A) (Constancy A)

pathToId : ∀{ℓ}{Γ : Set ℓ}{A : Γ → Set}{x : Γ}{a a' : A x} → Path A (x , a' , a') → Id A (x , a' , a')
pathToId p = (p , O ≈I , λ u → O≠I u)

ConstancyExt : ∀{ℓ}{Γ : Set ℓ}(A : Γ → Set)
  {x : Γ} {a a' : A x}
  {p p' : a ~ a'} (eq : p ≡ p')
  {u : Constancy A ((x , (a , a')) , p)}
  {v : Constancy A ((x , (a , a')) , p')}
  → u .fst ≡ v .fst
  → subst ((λ p → Constancy A ((x , a , a') , p))) eq u ≡ v
ConstancyExt A {a = a} {p = p} {_} refl {(φ , _)} refl =
  Σext refl (funext λ _ → funext λ _ → uipImp)

IdExt :
  ∀{ℓ}{Γ : Set ℓ}
  {A : Γ → Set}
  {x : Γ}
  {a a' : A x}
  {id id' : Id A (x , (a , a'))}
  → ------------
  (id .fst .at ≡ id' .fst .at) → id .snd .fst ≡ id' .snd .fst → id ≡ id'
IdExt {_} {Γ} {A} {x} {a} {a'} {(p , u)} refl refl =
  let pathEq = (PathExt refl) in
  Σext pathEq (ConstancyExt A pathEq refl)

FibIdId : {A : Int → Set} → isFib A → isFib (Id A)
FibIdId {A} α = FibΣ {B = Constancy A} (FibPath {A = A} α) β
  where
  β : isFib (Constancy A)
  β r p φ f ((ψ₀ , cst₀) , ex) =
    record
    { comp = λ s →
      ( ( φ ∧ (λ u → f u s .fst)
        , λ {(u , v) → f u s .snd v}
        )
      , λ u →
        ConstancyExt A {p = snd (p s)} refl
          (cofExt
            (λ v → u , v)
            (λ {(u' , v) → subst (λ w → [ f w s .fst ]) (cofIsProp φ _ _) v}))
      )
    ; cap =
      ( path
        (λ t →
          ( (φ ∧ (λ u → f u r .fst)) ∨ ((t ≈I) ∧ (λ _ → ψ₀))
          , ∨-rec (φ ∧ (λ u → f u r .fst)) ((t ≈I) ∧ (λ _ → ψ₀))
              (λ {(u , v) → f u r .snd v})
              (λ {(refl , w) → cst₀ w})
              (λ _ _ → funext λ _ → uipImp)
          )
        )
        (ConstancyExt A {p = snd (p r)} _
          (cofExt
            (∨-rec (φ ∧ (λ u → f u r .fst)) ((O ≈I) ∧ (λ _ → ψ₀))
              id
              (O≠I ∘ fst)
              (λ _ _ → cofIsProp (φ ∧ (λ u → f u r .fst)) _ _))
            (∣_∣ ∘ inl)))
        (ConstancyExt A {p = snd (p r)} _
          (cofExt
            (∨-rec (φ ∧ (λ u → f u r .fst)) ((I ≈I) ∧ (λ _ → ψ₀))
              (λ {(u , v) → subst ([_] ∘ fst) (ex u) v})
              snd
              (λ _ _ → cofIsProp ψ₀ _ _))
            (λ w → ∣ inr (refl , w) ∣)))
      , λ t u →
        ConstancyExt A {p = snd (p r)} _
          (cofExt
            (λ v → ∣ inl (u , v) ∣)
            (∨-rec (φ ∧ (λ u → f u r .fst)) ((t ≈I) ∧ (λ _ → ψ₀))
              (λ {(u' , v) → subst (λ x → [ f x r .fst ]) (cofIsProp φ _ _) v})
              (λ {(refl , w) → subst ([_] ∘ fst) (symm (ex u)) w})
              (λ _ _ → cofIsProp (f u r .fst) _ _)))
      )
    }

FibId : ∀{ℓ}{Γ : Set ℓ}{A : Γ → Set} → isFib A → isFib (Id A)
FibId {_} {Γ} {A} α e p = FibIdId (reindex A α (fst ∘ p)) e (id× p) where
  id×_ : (p : Int → Σ Γ (λ x → A x × A x)) → Int → Σ Int (λ i → A (fst (p i)) × A (fst (p i)))
  (id× p) i = (i , snd (p i))

----------------------------------------------------------------------
-- Forming Id types is stable under reindexing
----------------------------------------------------------------------
reindexId :
  ∀{ℓ ℓ'}{Δ : Set ℓ}{Γ : Set ℓ'}
  (A : Γ → Set)
  (α : isFib A)
  (ρ : Δ → Γ)
  → ----------------------
  reindex (Id A) (FibId α) (ρ ×id) ≡ FibId (reindex A α ρ)
reindexId A α ρ = refl


-- EC : TODO J
