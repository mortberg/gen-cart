{-

CCHM style identity types.

-}
{-# OPTIONS --rewriting #-}
module Data.id where

open import prelude
open import interval
open import cofprop
open import fibrations
open import Data.paths
open import Data.products
open import cofreplacement

postulate
  _∧_ : (φ : CofProp) → ([ φ ] → CofProp) → CofProp
  [∧] : ∀ φ ψ → [ φ ∧ ψ ] ≡ Σ [ φ ] ([_] ∘ ψ)

  {-# REWRITE [∧] #-}

  cofExt : {φ ψ : CofProp} → ([ φ ] → [ ψ ]) → ([ ψ ] → [ φ ]) → φ ≡ ψ

----------------------------------------------------------------------
-- Id types
----------------------------------------------------------------------

Constancy : {A : Set} {a a' : A} → a ~ a' → Set
Constancy {a = a} p = Σ φ ∈ CofProp , ([ φ ] → (i : Int) → p .at i ≡ a)

Constancy' : ∀{ℓ}{Γ : Set ℓ}(A : Γ → Set)
  → Σ (Σ Γ (λ x → A x × A x)) (Path A) → Set
Constancy' A ((x , (a , a')) , p) = Constancy p

Id : {A : Set} → A → A → Set
Id a a' = Σ (a ~ a') Constancy

Id' : ∀{ℓ}{Γ : Set ℓ}(A : Γ → Set) → Σ x ∈ Γ , A x × A x → Set
Id' {_} {Γ} A = Σ' (Path A) (Constancy' A)

pathToId : {A : Set} {a a' : A} → a ~ a' → Id a a'
pathToId p = (p , ⊥ , ⊥→)

ConstancyExt : {A : Set} {a a' : A} {p p' : a ~ a'} (eq : p ≡ p')
  {u : Constancy p}{v : Constancy p'}
  → u .fst ≡ v .fst
  → subst (λ p → Constancy p) eq u ≡ v
ConstancyExt refl refl  =
  Σext refl (funext λ _ → funext λ _ → uipImp)

IdExt : {A : Set} {a a' : A} {id id' : Id a a'}
  → id .fst .at ≡ id' .fst .at → id .snd .fst ≡ id' .snd .fst → id ≡ id'
IdExt refl refl =
  let pathEq = (PathExt refl) in
  Σext pathEq (ConstancyExt pathEq refl)

IdExtDep : {I : Set} {A : Set} {a a' : I → A}
  {i i' : I} (r : i ≡ i')
  {id : Id (a i) (a' i)} {id' : Id (a i') (a' i')}
  → id .fst .at ≡ id' .fst .at
  → id .snd .fst ≡ id' .snd .fst
  → subst (λ i → Id (a i) (a' i)) r id ≡ id'
IdExtDep refl = IdExt

SingletonExt : {A : Set} {a : A}
  {sing sing' : Σ a' ∈ A , Id a a'}
  → sing .snd .fst .at ≡ sing' .snd .fst .at
  → sing .snd .snd .fst ≡ sing' .snd .snd .fst
  → sing ≡ sing'
SingletonExt {sing = sing} {sing'} refl eq =
  Σext
    (trans (sing' .snd .fst .atI) (symm (sing .snd .fst .atI)))
    (IdExtDep
      (trans (sing' .snd .fst .atI) (symm (sing .snd .fst .atI)))
      refl
      eq)

FibIdId : {A : Int → Set} → isFib A → isFib (Id' A)
FibIdId {A} α = FibΣ {B = Constancy' A} (FibPath {A = A} α) β
  where
  β : isFib (Constancy' A)
  β r p φ f ((ψ₀ , cst₀) , ex) =
    record
    { comp = λ s →
      ( ( φ ∧ (λ u → f u s .fst)
        , λ {(u , v) → f u s .snd v}
        )
      , λ u →
        ConstancyExt {p = p s .snd} refl
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
        (ConstancyExt {p = p r .snd} refl
          (cofExt
            (∨-rec (φ ∧ (λ u → f u r .fst)) (⊥ ∧ (λ _ → ψ₀))
              id
              (O≠I ∘ fst)
              (λ _ _ → cofIsProp (φ ∧ (λ u → f u r .fst)) _ _))
            (∣_∣ ∘ inl)))
        (ConstancyExt {p = p r .snd} refl
          (cofExt
            (∨-rec (φ ∧ (λ u → f u r .fst)) ((I ≈I) ∧ (λ _ → ψ₀))
              (λ {(u , v) → subst ([_] ∘ fst) (ex u) v})
              snd
              (λ _ _ → cofIsProp ψ₀ _ _))
            (λ w → ∣ inr (refl , w) ∣)))
      , λ t u →
        ConstancyExt {p = p r .snd} refl
          (cofExt
            (λ v → ∣ inl (u , v) ∣)
            (∨-rec (φ ∧ (λ u → f u r .fst)) ((t ≈I) ∧ (λ _ → ψ₀))
              (λ {(u' , v) → subst (λ x → [ f x r .fst ]) (cofIsProp φ _ _) v})
              (λ {(refl , w) → subst ([_] ∘ fst) (symm (ex u)) w})
              (λ _ _ → cofIsProp (f u r .fst) _ _)))
      )
    }

FibId : ∀{ℓ}{Γ : Set ℓ}{A : Γ → Set} → isFib A → isFib (Id' A)
FibId {_} {Γ} {A} α e p = FibIdId (reindex A α (fst ∘ p)) e (id× p)
  where
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
  reindex (Id' A) (FibId α) (ρ ×id) ≡ FibId (reindex A α ρ)
reindexId A α ρ = refl

----------------------------------------------------------------------
-- Refl and J
----------------------------------------------------------------------

module _ {ℓ} {Γ : Set ℓ} (A : Γ → Set) where

  refl1 : ∀ x → (a : A x) → Id' A (x , (a , a))
  refl1 x a = refl~ a , O ≈O , λ _ _ → refl

  private
    module J (α : isFib A) (x : Γ)
      (X : Σ' (Σ' A (A ∘ fst)) (Id' A) x → Set) (χ : isFib X)
      (x₀ : (a : A x) → X ((a , a) , refl1 x a))
      (a b : A x) (id : Id a b)
      where

      p = id .fst
      φ = id .snd .fst
      cst = id .snd .snd

      Xa : (Σ a' ∈ A x , Id a a') → Set
      Xa (b , id) = X ((a , b) , id)

      compSq : (i : Int) → _
      compSq i =
        strictifyFib _ α O (λ _ → x) (φ ∨ i ≈O ∨ i ≈I)
          (∨-rec φ (i ≈O ∨ i ≈I)
            (λ u _ → a)
            (OI-rec i
              (λ _ _ → a)
              (λ _ j → p .at j))
            (λ u → OI-elim i _
              (λ _ → refl)
              (λ _ → funext λ j → symm (cst u j))))
          ( a
          , ∨-elimEq φ (i ≈O ∨ i ≈I)
            (λ _ → refl)
            (OI-elim i _
              (λ _ → refl)
              (λ _ → p .atO))
          )

      b' : Int → A x
      b' i = compSq i .comp I (O≡IsCofProp I) .fst

      id' : (i : Int) → Id a (b' i)
      id' i =
        ( path
          (λ j → compSq i .comp j (O≡IsCofProp j) .fst)
          (compSq i .cap (O≡IsCofProp O))
          refl
        , (i ≈O) ∨ φ
        , ∨-rec (i ≈O) φ
          (λ {refl j →
            symm (compSq O .comp j (O≡IsCofProp j) .snd ∣ inr ∣ inl refl ∣ ∣)})
          (λ u j →
            symm (compSq i .comp j (O≡IsCofProp j) .snd ∣ inl u ∣))
          (λ _ _ → funext λ _ → uipImp)
        )

      id'φ : [ φ ] → (i : Int) → _≡_ {A = Σ a' ∈ A x , Id a a'} (a , refl1 x a) (b' i , id' i)
      id'φ u i =
        SingletonExt
          (funext λ j → compSq i .comp j (O≡IsCofProp j) .snd ∣ inl u ∣)
          (cofExt (λ _ → ∣ inr u ∣) (λ _ → refl))

      id'O : _≡_ {A = Σ a' ∈ A x , Id a a'} (a , refl1 x a) (b' O , id' O)
      id'O =
       SingletonExt
        (funext λ j → compSq O .comp j (O≡IsCofProp j) .snd ∣ inr ∣ inl refl ∣ ∣)
        (cofExt (λ _ → ∣ inl refl ∣) (λ _ → refl))

      id'I : _≡_ {A = Σ a' ∈ A x , Id a a'} (b , id) (b' I , id' I)
      id'I =
        SingletonExt
          (funext λ j → compSq I .comp j (O≡IsCofProp j) .snd ∣ inr ∣ inr refl ∣ ∣)
          (cofExt
            (λ u → ∣ inr u ∣)
            (∨-rec (I ≈O) φ (λ I≡O → O≠I (symm I≡O)) (λ u → u) (λ _ _ → cofIsProp φ _ _)))

      compX = χ O (λ i → (a , b' i) , id' i) φ
        (λ u i → subst Xa (id'φ u i) (x₀ a))
        ( subst Xa id'O (x₀ a)
        , λ u → cong₂ (subst Xa) (uip (id'φ u O) id'O) refl
        )

      result : X ((a , b) , id)
      result = subst Xa (symm id'I) (compX .comp I .fst)

  J : (α : isFib A) (x : Γ)
    → triv-cofibration {B = Σ' (Σ' A (A ∘ fst)) (Id' A) x} (λ a → ((a , a) ,  refl1 x a))
  J α x .j X χ x₀ ((a , b) , id) = result
    where
    open J α x X χ x₀ a b id

  J α x .upper-tri X χ x₀ a =
    {!eq!} -- takes forever?
    where
    open J α x X χ x₀ a a (refl1 x a)

    eq : subst Xa (symm id'I) (compX .comp I .fst) ≡ x₀ a
    eq =
      adjustSubstEq {A = Σ a' ∈ A x , Id a a'} Xa
        refl (id'φ refl I)
        (symm id'I) refl
        (symm (compX .comp I .snd refl))
