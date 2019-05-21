{-

Definition of trivial fibrations and proof that they are actually
fibrations.

-}
{-# OPTIONS --rewriting #-}
module trivialfib where

open import prelude
open import cofprop
open import fibrations
open import interval
open import equivs

O≡I-elim : ∀ {ℓ} {i : Int} {D : [ i ≈O ] → [ i ≈I ] → Set ℓ} (v : i ≡ O) (u : i ≡ I) → D v u
O≡I-elim v u = O≠I (trans u (symm v))

path-contr : {A : Set} (ac : SContr A) (a a' : A) → (SContr (a ~ a'))
path-contr {A} ac a a' φ u =
  path (λ i → fst (ac (φ' i) (u' i)))
       (symm (snd (ac (φ' O) (u' O)) ∣ inr ∣ inl refl ∣ ∣))
       (symm (snd (ac (φ' I) (u' I)) ∣ inr ∣ inr refl ∣ ∣))
  , λ x → PathExt (funext (λ i → snd (ac (φ' i) (u' i)) ∣ inl x ∣))
  where
    φ' = λ i → φ ∨ (i ≈O) ∨ (i ≈I)
    u' : (i : Int) → [ φ' i ] → A
    u' i = ∨-rec φ ((i ≈O) ∨ (i ≈I)) (λ x → u x .at i) (OI-rec i (λ _ → a) (λ _ → a'))
           (λ w v → ∨-elim (i ≈O) (i ≈I) (λ v' → u w .at i ≡ OI-rec i (λ _ → a) (λ _ → a') v')
             (λ {refl → (u w) .atO}) (λ {refl → (u w) .atI}) O≡I-elim v)


scontr-iso : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} (f : A → B) (g : B → A)
             (f-g : (b : B) → f (g b) ≡ b) (g-f : (a : A) → g (f a) ≡ a) →
             SContr A → SContr B
scontr-iso f g f-g g-f acontr =
  λ φ u → (f (fst (acontr φ (g ∘ u)))) ,
  λ x → trans (cong f (snd (acontr φ (g ∘ u)) x)) (symm (f-g (u x)))

isTrivialFib : ∀ {ℓ ℓ'} {Γ : Set ℓ} (B : Γ → Set ℓ') → (Set (ℓ ⊔ ℓ'))
isTrivialFib {Γ = Γ} B = (γ : Γ) → SContr (B γ)

SFiber : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} (f : A → B) (b : B) → (Set (ℓ ⊔ ℓ'))
SFiber {A = A} f b = Σ A λ a → f a ≡ b

map-isTrivialFib : {A : Set} {B : Set} (f : A → B) → Set
map-isTrivialFib f = isTrivialFib (SFiber f)

TrivialFib-tomap : {Γ : Set} (A : Γ → Set) → (isTrivialFib A) → (map-isTrivialFib (fst {A = Γ} {B = A}))
TrivialFib-tomap {Γ} A tf γ = scontr-iso (λ a → (γ , a) , refl) (λ {((γ' , a'), p) → subst A p a'})
  (λ {((γ' , a'), p) → lemma p a'}) (λ a → refl) (tf γ)
  where
    lemma : {γ γ' : Γ} (p : γ' ≡ γ) (a' : A γ') → (((γ , subst A p a') , refl) ≡ ((γ' , a') , p))
    lemma refl a' = refl

TrivialFib-∘ : {A B C : Set} (g : B → C) (f : A → B) → (map-isTrivialFib g) → (map-isTrivialFib f) →
               (map-isTrivialFib (g ∘ f))
TrivialFib-∘ g f gtf ftf c φ u = (a , (trans p (cong g q))) , (λ x → Σext (Σeq₁ (abdy x)) (uip _ _))
  where
    u' : [ φ ] → SFiber g c
    u' x = f (fst (u x)) , snd (u x)

    bp0 = gtf c φ u'

    b = fst (fst bp0)
    p = snd (fst bp0)
    bbdy = snd bp0

    aq0 = ftf b φ (λ x → (fst (u x)) , Σeq₁ (bbdy x))
    a = fst (fst aq0)
    q = snd (fst aq0)
    abdy = snd aq0


SContrToPaths : {A : Int → Set} (tf : isTrivialFib A) (a : A O) (a' : A I) → (a ~~ a')
SContrToPaths {A} tf a a' =
  path p e0 e1
  where
    φ : Int → CofProp
    φ i = (i ≈O) ∨ (i ≈I)

    u : (i : Int) → [ φ i ] → A i
    u i x = OI-rec i ((λ p → subst A (symm p) a)) ((λ q → subst A (symm q) a')) x

    pc = λ i → tf i (φ i) (u i)
    p = λ i → fst (pc i)

    e0 : p O ≡ a
    e0 = symm (snd (pc O) ∣ inl refl ∣)
    
    e1 : p I ≡ a'
    e1 = symm (snd (pc I) ∣ inr refl ∣)

TrivialFib-isFib : ∀ {ℓ} {Γ : Set ℓ} (A : Γ → Set) → (isTrivialFib A) → (isFib A)
TrivialFib-isFib A tf r p φ f x₀ =
  record { comp = co ; cap = ca }
  where
    co = λ i → tf (p i) φ (λ x → f x i)
    
    φ' = λ i → φ ∨ (i ≈O) ∨ (i ≈I)
    u : (i : Int) → [ φ' i ] → A (p r)
    u i x = ∨-rec φ ((i ≈O) ∨ (i ≈I)) (λ x' → f x' r)
                  endpoints
                  (λ v w → ∨-elim (i ≈O) (i ≈I) (λ w' → f v r ≡ endpoints w')
                                     (λ p → snd (co r) v)
                                     (λ p → snd x₀ v)
                                     O≡I-elim w)
                  x
        where
          endpoints = OI-rec i ((λ _ → fst (co r))) ((λ _ → fst x₀))

    pth = λ i → fst (tf (p r) (φ' i) (u i))
    bdy = λ i → snd (tf (p r) (φ' i) (u i))

    ca = path pth (symm (bdy O ∣ inr ∣ inl refl ∣ ∣))
                  (symm (bdy I ∣ inr ∣ inr refl ∣ ∣)) ,
         λ i x → bdy i ∣ inl x ∣

