{-

Identity types constructed using cofibrant replacement (factorisation
of a map as a cofibration followed by trivial fibration).

In this version the cofibrant replacement is constructed by assuming W
types with reductions rather than ax7 and extensionality for cofibrant
propositions.

-}


{-# OPTIONS --rewriting #-}
module Data.id2 (Γ : Set) (A : Γ → Set) where

open import prelude
open import cofreplacement
open import Data.products
open import interval
open import cofprop
open import fibrations
open import trivialfib
open import Data.paths

Path' : Γ → Set
Path' γ = Int → A γ

r-path : {γ : Γ} → A γ → Path' γ
r-path a = λ _ → a

eO-path : {γ : Γ} → Path' γ → A γ
eO-path p = p O

{- Endpoint maps are both trivial fibrations (we only show eO) -}
eO-path-tf : {γ : Γ} → (isFib A) → map-isTrivialFib (eO-path {γ})
eO-path-tf {γ} afib a φ u =
  ((λ i → fst (comp sc i (O≡IsCofProp i))) ,
  cap sc (O≡IsCofProp O)) ,
  λ x → Σext (funext (λ i → snd (comp sc i (O≡IsCofProp i)) x)) (uip _ _)
  where
    sc = strictifyFib A afib O (λ _ → γ) φ (λ x → fst (u x)) (a , (λ x → snd (u x)))

{- Id2' has the wrong type to work as identity type, but is more convenient to work with. -}
Id2' : Γ → Set
Id2' γ = cof-replace.M (r-path {γ})

{- A bunch more utility functions. -}
{- This one is a variant of the reflexivity map. -}
r' : {γ : Γ} → A γ → Id2' γ
r' = cof-replace.L r-path

{- Endpoint projection. -}
eO' : {γ : Γ} → Id2' γ → A γ
eO' = eO-path ∘ cof-replace.R r-path

eO-tf : {γ : Γ} (afib : isFib A) → map-isTrivialFib (eO' {γ})
eO-tf afib = TrivialFib-∘ eO-path (cof-replace.R r-path) (eO-path-tf afib) (cof-replace.R-tf r-path)

r-cof : {γ : Γ} → cofibration (r' {γ})
r-cof = cof-replace.L-cof r-path

Path-fmap : {B C : Set} {b b' : B} (f : B → C) → (b ~ b') → (f b ~ f b')
Path-fmap f (path p bO bI) = path (f ∘ p) (cong f bO) (cong f bI)

private
  extract-pth : (x : Σ (Σ γ ∈ Γ , A γ × A γ) (Path A)) → Path' (fst (fst x))
  extract-pth ((γ , (a , a')) , pth) = at pth

{- Actual identity type (with correct type) is Id2 here. -}
Id2 : Σ γ ∈ Γ , (A γ × A γ) → Set
Id2 = Σ' (Path A) (λ x → cof-replace.M₀ r-path (extract-pth x))

{- Reflexivity map -}
r : (γ : Γ) → (a : A γ) → Id2 (γ , (a , a))
r γ a = (refl~ a) , cof-replace.L₀ r-path a

{- The identity type is a fibration over Γ, A γ, A γ. -}
Id2-isFib : (afib : isFib A) → isFib Id2
Id2-isFib afib = FibΣ {Γ = Σ γ ∈ Γ , (A γ × A γ)} {A = Path A}
  {B = λ x → cof-replace.M₀ r-path (extract-pth x)} (FibPath afib)
  (TrivialFib-isFib (λ x → cof-replace.M₀ r-path (extract-pth x))
                    (λ x → cof-replace.M₀-isTrivialFib r-path (extract-pth x)))


module _ (afib : isFib A) (γ : Γ) where
  open cofibration (r-cof {γ})

  id-path' : (z : Id2' γ) → (r' (eO' z) , refl) ~ (z , refl)
  id-path' =
    j (λ z → (r' (eO' z) , refl) ~ (z , refl))
             (λ z' → path-contr (eO-tf afib (eO' z')) _ _)
             λ a → refl~ _


  id-path : (z : Id2' γ) → r' (eO' z) ~ z
  id-path z = Path-fmap fst (id-path' z)

  id-refl' : (a : A γ) → (id-path' (r' a) ≡ refl~ _)
  id-refl' a = upper-tri (((λ z → (r' (eO' z) , refl) ~ (z , refl))))
                          (λ z' → path-contr (eO-tf afib (eO' z')) _ _)
                          (λ a₁ → refl~ _) a

  id-refl : (a : A γ) → (id-path (r' a) ≡ refl~ _)
  id-refl a = cong (Path-fmap fst) (id-refl' a)


{- Leibniz exponential from endpoint inclusion -}
δ₀⇒ : {ℓ' : Level} {Γ' : Set ℓ'} (C : Γ' → Set) →
      Σ (Int → Γ') (λ p → C (p O)) → Set
δ₀⇒ C (p ,  c₀) = Σ ((i : Int) → C (p i)) λ p' → p' O ≡ c₀

{- Leibniz exponential with an endpoint sends fibrations to trivial fibrations. -}
path-lift-tf : {ℓ' : Level} {Γ' : Set ℓ'} (C : Γ' → Set) (cfib : isFib C) → isTrivialFib (δ₀⇒ C)
path-lift-tf C cfib (p , c₀) φ u =
    ((λ i → fst (comp sc i (O≡IsCofProp i)))
      , cap sc (O≡IsCofProp O))
    , (λ x → Σext (funext (λ i → snd (comp sc i (O≡IsCofProp i)) x)) (uip _ _))
    where
      u' : [ φ ] → (i : Int) → C (p i)
      u' = fst ∘ u

      sc = strictifyFib C cfib O p φ u' (c₀ , (λ x → snd (u x)))


{- If a map is both a cofibration and strong deformation retract, then it is a 
   trivial cofibration.
-}
sdr-cof-to-tc : {A B : Set} (r : A → B) (s : B → A) (s-r : (a : A) → s (r a) ≡ a)
                (r-s : (b : B) → r (s b) ~ b) →
                ((a : A) → r-s (r a) ≡ path (λ _ → r a) (cong r (symm (s-r a))) refl) →
                (cofibration r) → (triv-cofibration r)
sdr-cof-to-tc {A} {B} r s s-r r-s str rcof =
  record { j = j
         ; upper-tri = ut }
  where
    module _ (X : B → Set) (xfib : isFib X) (x₀ : (a : A) → X (r a)) where
      str' : (a : A) → (i : Int) → (r-s (r a) .at i ≡ r a)
      str' a = subst (λ pth → (i : Int) → pth .at i ≡ r a) (symm (str a)) λ _ → refl

      X' : B → Set
      X' b = δ₀⇒ X ((at (r-s b)) , (subst X (symm (atO (r-s b))) (x₀ (s b))))

      X'-tf : isTrivialFib X'
      X'-tf = λ b φ u → path-lift-tf X xfib (((at (r-s b)) , (subst X (symm (atO (r-s b))) (x₀ (s b))))) φ u

      {- NB: Both lemmas use axiom K. -}
      lemma1 : {a a' : A} (q : a' ≡ a) {b : B} (l : b ≡ r a) (p : b ≡ r a') →
               (subst X (symm l) (x₀ a) ≡ (subst X (symm p) (x₀ a')))
      lemma1 refl refl refl = refl

      lemma2 : {b b' : B} (p q : b ≡ b') → (x : X b') → subst X p (subst X (symm q) x) ≡ x 
      lemma2 refl refl x = refl

      x₀' : (a : A) → X' (r a)
      x₀' a = (λ i → subst X (symm (str' a i)) (x₀ a))
              , lemma1 (s-r a) (str' a O) (atO (r-s (r a)))

      j = λ b → subst X (atI (r-s b)) (fst (cofibration.j rcof X' X'-tf x₀' b) I)

      ut = λ a → trans (lemma2 (atI (r-s (r a))) (str' a I) (x₀ a))
           (cong (λ x → subst X (atI (r-s (r a))) (fst x I)) (cofibration.upper-tri rcof X' X'-tf x₀' a))




module _ {γ : Γ} (afib : isFib A) (C : Id2' γ → Set) (cfib : isFib C)
  (c₀ : (a : A γ) → C (r' a)) where

  open triv-cofibration (sdr-cof-to-tc r' eO' (λ a → refl)
                                       (λ b → id-path afib γ b)
                                       (id-refl afib γ) (cof-replace.L-cof r-path))

  J' : (z : Id2' γ) → C z
  J' = j C cfib c₀


  J-comp' : (a : A γ) → J' (r' a) ≡ c₀ a
  J-comp' = upper-tri C cfib c₀


{- J rule formatted for the actual identity type - Id2 -}
module _ (afib : isFib A) (C : Σ (Σ γ ∈ Γ , A γ × A γ) Id2 → Set)
  (cfib : isFib C) (c₀ : (γ : Γ) → (a : A γ) → C ((γ , (a , a)) , (r γ a))) where

    C' : (γ : Γ) → Id2' γ → Set
    C' γ (p , z) = C ((γ , ((p O) , (p I))) , (path p refl refl) , z)

    c₀' : (γ : Γ) → (a : A γ) → C' γ (r' a)
    c₀' γ a = c₀ γ a

    cfib' : (γ : Γ) → isFib (C' γ)
    cfib' γ = reindex C cfib (λ {(p , z) → (γ , (p O) , (p I)) , (path p refl refl) , z})

    J : (z : Σ (Σ γ ∈ Γ , A γ × A γ) Id2) → C z
    J ((γ , a , a') , (pth , z)) =
      subst C (symm (lemma (at pth) (atO pth) (atI pth) z))
              (J' afib (C' γ) (cfib' γ) (c₀' γ) ((at pth) , z))
      where
        lemma : {b b' : A γ} (α : Int → A γ) (p : α O ≡ b) (q : α I ≡ b') →
          (z' : _) →
          ((γ , b , b') , (path α p q , z')) ≡ ((γ , α O , α I) , (path α refl refl , z'))
        lemma α refl refl z' = refl
