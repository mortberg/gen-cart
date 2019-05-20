{-# OPTIONS --rewriting #-}

open import prelude

module pushout where

postulate
  Pushout : {ℓ m k : Level} {A : Set ℓ} {B : Set m} {C : Set k}
    (f : A → B) (g : A → C) → Set (ℓ ⊔ m ⊔ k)


module _ {ℓ m k : Level} {A : Set ℓ} {B : Set m} {C : Set k}
  {f : A → B} {g : A → C}
  where
  postulate

    left : B → Pushout f g
    right : C → Pushout f g
    push : (a : A) → (left (f a) ≡ right (g a))

  module _ {j : Level} (X : Pushout f g → Set j)
    (l : (b : B) → X (left b))
    (r : (c : C) → X (right c))
    (p : (a : A) → subst X (push a) (l (f a)) ≡ r (g a))
    where
      postulate
        pushout-elim : (z : Pushout f g) → (X z)

        pushout-l-β : (b : B) → (pushout-elim (left b) ≡ l b)
        pushout-r-β : (c : C) → (pushout-elim (right c) ≡ r c)

        {-# REWRITE pushout-l-β #-}
        {-# REWRITE pushout-r-β #-}

  pushout-rec : {j : Level} {X : Set j} (l : B → X) (r : C → X) →
                (p : (a : A) → l (f a) ≡ r (g a)) → Pushout f g → X
  pushout-rec {X = X} l r p =
    pushout-elim (λ _ → X) l r
                 (λ a → trans (p a) (substconst X (push a) (l (f a))))
