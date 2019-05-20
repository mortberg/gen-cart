{-

W-types with reductions.

-}
{-# OPTIONS --rewriting #-}
module wtypesred {ℓ} where

open import prelude
open import cof

record Poly : Set (lsuc ℓ) where
  field
    Constr : Set ℓ
    Arity : Constr → Set ℓ
    Red : Constr → Cof
    ev : (c : Constr) → [ Red c ] → (Arity c)

module _ (P : Poly) where
  open Poly P

  postulate
    WR : Set ℓ

    sup : (c : Constr) → (Arity c → WR) → WR
    red : (c : Constr) → (α : Arity c → WR) →
             (x : [ Red c ]) → (sup c α ≡ α (ev c x))

    WR-elim : ∀ {ℓ'} (X : WR → Set ℓ')
              (s : (c : Constr) (α : Arity c → WR) → ((a : Arity c) → X (α a)) → X (sup c α)) →
              (r : (c : Constr) (α : Arity c → WR) → (u : (a : Arity c) → X (α a)) →
                   (x : [ Red c ]) → subst X (red c α x) (s c α u) ≡ u (ev c x))
              (w : WR) → X w

    WR-elim-β : ∀ {ℓ'} (X : WR → Set ℓ')
                (s : (c : Constr) (α : Arity c → WR) → ((a : Arity c) → X (α a)) → X (sup c α))
                (r : (c : Constr) (α : Arity c → WR) → (u : (a : Arity c) → X (α a)) →
                  (x : [ Red c ]) → subst X (red c α x) (s c α u) ≡ u (ev c x))
                (c : Constr) (α : Arity c → WR) (u : (a : Arity c) → X (α a)) →
                WR-elim X s r (sup c α) ≡ s c α (λ a → WR-elim X s r (α a))

record IxPoly (I : Set) : Set (lsuc ℓ) where
  field
    Constr : I → Set ℓ
    Arity : {i : I} → Constr i → I → Set ℓ
    Red : {i : I} → Constr i → Cof
    ev : {i : I} → (c : Constr i) → [ Red c ] → (Arity c i)

module _ {I : Set} (P : IxPoly I) where
  open IxPoly P

  postulate
    IxWR : I → Set ℓ

    ixsup : {i : I} (c : Constr i) → ((j : I) → Arity c j → IxWR j) → IxWR i
    ixred : {i : I} (c : Constr i) (α : (j : I) → Arity c j → IxWR j) →
             (x : [ Red c ]) → (ixsup c α ≡ α i (ev c x))

    IxWR-elim : ∀ {ℓ'} (X : (i : I) → IxWR i → Set ℓ')
      (s : {i : I} (c : Constr i) (α : (j : I) → Arity c j → IxWR j)
           → ((j : I) (a : Arity c j) → X j (α j a)) → X i (ixsup c α))
      (r : {i : I} (c : Constr i) (α : (j : I) → Arity c j → IxWR j)
           (u : (j : I) (a : Arity c j) → X j (α j a))
           (x : [ Red c ]) → subst (X i) (ixred c α x) (s c α u) ≡ u i (ev c x))
      (i : I) (w : IxWR i) → X i w

    IxWR-elim-β : ∀ {ℓ'} (X : (i : I) → IxWR i → Set ℓ')
      (s : {i : I} (c : Constr i) (α : (j : I) → Arity c j → IxWR j)
           → ((j : I) (a : Arity c j) → X j (α j a)) → X i (ixsup c α))
      (r : {i : I} (c : Constr i) (α : (j : I) → Arity c j → IxWR j)
           (u : (j : I) (a : Arity c j) → X j (α j a))
           (x : [ Red c ]) → subst (X i) (ixred c α x) (s c α u) ≡ u i (ev c x))
      (i : I) (c : Constr i) (α : (j : I) → Arity c j → IxWR j) (u : (j : I) (a : Arity c j) → X j (α j a))
      → IxWR-elim X s r i (ixsup c α) ≡ s c α (λ j a → IxWR-elim X s r j (α j a))

    {-# REWRITE IxWR-elim-β #-}
