{-# OPTIONS --rewriting #-}
module Data.inductive-fiber {ℓ} {Γ : Set ℓ} {A B : Γ → Set} (f : ∀ x → A x → B x) where

open import prelude
open import interval
open import cofprop
open import fibrations
open import wtypesred
open import hcomp-coe
open import fiberwise-total
open import retract
open import cofreplacement
open import fibreplacement
open import Data.products
open import Data.paths

FR' : (x : Γ) → (b : B x) → Set
FR' x = FR (f x)

ΣFR'IsHFib : isFib B → isHFib (Σ' B (uncurry FR'))
ΣFR'IsHFib β r x φ h σ₀ =
  FibΣ {Γ = Unit}
    (reindex B β (λ _ → x))
    (reindex (FR' x) (FRIsFib (f x)) (λ {(_ , b) → b}))
    r _
    φ h σ₀

module _ (α : isFib A) (β : isFib B) where

  eval : {x : Γ} → (b : B x) → FR' x b → A x
  eval {x} = curry
    (quotIsTrivCofibration (f x) .j _ (reindex A α (λ _ → x)) id)

  quotEval : {x : Γ} (b : B x) (c : FR' x b)
    → _~_ {A = Σ (B x) (FR' x)} (quot _ (eval b c)) (b , c)
  quotEval {x} = curry
    (quotIsTrivCofibration (f x) .j
      (λ {(b , c) → quot _ (eval b c) ~ (b , c)})
      (reindex
        (Path (λ _ → Σ (B x) (FR' x)))
        (FibPath sigFib)
        (λ {(b , c) → tt , quot (f x) (eval b c) , (b , c)}))
      (λ a →
        eqToPath
          (trans
            (cong (λ emp → (f x a , ixsup (FRPoly _) (dom a) emp))
              (funext λ _ → funext ∅-elim))
            (cong (quot (f x))
              (quotIsTrivCofibration (f x) .upper-tri
                _ (reindex A α (λ _ → x)) id a)))))
    where
    sigFib : isFib (λ _ → Σ (B x) (FR' x))
    sigFib =
      FibΣ {B = λ {(_ , b) → FR' x b}}
        (reindex B β (λ _ → x))
        (reindex (FR' x) (FRIsFib (f x)) (λ {(_ , b) → b}))

  ΣFR'IsFib : isFib (Σ' B (uncurry FR'))
  ΣFR'IsFib =
    homotopyRetractIsFib (Σ' B (uncurry FR')) A
      (ΣFR'IsHFib β)
      α
      (λ {x (b , c) → eval b c})
      (λ x a → quot _ a)
      (λ {x (b , c) → quotEval b c})

  FR'IsFib : isFib (uncurry FR')
  FR'IsFib =
    fiberwise+total→isFib B FR' β (λ x → FRIsFib (f x)) ΣFR'IsFib
