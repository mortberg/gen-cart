module Data.nat where

open import prelude
open import interval
open import cof
open import fibrations
open import hcomp-coe

open import Agda.Builtin.Nat public
  using (zero; suc)
  renaming (Nat to ℕ)

pred : ℕ → ℕ
pred zero    = zero
pred (suc x) = x

natDec : (x y : ℕ) → (x ≡ y) ⊎ ¬ (x ≡ y)
natDec zero zero       = inl refl
natDec zero (suc y)    = inr λ ()
natDec (suc x) zero    = inr λ ()
natDec (suc x) (suc y) with natDec x y
... | inl p = inl (cong suc p)
... | inr p = inr (λ q → p (cong pred q))

isFibNat : {Γ : Set} → isFib {Γ = Γ} (λ _ → ℕ)
isFibNat = constHFib→isFib ℕ (decEq→isHFib _ natDec)

fibNat : Fib ℕ
fibNat = _ , isFibNat
