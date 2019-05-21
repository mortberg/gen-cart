{-# OPTIONS --rewriting #-}
module Data.id3 {ℓ} {Γ : Set ℓ} (A : Γ → Set) where

open import prelude
open import Data.products
open import interval
open import cofprop
open import fibrations
open import fiberwise-total
open import cofreplacement
open import fibreplacement
open import Data.products
open import Data.inductive-fiber

Δ : (x : Γ) → A x → A x × A x
Δ x a = (a , a)

Id3 : Σ x ∈ Γ , A x × A x → Set
Id3 = uncurry (FR' Δ)

refl3 : (x : Γ) (a : A x) → Id3 (x , (a , a))
refl3 x a = quot (Δ x) a .snd

refl3IsTrivCofibration : (x : Γ)
  → triv-cofibration (λ a → ((a , a) , refl3 x a))
refl3IsTrivCofibration x = quotIsTrivCofibration (Δ x)

Id3IsFib : isFib A → isFib Id3
Id3IsFib α = FR'IsFib Δ α αα
  where
  αα = FibΣ {A = A} {B = λ {(x , _) → A x}} α (reindex A α fst)

