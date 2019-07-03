{-

This file provides a stable interface to the formalization of the
paper:

  Unifying Cubical Models of Univalent Type Theory

by Evan Cavallo, Anders Mörtberg and Andrew Swan.

PLEASE DO NOT RENAME THIS FILE - its name is referenced in the article
about this formalization.

-}
module unifying-summary where

-- | Section 2.1: The interval and Path types.
-- (axioms 1 and 2)
open import interval


-- | Section 2.2: Cofibrant propositions (Φ is called CofProp)
-- (axioms 3, 4, 5 and 7)
open import cofprop


-- | Section 2.3: Fibration structures (WComp and SComp)
open import fibrations


-- | Section 2.3.1: ABCFHL fibrations
open import ABCFHL


-- | Section 2.3.2: CCHM fibrations
open import CCHM


-- | Section 2.4: Fibration structures for basic type formers

-- Σ-types:
open import Data.products

-- Π-types:
open import Data.functions

-- Path types:
open import Data.paths

-- Natural numbers
open import Data.nat


-- | Section 2.5: Glueing

-- Definition 16 (Glueing) and Theorem 17 (Fibrant Glue types)
open import glueing.core

-- Axiom 6
open import strictness-axioms

-- Strict Glue types (SGlue)
open import glueing.strict

-- Alignment for SGlue
open import glueing.aligned


-- | Section 2.5.1: Univalence
open import univalence


-- | Section 3.2: Cofibration and trivial fibration awfs
open import cofreplacement


-- | Section 3.3: Trivial cofibration and fibration awfs
open import fibreplacement


-- | Section 4: Identity types and higher inductive types

-- CCHM style identity types using a dominance on CofProp
open import Data.id

-- Identity types from cofibrant replacement
open import Data.id2

-- Identity types from fibrant replacement
open import Data.id3
