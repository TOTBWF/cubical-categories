{-# OPTIONS --cubical --safe #-}
open import Categories.Category

-- Reasoning Combinators when dealing with commutative diagrams.
module Categories.Reasoning.Commutative {o ℓ} (C : Category o ℓ) where

open import Cubical.Foundations.Prelude
open import Categories.Reasoning.Hom C
open Category C
