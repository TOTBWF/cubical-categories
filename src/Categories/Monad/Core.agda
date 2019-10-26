{-# OPTIONS --cubical --safe #-}
module Categories.Monad.Core where

open import Level

open import Cubical.Foundations.Prelude

open import Categories.Category
open import Categories.Functor.Core
open import Categories.NaturalTransformation.Core renaming (id to idN)

private
  variable
    o ℓ o′ ℓ′ o″ ℓ″ : Level
    C D E : Category o ℓ

record Monad (C : Category o ℓ) : Set (o ⊔ ℓ) where
  field
    T : Endofunctor C
    η : NaturalTransformation id T
    μ : NaturalTransformation (T ∘F T) T

  module T = Functor T
  open T public using () renaming (F₀ to T₀; F₁ to T₁)

