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
    𝓒 𝓓 𝓔 : Category o ℓ

record Monad (𝓒 : Category o ℓ) : Set (o ⊔ ℓ) where
  field
    T : Endofunctor 𝓒
    η : NaturalTransformation id T
    μ : NaturalTransformation (T ∘F T) T

  module T = Functor T
  open T public using () renaming (F₀ to T₀; F₁ to T₁)


  field
    assoc : μ ∘ᵛ (T ∘ˡ μ) ∘ᵛ ()
