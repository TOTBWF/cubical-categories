{-# OPTIONS --cubical --safe #-}
module Categories.Monad.Core where

open import Level

open import Cubical.Foundations.Prelude

open import Categories.Category
open import Categories.Functor.Core renaming (id to Id)
open import Categories.NaturalTransformation.Core renaming (id to idN)

private
  variable
    o ℓ : Level

record Monad (𝓒 : Category o ℓ) : Set (o ⊔ ℓ) where
  field
    T : Endofunctor 𝓒
    η : NaturalTransformation Id T
    μ : NaturalTransformation (T ∘F T) T

  module T = Functor T
  open T public using () renaming (F₀ to T₀; F₁ to T₁)
  module η = NaturalTransformation η
  module μ = NaturalTransformation μ
  module 𝓒 = Category 𝓒

  open Category 𝓒

  field
    assoc     : ∀ {X} → μ.η X ∘ T₁ (μ.η X)  ≡ μ.η X ∘ μ.η (T₀ X)
    identityˡ : ∀ {X} → μ.η X ∘ T₁ (η.η X) ≡ id
    identityʳ : ∀ {X} → μ.η X ∘ η.η (T₀ X) ≡ id
