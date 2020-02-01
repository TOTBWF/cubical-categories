{-# OPTIONS --cubical --safe #-}
module Categories.Comonad.Core where

open import Level

open import Cubical.Foundations.Prelude

open import Categories.Category
open import Categories.Functor.Core renaming (id to Id)
open import Categories.NaturalTransformation.Core renaming (id to idN)

private
  variable
    o ℓ : Level

record Comonad (𝓒 : Category o ℓ) : Set (o ⊔ ℓ) where
  private module 𝓒 = Category 𝓒
  field
    W : Endofunctor 𝓒
    ε : NaturalTransformation W Id
    δ : NaturalTransformation W (W ∘F W)
  module W = Functor W
  open W public using () renaming (F₀ to W₀; F₁ to W₁)
  module ε = NaturalTransformation ε
  module δ = NaturalTransformation δ

  open Category 𝓒

  field
    assoc     : ∀ {X} → δ.η (W₀ X) ∘ δ.η X ≡ W₁ (δ.η X) ∘ δ.η X
    identityˡ : ∀ {X} → W₁ (ε.η X) ∘ δ.η X ≡ id
    identityʳ : ∀ {X} → ε.η (W₀ X) ∘ δ.η X ≡ id
