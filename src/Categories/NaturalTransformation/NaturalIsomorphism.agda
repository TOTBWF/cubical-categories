{-# OPTIONS --cubical --safe #-}
module Categories.NaturalTransformation.NaturalIsomorphism where

open import Level

open import Cubical.Foundations.Prelude

open import Categories.Category
open import Categories.Functor.Core
open import Categories.NaturalTransformation.Core

import Categories.Morphism.Isomorphism as Iso

private
  variable
    o ℓ o′ ℓ′ o″ ℓ″ : Level
    𝓒 𝓓 : Category o ℓ

record NaturalIsomorphism {𝓒 : Category o ℓ}
                             {𝓓 : Category o′ ℓ′}
                             (F G : Functor 𝓒 𝓓) : Set (o ⊔ ℓ ⊔ o′ ⊔ ℓ′) where
  private
    module F = Functor F
    module G = Functor G

  field
    F⇒G : NaturalTransformation F G
    F⇐G : NaturalTransformation G F

  open NaturalTransformation F⇒G renaming (η to ηˡ; commute to commuteˡ)
  open NaturalTransformation F⇐G renaming (η to ηʳ; commute to commuteˡ)

  field
    iso : ∀ X → Iso.Iso 𝓓 (ηˡ X) (ηʳ X)

infix 4 _≃_
-- commonly used short-hand in CT for NaturalIsomorphism
_≃_ : (F G : Functor 𝓒 𝓓) → Set _
_≃_ = NaturalIsomorphism
