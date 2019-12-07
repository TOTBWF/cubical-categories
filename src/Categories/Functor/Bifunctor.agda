{-# OPTIONS --cubical --safe #-}

module Categories.Functor.Bifunctor where

open import Level

open import Cubical.Foundations.Prelude

open import Categories.Category
open import Categories.Category.Product

open import Categories.Functor.Core

private
  variable
    o ℓ o′ ℓ′ o″ ℓ″ : Level

Bifunctor : (𝓒 : Category o ℓ) →
            (𝓓 : Category o′ ℓ′) →
            (𝓔 : Category o″ ℓ″) → Set (o ⊔ ℓ ⊔ o′ ⊔ ℓ′ ⊔ o″ ⊔  ℓ″)
Bifunctor 𝓒 𝓓 𝓔 = Functor (𝓒 × 𝓓) 𝓔

-- Some notational tricks:

module _ {𝓒 : Category o ℓ} (⊗ : Bifunctor 𝓒 𝓒 𝓒) where
  open Category 𝓒
  _⊗⟨-⟩ : Obj → Functor 𝓒 𝓒 
  X ⊗⟨-⟩ = record
    { F₀ = {!!}
    ; F₁ = {!!}
    ; identity = {!!}
    ; homomorphism = {!!}
    }
