{-# OPTIONS --cubical --safe #-}

module Categories.Morphism where

open import Level
open import Cubical.Foundations.Prelude

open import Categories.Category
open import Categories.Morphism.Core

private
  variable
    o ℓ : Level

_[_iso_] : (𝓒 : Category o ℓ) →
           {A B : Category.Obj 𝓒} →
           (from : Category._⇒_ 𝓒 A B) →
           (to : Category._⇒_ 𝓒 B A) → Set ℓ
_[_iso_] = Iso

_[_≅_] : (𝓒 : Category o ℓ) → (A B : Category.Obj 𝓒) → Set ℓ
_[_≅_] = _≅_
