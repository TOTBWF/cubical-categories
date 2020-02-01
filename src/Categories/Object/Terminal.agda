{-# OPTIONS --cubical --safe #-}
open import Categories.Category

module Categories.Object.Terminal {o ℓ} (𝓒 : Category o ℓ) where

open import Level
open import Cubical.Foundations.Prelude

open Category 𝓒

record Terminal : Set (o ⊔ ℓ) where
  field
    ⊤        : Obj
    !        : ∀ {A} → (A ⇒ ⊤)
    !-unique : ∀ {A} → (f : A ⇒ ⊤) → (! ≡ f)
