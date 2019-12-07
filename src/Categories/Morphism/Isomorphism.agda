{-# OPTIONS --cubical --safe #-}

open import Categories.Category

module Categories.Morphism.Isomorphism {o ℓ} (𝓒 : Category o ℓ) where

open import Cubical.Foundations.Prelude

open Category 𝓒

private
  variable
    A B C : Obj

record Iso (isoˡ : A ⇒ B) (isoʳ : B ⇒ A) : Set ℓ where
  field
    inverseˡ : isoˡ ∘ isoʳ ≡ id
    inverseʳ : isoʳ ∘ isoˡ ≡ id
infix 4 _≃_
record _≃_ (a : Obj) (b : Obj) : Set ℓ where
  field
    isoˡ : a ⇒ b
    isoʳ : b ⇒ a
    inverseˡ : isoˡ ∘ isoʳ ≡ id
    inverseʳ : isoʳ ∘ isoˡ ≡ id


