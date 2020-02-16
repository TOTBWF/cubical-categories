{-# OPTIONS --cubical --safe #-}
open import Categories.Category

module Categories.Morphism.Core {o ℓ} (𝓒 : Category o ℓ) where

open import Level
open import Cubical.Foundations.Prelude
open import Cubical.Core.Glue

open Category 𝓒

record Iso {A B : Obj} (from : A ⇒ B) (to : B ⇒ A) : Set ℓ where
  field
    isoˡ : to ∘ from ≡ id
    isoʳ : from ∘ to ≡ id

infix 4 _≅_
record _≅_ (A B : Obj): Set ℓ where
  field
    from : A ⇒ B
    to   : B ⇒ A
    iso  : Iso from to
  open Iso iso public

-- Identity morphisms form an isomorphism
id-iso : ∀ {A} → A ≅ A
id-iso = record
  { from = id
  ; to = id
  ; iso = record
    { isoˡ = identityˡ
    ; isoʳ = identityʳ
    }
  }

≡-to-iso : ∀ {A B} → A ≡ B → A ≅ B
≡-to-iso {A} {B} eq = subst (λ X → A ≅ X) eq id-iso
