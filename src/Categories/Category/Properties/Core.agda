{-# OPTIONS --cubical --safe #-}

open import Categories.Category.Core

module Categories.Category.Properties.Core {o ℓ} (C : Category o ℓ) where

open import Cubical.Foundations.Prelude

open Category C

id-unique : ∀ {a} {f : a ⇒ a} → (∀ {b} → (g : a ⇒ b) → g ∘ f ≡ g) → f ≡ id
id-unique {f = f} g∘f≡g = 
  f ≡⟨ sym identityˡ ⟩
  id ∘ f ≡⟨ g∘f≡g id ⟩
  id ∎

id-comm : ∀ {a b} {f : a ⇒ b} → f ∘ id ≡ id ∘ f
id-comm {f = f} =
  f ∘ id ≡⟨ identityʳ ⟩
  f ≡⟨ sym identityˡ ⟩
  id ∘ f ∎
