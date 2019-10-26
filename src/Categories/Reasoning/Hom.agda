{-# OPTIONS --cubical --safe #-}
open import Categories.Category

-- Reasoning Combinators when dealing with composition.
module Categories.Reasoning.Hom {o ℓ} (C : Category o ℓ) where

open import Cubical.Foundations.Prelude
open Category C

private
  variable
    A B : Obj

infixr 4 _⟩∘⟨_ refl⟩∘⟨_
infixl 5 _⟩∘⟨refl

_⟩∘⟨_ : ∀ {M} {f h : M ⇒ B} {g i : A ⇒ M} → f ≡ h → g ≡ i → f ∘ g ≡ h ∘ i
_⟩∘⟨_ f≡h g≡i = cong₂ _∘_ f≡h g≡i

refl⟩∘⟨_ : ∀ {M} {f : M ⇒ B} {g i : A ⇒ M} → g ≡ i → f ∘ g ≡ f ∘ i
refl⟩∘⟨_ {f = f} g≡i = cong (f ∘_) g≡i

_⟩∘⟨refl : ∀ {M} {f h : M ⇒ B} {g : A ⇒ M} → f ≡ h → f ∘ g ≡ h ∘ g
_⟩∘⟨refl {g = g} f≡h = cong (_∘ g) f≡h
