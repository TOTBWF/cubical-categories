{-
The free category for a quiver
-}

{-# OPTIONS --cubical --safe #-}

open import Level

open import Cubical.Foundations.Prelude

open import Categories.Category.Core

module Categories.Category.Construction.Free  where

module _ {o ℓ} (Obj : Set o) (_⇒_ : Obj → Obj → Set ℓ) where
  data _⇒⁺_ : Obj → Obj → Set (o ⊔ suc ℓ) where
    ⟦_⟧ : ∀ {A B} → (A ⇒ B) → A ⇒⁺ B
    id⁺ : ∀ {A} → A ⇒⁺ A
    _∘⁺_ : ∀ {A B C} → (B ⇒⁺ C) → (A ⇒⁺ B) → A ⇒⁺ C
    identity⁺ˡ : ∀ {A B} {f : A ⇒⁺ B} → id⁺ ∘⁺ f ≡ f 
    identity⁺ʳ : ∀ {A B} {f : A ⇒⁺ B} → f ∘⁺ id⁺ ≡ f 
    assoc⁺ : ∀ {A B C D} {f : A ⇒⁺ B} {g : B ⇒⁺ C} {h : C ⇒⁺ D} → (h ∘⁺ g) ∘⁺ f ≡ h ∘⁺ (g ∘⁺ f)


  Free : Category o (o ⊔ suc ℓ)
  Free = record
    { Obj = Obj
    ; _⇒_ = _⇒⁺_
    ; id = id⁺
    ; _∘_ = _∘⁺_
    ; assoc = assoc⁺
    ; identityˡ = identity⁺ˡ
    ; identityʳ = identity⁺ʳ 
    }
