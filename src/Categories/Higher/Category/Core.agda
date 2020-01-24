{-# OPTIONS --cubical --safe #-}
module Categories.Higher.Category.Core where

open import Level using (Level; _⊔_; suc)

open import Relation.Binary hiding (_⇒_)

open import Data.Nat using (ℕ; _+_)

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels


record [∞,1]-Category (o ℓ : Level) : Set (suc (o ⊔ ℓ)) where
  eta-equality
  infix  4 _⇒_
  infixr 9 _∘_

  field
    Obj : Set o
    _⇒_ : Rel Obj ℓ

    id  : ∀ {A} → (A ⇒ A)
    _∘_ : ∀ {A B C} → (B ⇒ C) → (A ⇒ B) → (A ⇒ C)

  field
    assoc      : ∀ {A B C D} {f : A ⇒ B} {g : B ⇒ C} {h : C ⇒ D} → (h ∘ g) ∘ f ≡ h ∘ (g ∘ f)
    identityˡ  : ∀ {A B} {f : A ⇒ B} → id ∘ f ≡ f
    identityʳ  : ∀ {A B} {f : A ⇒ B} → f ∘ id ≡ f

record [_,1]-Category (n : ℕ) (o ℓ : Level) : Set (suc (o ⊔ ℓ)) where
  eta-equality
  field
    cat : [∞,1]-Category o ℓ
  open [∞,1]-Category cat public
  field
    hom-is-hLevel : ∀ {A B} → isOfHLevel (n + 1) (A ⇒ B)

1-Category : ∀ (o ℓ : Level) → Set (suc (o ⊔ ℓ))
1-Category o ℓ = [ 1 ,1]-Category o ℓ
