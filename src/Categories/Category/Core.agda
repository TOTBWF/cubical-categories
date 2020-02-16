{-# OPTIONS --cubical --safe #-}
module Categories.Category.Core where

open import Level using (Level; _⊔_; suc)

open import Relation.Binary hiding (_⇒_)

open import Cubical.Foundations.Prelude


  

record Category (o ℓ : Level) : Set (suc (o ⊔ ℓ)) where
  eta-equality
  infix  4 _⇒_
  infixr 9 _∘_

  field
    Obj : Set o
    _⇒_ : Rel Obj ℓ

  field
    id  : ∀ {A} → (A ⇒ A)
    _∘_ : ∀ {A B C} → (B ⇒ C) → (A ⇒ B) → (A ⇒ C)

    hom-is-set : ∀ {A B} → isSet (A ⇒ B)
    assoc      : ∀ {A B C D} {f : A ⇒ B} {g : B ⇒ C} {h : C ⇒ D} → (h ∘ g) ∘ f ≡ h ∘ (g ∘ f)
    identityˡ  : ∀ {A B} {f : A ⇒ B} → id ∘ f ≡ f
    identityʳ  : ∀ {A B} {f : A ⇒ B} → f ∘ id ≡ f

  ∘-congˡ : ∀ {A B C} {f : A ⇒ B} {f′ : A ⇒ B} {g : B ⇒ C} → f ≡ f′ → g ∘ f ≡ g ∘ f′
  ∘-congˡ {g = g} f≡f′ = cong (λ k → g ∘ k) f≡f′

  ∘-congʳ : ∀ {A B C} {f : B ⇒ C} {f′ : B ⇒ C} {g : A ⇒ B} → f ≡ f′ → f ∘ g ≡ f′ ∘ g
  ∘-congʳ {g = g} f≡f′ = cong (λ k → k ∘ g) f≡f′
