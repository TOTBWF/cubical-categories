{-# OPTIONS --cubical --safe #-}

open import Categories.Category

module Categories.CommutativeDiagram.Square {o ℓ} (C : Category o ℓ) where

open import Cubical.Foundations.Prelude

open Category C

private
  variable
    X Y : Obj
    a a′ a″ b b′ b″ c c′ c″ : X ⇒ Y
    f g h i : X ⇒ Y


CommutativeSquare : ∀ {A B C D} → (f : A ⇒ B) (g : A ⇒ C) (h : B ⇒ D) (i : C ⇒ D) → Set _
CommutativeSquare f g h i = h ∘ f ≡ i ∘ g
