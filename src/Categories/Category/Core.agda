{-# OPTIONS --cubical --safe #-}
module Categories.Category.Core where

open import Level

open import Relation.Binary hiding (_⇒_)

open import Data.Unit.Polymorphic using (⊤; tt)

open import Cubical.Foundations.Prelude

record Category (o ℓ : Level) : Set (suc (o ⊔ ℓ)) where
  eta-equality
  infix  4 _⇒_
  infixr 9 _∘_

  field
    Obj : Set o
    _⇒_ : Rel Obj ℓ

    id  : ∀ {A} → (A ⇒ A)
    _∘_ : ∀ {A B C} → (B ⇒ C) → (A ⇒ B) → (A ⇒ C)

  field
    assoc     : ∀ {A B C D} {f : A ⇒ B} {g : B ⇒ C} {h : C ⇒ D} → (h ∘ g) ∘ f ≡ h ∘ (g ∘ f)
    identityˡ : ∀ {A B} {f : A ⇒ B} → id ∘ f ≡ f
    identityʳ : ∀ {A B} {f : A ⇒ B} → f ∘ id ≡ f

-- Some examples:

-- A single object category
One : ∀ {o ℓ} → Category o ℓ
One {o} {ℓ} = record
  { Obj = ⊤ o
  ; _⇒_ = λ _ _ → ⊤ ℓ
  ; id = tt
  ; _∘_ = λ _ _ → tt
  ; assoc = λ i → tt
  ; identityˡ = λ i → tt
  ; identityʳ = λ i → tt
  }

-- The category of sets
Sets : ∀ o → Category (suc o) o
Sets o = record
  { Obj = Set o
  ; _⇒_ = λ a b → a → b
  ; id = λ x → x
  ; _∘_ = λ f g x → f (g x)
  ; assoc = refl
  ; identityˡ = refl
  ; identityʳ = refl
  }


_ᵒᵖ : ∀ {o ℓ} → Category o ℓ → Category o ℓ
C ᵒᵖ = record
  { Obj = C.Obj
  ; _⇒_ = λ a b → b ⇒ a
  ; id = C.id
  ; _∘_ = λ f g → g ∘ f
  ; assoc = sym C.assoc
  ; identityˡ = C.identityʳ
  ; identityʳ = C.identityˡ
  }
  where
    module C = Category C
    open C

