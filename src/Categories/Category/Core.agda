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

  ∘-congˡ : ∀ {A B C} {f : A ⇒ B} {f′ : A ⇒ B} {g : B ⇒ C} → f ≡ f′ → g ∘ f ≡ g ∘ f′
  ∘-congˡ {g = g} f≡f′ = cong (λ k → g ∘ k) f≡f′

  ∘-congʳ : ∀ {A B C} {f : B ⇒ C} {f′ : B ⇒ C} {g : A ⇒ B} → f ≡ f′ → f ∘ g ≡ f′ ∘ g
  ∘-congʳ {g = g} f≡f′ = cong (λ k → k ∘ g) f≡f′


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
SET : ∀ o → Category (suc o) o
SET o = record
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
