{-# OPTIONS --cubical --safe #-}
module Setoid where

open import Cubical.Foundations.Prelude hiding (_≡⟨_⟩_)

open import Level

record Category (o ℓ : Level) : Set (suc (o ⊔ ℓ)) where

  infix 4 _⇒_
  infixr 9 _∘_

  field
    Obj : Set o
    _⇒_ : Obj → Obj → Set ℓ

    id : ∀ {A} → A ⇒ A
    _∘_ : ∀ {A B C} → (B ⇒ C) → (A ⇒ B) → (A ⇒ C)

  field
    assoc : ∀ {A B C D} {f : A ⇒ B} {g : B ⇒ C} {h : C ⇒ D} → (h ∘ g) ∘ f ≡ h ∘ (g ∘ f)
    identityˡ : ∀ {A B} {f : A ⇒ B} → id ∘ f ≡ f
    identityʳ : ∀ {A B} {f : A ⇒ B} → f ∘ id ≡ f
    ∘-resp-≡  : ∀ {A B C} {f h : B ⇒ C} {g i : A ⇒ B} → f ≡ h → g ≡ i → f ∘ g ≡ h ∘ i

infix 10  _[_,_] _[_∘_]

_[_,_] : ∀ {o ℓ} → (C : Category o ℓ) → (X : Category.Obj C) → (Y : Category.Obj C) → Set ℓ
_[_,_] = Category._⇒_

_[_∘_] : ∀ {o ℓ} → (C : Category o ℓ) → ∀ {X Y Z} (f : C [ Y , Z ]) → (g : C [ X , Y ]) → C [ X , Z ]
_[_∘_] = Category._∘_

record Functor {o ℓ o′ ℓ′} (C : Category o ℓ) (D : Category o′ ℓ′) : Set (o ⊔ ℓ ⊔ o′ ⊔ ℓ′) where
  private module C = Category C
  private module D = Category D

  field
    F₀ : C.Obj → D.Obj
    F₁ : ∀ {A B} → C [ A , B ] → D [ F₀ A , F₀ B ]

    identity : ∀ {A} → F₁ (C.id {A}) ≡ D.id
    homomorphism : ∀ {X Y Z} {f : C [ X , Y ]} {g : C [ Y , Z ]} → D [ F₁ g ∘ F₁ f ] ≡ F₁ (C [ g ∘ f ])
    F-resp-≡ : ∀ {A B} {f g : C [ A , B ]} → f ≡ g → F₁ f ≡ F₁ g

record NaturalTransformation {o ℓ o′ ℓ′} {C : Category o ℓ} {D : Category o′ ℓ′} (F G : Functor C D) : Set (o ⊔ ℓ ⊔ o′ ⊔ ℓ′) where
  private
    module C = Category C
    module D = Category D
    module F = Functor F
    module G = Functor G
  open F using (F₀; F₁)
  open G using () renaming (F₀ to G₀; F₁ to G₁)
  field
    τ : ∀ X → D [ F₀ X , G₀ X ]
    commute : ∀ {A B} → D [ τ B ∘