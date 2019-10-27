{-# OPTIONS --cubical --safe #-}
module Categories.NaturalTransformation.Core where

open import Level

open import Cubical.Foundations.Prelude

open import Categories.Category
open import Categories.Functor.Core renaming (id to idF)
open import Categories.Functor.Properties.Core
import Categories.CommutativeDiagram.Square as Square

private
  variable
    o ℓ o′ ℓ′ o″ ℓ″ : Level
    C D E : Category o ℓ


record NaturalTransformation {C : Category o ℓ}
                             {D : Category o′ ℓ′}
                             (F G : Functor C D) : Set (o ⊔ ℓ ⊔ o′ ⊔ ℓ′) where
  private
    module C = Category C
    module D = Category D
    module F = Functor F
    module G = Functor G
  open F using (F₀; F₁)
  open G using () renaming (F₀ to G₀; F₁ to G₁)
  open Square D

  field
    η : ∀ X → D [ F₀ X , G₀ X ]
    commute : ∀ {X Y} → (f : C [ X , Y ]) → CommutativeSquare (F₁ f) (η X) (η Y) (G₁ f)

id : ∀ {F :  Functor C D} → NaturalTransformation F F
id {C = C} {D = D} {F} = record
  { η = λ _ → D.id
  ; commute = λ f → 
      D [ D.id ∘ F₁ f ] ≡⟨ D.identityˡ ⟩
      F₁ f ≡⟨ sym D.identityʳ ⟩
      D [ F₁ f ∘ D.id ] ∎
  }
  where
    module C = Category C
    module D = Category D
    module F = Functor F
    open F

-- Vertical Composition
_∘ᵛ_ : ∀ {F G H : Functor C D} →
         NaturalTransformation G H → NaturalTransformation F G → NaturalTransformation F H
_∘ᵛ_ {C = C} {D = D} {F} {G} {H} X Y = record
  { η = λ q → D [ X.η q ∘ Y.η q ]
  ; commute = λ {q} {p} f → glue-□ (X.commute f) (Y.commute f)
  }
  where
    module D = Category D
    open import Categories.Reasoning.Commutative D

    module X = NaturalTransformation X
    module Y = NaturalTransformation Y

    module F = Functor F
    module G = Functor G
    module H = Functor H
    open F
    open G renaming (F₀ to G₀; F₁ to G₁)
    open H renaming (F₀ to H₀; F₁ to H₁)

-- Left Composition of a Functor
_∘ˡ_ : ∀ {G H : Functor C D} (F : Functor D E) →
         NaturalTransformation G H →
         NaturalTransformation (F ∘F G) (F ∘F H)
_∘ˡ_ {E = E} F α = record
  { η = λ X → F₁ (η X)
  ; commute =  λ f → [ F ]-resp-square (commute f)
  }
  where
    open Functor F
    open NaturalTransformation α
