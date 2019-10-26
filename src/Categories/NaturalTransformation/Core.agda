{-# OPTIONS --cubical --safe #-}
module Categories.NaturalTransformation.Core where

open import Level

open import Cubical.Foundations.Prelude

open import Categories.Category
open import Categories.Functor.Core renaming (id to idF)

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

  field
    η : ∀ X → D [ F₀ X , G₀ X ]
    commute : ∀ {X Y} → (f : C [ X , Y ]) → D [ G₁ f ∘ η X ] ≡ D [ η Y ∘ F₁ f ]

id : ∀ {F :  Functor C D} → NaturalTransformation F F
id {C = C} {D = D} {F} = record
  { η = λ _ → D.id
  ; commute = λ f →
    D [ F₁ f ∘ D.id ] ≡⟨ D.identityʳ ⟩
    F₁ f ≡⟨ sym D.identityˡ ⟩
    D [ D.id ∘ F₁ f ] ∎
  }
  where
    module C = Category C
    module D = Category D
    module F = Functor F
    open F

_∘ᵛ_ : ∀ {F G H : Functor C D} →
         NaturalTransformation G H → NaturalTransformation F G → NaturalTransformation F H
_∘ᵛ_ {C = C} {D = D} {F} {G} {H} X Y = record
  { η = λ q → D [ X.η q ∘ Y.η q ]
  ; commute = λ {q} {p} f →
    D [ H₁ f ∘ D [ X.η q ∘ Y.η q ] ] ≡⟨ sym D.assoc ⟩
    D [ D [ H₁ f ∘ X.η q ] ∘ Y.η q ] ≡⟨ cong (λ a → a D.∘ Y.η q) (X.commute f) ⟩
    D [ D [ X.η p ∘ G₁ f ] ∘ Y.η q ] ≡⟨ D.assoc ⟩
    D [ X.η p ∘ D [ G₁ f ∘ Y.η q ] ] ≡⟨ cong (λ a → (X.η p) D.∘ a) (Y.commute f) ⟩
    D [ X.η p ∘ D [ Y.η p ∘ F₁ f ] ] ≡⟨ sym D.assoc ⟩
    D [ D [ X.η p ∘ Y.η p ] ∘ F₁ f ] ∎
  }
  where
    module D = Category D

    module X = NaturalTransformation X
    module Y = NaturalTransformation Y

    module F = Functor F
    module G = Functor G
    module H = Functor H
    open F
    open G renaming (F₀ to G₀; F₁ to G₁)
    open H renaming (F₀ to H₀; F₁ to H₁)
