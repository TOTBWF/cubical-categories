{-# OPTIONS --cubical --safe #-}
open import Categories.Category

module Categories.Functor.Core where

open import Level

open import Cubical.Foundations.Prelude


private
  variable
    o ℓ o′ ℓ′ o′′ ℓ′′ : Level
    
record Functor (C : Category o ℓ) (D : Category o′ ℓ′) : Set (o ⊔ ℓ ⊔ o′ ⊔ ℓ′) where
  private module C = Category C
  private module D = Category D

  field
    F₀ : C.Obj → D.Obj
    F₁ : ∀ {A B} → C [ A , B ] → D [ F₀ A , F₀ B ]

    identity : ∀ {A} → F₁ (C.id {A}) ≡ D.id
    homomorphism : ∀ {X Y Z} {f : C [ X , Y ]}
                             {g : C [ Y , Z ]}
                             → F₁ (C [ g ∘ f ]) ≡ D [ F₁ g ∘ F₁ f ]

Endofunctor : Category o ℓ → Set _
Endofunctor C = Functor C C

id : ∀ {C : Category o ℓ} → Endofunctor C
id {C = C} = record
  { F₀           = λ x → x
  ; F₁           = λ f → f
  ; identity     = refl
  ; homomorphism = refl
  }

_∘F_ : ∀ {C : Category o ℓ} {D : Category o′ ℓ′} {E : Category o′′ ℓ′′}
    → Functor D E → Functor C D → Functor C E
_∘F_ {C = C} {D = D} {E = E} F G = record
  { F₀ = λ x → F₀ (G₀ x)
  ; F₁ = λ f → F₁ (G₁ f)
  ; identity =
             F₁ (G₁ C.id) ≡⟨ cong F₁ G.identity ⟩
             F₁ D.id ≡⟨ F.identity ⟩
             E.id ∎
  ; homomorphism = λ {X} {Y} {Z} {f = f} {g = g} →
             F₁ (G₁ (C [ g ∘ f ])) ≡⟨ cong F₁ G.homomorphism ⟩
             F₁ (D [ G₁ g ∘ G₁ f ] ) ≡⟨ F.homomorphism ⟩
             E [ F₁ (G₁ g) ∘ F₁ (G₁ f) ] ∎
  }
  where
    module C = Category C
    module D = Category D
    module E = Category E

    module F = Functor F
    module G = Functor G
    open F
    open G renaming (F₀ to G₀; F₁ to G₁)

