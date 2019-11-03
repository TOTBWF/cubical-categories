{-# OPTIONS --cubical --safe #-}
open import Categories.Category

module Categories.Functor.Core where

open import Level

open import Cubical.Foundations.Prelude

private
  variable
    o ℓ o′ ℓ′ o″ ℓ″ o‴ ℓ‴ : Level
    
record Functor (𝓒 : Category o ℓ) (𝓓 : Category o′ ℓ′) : Set (o ⊔ ℓ ⊔ o′ ⊔ ℓ′) where
  private module 𝓒 = Category 𝓒
  private module 𝓓 = Category 𝓓

  field
    F₀ : 𝓒.Obj → 𝓓.Obj
    F₁ : ∀ {A B} → 𝓒 [ A , B ] → 𝓓 [ F₀ A , F₀ B ]

    identity : ∀ {A} → F₁ (𝓒.id {A}) ≡ 𝓓.id
    homomorphism : ∀ {A B C} {f : 𝓒 [ A , B ]}
                             {g : 𝓒 [ B , C ]}
                             → F₁ (𝓒 [ g ∘ f ]) ≡ 𝓓 [ F₁ g ∘ F₁ f ]
Endofunctor : Category o ℓ → Set _
Endofunctor 𝓒 = Functor 𝓒 𝓒

id : ∀ {𝓒 : Category o ℓ} → Endofunctor 𝓒
id  = record
  { F₀           = λ x → x
  ; F₁           = λ f → f
  ; identity     = refl
  ; homomorphism = refl
  }

infixr 9 _∘F_

-- Functor Composition.
-- NOTE: Using the reasoning combinators from `cubical` makes
-- the proofs look nicer, but they add an extra `refl` on
-- to the path. This makes other proofs much more painful,
-- so we should avoid doing so.
_∘F_ : ∀ {𝓒 : Category o ℓ} {𝓓 : Category o′ ℓ′} {𝓔 : Category o″ ℓ″}
    → Functor 𝓓 𝓔 → Functor 𝓒 𝓓 → Functor 𝓒 𝓔
_∘F_ F G = record
  { F₀ = λ x → F₀ (G₀ x)
  ; F₁ = λ f → F₁ (G₁ f)
  ; identity = (cong F₁ G.identity) ∙ F.identity
  ; homomorphism = λ {X} {Y} {Z} {f = f} {g = g} → (cong F₁ G.homomorphism) ∙ F.homomorphism
  }
  where
    module F = Functor F
    module G = Functor G
    open F
    open G renaming (F₀ to G₀; F₁ to G₁)
