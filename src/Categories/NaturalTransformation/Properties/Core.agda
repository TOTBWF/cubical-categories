{-# OPTIONS --cubical --safe #-}
module Categories.NaturalTransformation.Properties.Core where

open import Level

open import Cubical.Foundations.Prelude

open import Categories.Category
open import Categories.Functor.Core using (Functor)
open import Categories.NaturalTransformation.Core

private
  variable
    o ℓ o′ ℓ′ : Level

module _ {𝓒 : Category o ℓ} {𝓓 : Category o′ ℓ′} {F G : Functor 𝓒 𝓓} {α β : NaturalTransformation F G} where
  private
    module α = NaturalTransformation α
    module β = NaturalTransformation β
    module F = Functor F
    module G = Functor G
    open F
    open G renaming (F₀ to G₀; F₁ to G₁)
    module 𝓓 = Category 𝓓

    open NaturalTransformation

  nat-trans-commute-eq : α.η ≡ β.η → α ≡ β
  nat-trans-commute-eq p i .η = p i
  nat-trans-commute-eq p i .commute f = rem i
    where
    rem : PathP (λ i → 𝓓 [ p i _ ∘ F₁ f ] ≡ 𝓓 [ G₁ f ∘ p i _ ]) (α.commute f) (β.commute f)
    rem = toPathP (𝓓.hom-is-set _ _ _ _)


module _ {𝓒 : Category o ℓ} {𝓓 : Category o′ ℓ′} {F G : Functor 𝓒 𝓓} (α : NaturalTransformation F G) where
  private
    module α = NaturalTransformation α
    module 𝓓 = Category 𝓓
  ∘ᵛ-identityˡ : id ∘ᵛ α ≡ α
  ∘ᵛ-identityˡ = nat-trans-commute-eq (λ i X → 𝓓.identityˡ {f = α.η X} i)

  ∘ᵛ-identityʳ : α ∘ᵛ id ≡ α
  ∘ᵛ-identityʳ = nat-trans-commute-eq (λ i X → 𝓓.identityʳ {f = α.η X} i)

module _ {𝓒 : Category o ℓ} {𝓓 : Category o′ ℓ′} {F G H I : Functor 𝓒 𝓓}
         (α : NaturalTransformation H I) (β : NaturalTransformation G H) (γ : NaturalTransformation F G) where
  private
    module α = NaturalTransformation α
    module β = NaturalTransformation β
    module γ = NaturalTransformation γ
    module 𝓓 = Category 𝓓

  ∘ᵛ-assoc : (α ∘ᵛ β) ∘ᵛ γ ≡ α ∘ᵛ (β ∘ᵛ γ)
  ∘ᵛ-assoc = nat-trans-commute-eq λ i X → 𝓓.assoc {f = γ.η X} {g = β.η X} {h = α.η X} i
