{-# OPTIONS --cubical --safe #-}

module Categories.Functor.Properties.Core where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.GroupoidLaws renaming
  ( lUnit to ∙-unitˡ
  ; rUnit to ∙-unitʳ
  ; assoc to ∙-assoc
  )

open import Categories.Category
open import Categories.Functor.Core renaming (_∘F_ to _∘_; id to Id)

open import Level

private
  variable
    o ℓ : Level
    𝓒 𝓓 𝓔 𝓕 : Category o ℓ

module _ (F : Functor 𝓒 𝓓) where
  private
    module 𝓒 = Category 𝓒
    module 𝓓 = Category 𝓓


  open 𝓒 hiding (_∘_)
  module F = Functor F
  open F using (F₀; F₁)

  private
    variable
      A B E : Obj
      f g h i : A ⇒ B

  [_]-resp-∘ : 𝓒 [ f ∘ g ] ≡ h → 𝓓 [ F₁ f ∘ F₁ g ] ≡ F₁ h
  [_]-resp-∘ {f = f} {g = g} {h = h} eq = 
    𝓓 [ F₁ f ∘ F₁ g ] ≡⟨ sym F.homomorphism ⟩
    F₁ (𝓒 [ f ∘ g ]) ≡⟨ cong F₁ eq ⟩
    F₁ h ∎

  [_]-resp-square : 𝓒 [ h ∘ f ] ≡ 𝓒 [ i ∘ g ] → 𝓓 [ F₁ h ∘ F₁ f ] ≡ 𝓓 [ F₁ i ∘ F₁ g ]
  [_]-resp-square {h = h} {f = f} {i = i} {g = g} sq =
    𝓓 [ F₁ h ∘ F₁ f ] ≡⟨ sym F.homomorphism ⟩
    F₁ (𝓒 [ h ∘ f ]) ≡⟨ cong F₁ sq ⟩
    F₁ (𝓒 [ i ∘ g ]) ≡⟨ F.homomorphism ⟩
    𝓓 [ F₁ i ∘ F₁ g ] ∎

  ∘F-identityʳ : F ∘ Id ≡ F
  ∘F-identityʳ j = record
    { F₀ = F₀
    ; F₁ = F₁
    ; identity = λ i → ∙-unitˡ F.identity (~ j) i
    ; homomorphism = λ {_ _ _ f g} i → ∙-unitˡ (F.homomorphism {f = f} {g = g}) (~ j) i
    }
  
  ∘F-identityˡ : Id ∘ F ≡ F
  ∘F-identityˡ j = record
    { F₀ = F₀
    ; F₁ = F₁
    ; identity = λ i → ∙-unitʳ F.identity (~ j) i
    ; homomorphism = λ {_ _ _ f g} i → ∙-unitʳ (F.homomorphism {f = f} {g = g}) (~ j) i
    }
