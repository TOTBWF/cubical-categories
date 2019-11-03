{-# OPTIONS --cubical --safe #-}

module Categories.Functor.Properties.Core where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.GroupoidLaws renaming
  ( lUnit to ∙-unitˡ
  ; rUnit to ∙-unitʳ
  ; assoc to ∙-assoc
  )

open import Categories.Category
open import Categories.Category.Instances.Path using (cong-homo)
open import Categories.Functor.Core renaming (_∘F_ to _∘_; id to Id)

open import Level

private
  variable
    o ℓ o′ : Level
    𝓒 𝓓 𝓔 𝓕 : Category o ℓ

module _ (F : Functor 𝓒 𝓓) where
  private
    module 𝓒 = Category 𝓒
    module 𝓓 = Category 𝓓
    module F = Functor F

  open 𝓒 hiding (_∘_)
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

module _ (F : Functor 𝓒 𝓓) (G : Functor 𝓓 𝓔) (H : Functor 𝓔 𝓕) where
  private
    module F = Functor F
    module G = Functor G
    module H = Functor H

  open F using (F₀; F₁)
  open G renaming (F₀ to G₀; F₁ to G₁)
  open H renaming (F₀ to H₀; F₁ to H₁)

  ∘F-assoc-filler : ∀ {A : Set o} {B : Set o′} {w x y : A} {z : B} → (f : A → B) →
            (p : w ≡ x) → (q : x ≡ y) → (r : f y ≡ z) →
            cong f p ∙ (cong f q ∙ r) ≡ cong f (p ∙ q) ∙ r
  ∘F-assoc-filler f p q r =
    ∙-assoc (cong f p) (cong f q) r ∙ cong (λ a → a ∙ r) (cong-homo f p q)

  ∘F-assoc : (H ∘ G) ∘ F ≡ H ∘ (G ∘ F)
  ∘F-assoc j = record
    { F₀ = λ x → H₀ (G₀ (F₀ x))
    ; F₁ = λ f → H₁ (G₁ (F₁ f))
    ; identity = λ i →
      ∘F-assoc-filler H₁ (cong G₁ F.identity) G.identity H.identity j i
    ; homomorphism = λ {_ _ _ f g} i →
      ∘F-assoc-filler H₁ (cong G₁ F.homomorphism) G.homomorphism (H.homomorphism {f = G₁ (F₁ f)} {g = G₁ (F₁ g)}) j i
    }
