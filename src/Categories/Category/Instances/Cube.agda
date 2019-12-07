{-
Category of Cubes
https://ncatlab.org/nlab/show/category+of+cubes
-}

{-# OPTIONS --cubical --safe #-}
module Categories.Category.Instances.Cube where

open import Level
open import Data.Sum

open import Cubical.Foundations.Prelude hiding (_□_)

open import Categories.Category.Core

data □ : Set where
  I⁰ : □ 
  I¹ : □

infixr 9 _∘_
data _⇒_ : □ → □ → Set where
  id : ∀ {A} → A ⇒ A
  _∘_ : ∀ {A B C} → (f : B ⇒ C) → (g : A ⇒ B) → A ⇒ C
  i₀ : I⁰ ⇒ I¹  
  i₁ : I⁰ ⇒ I¹
  p  : I¹ ⇒ I⁰
  uniq : ∀ {f : I⁰ ⇒ I⁰} → f ≡ id
  assoc : ∀ {A B C D} {f : A ⇒ B} {g : B ⇒ C} {h : C ⇒ D} → (h ∘ g) ∘ f ≡ h ∘ (g ∘ f)
  identityˡ : ∀ {A B} {f : A ⇒ B} → id ∘ f ≡ f 
  identityʳ : ∀ {A B} {f : A ⇒ B} → f ∘ id ≡ f 


CUBE : Category _ _
CUBE = record
  { Obj = □
  ; _⇒_ = _⇒_
  ; id = id
  ; _∘_ = _∘_
  ; assoc = assoc
  ; identityˡ = identityˡ
  ; identityʳ = identityʳ
  }

open import Categories.Reasoning.Hom CUBE

-- open Category CUBE

{-
 I⁰ - i₀ -> I¹
  \         |
   \  comm  |
    \       |
    id      p
      \     |
       \    |
        v   v
          I⁰
-}

i⁰∘p≡id : p ∘ i₀ ≡ id
i⁰∘p≡id = uniq


{-
 I⁰ - i₁ -> I¹
  \         |
   \  comm  |
    \       |
    id      p
      \     |
       \    |
        v   v
          I⁰
-}

i¹∘p≡id : p ∘ i₀ ≡ id
i¹∘p≡id = uniq

2-non-id : ∀ (f : I¹ ⇒ I¹) → (f ≡ id) ⊎ (f ≡ i₀ ∘ p) ⊎ (f ≡ i₁ ∘ p)
2-non-id id = inj₁ refl
2-non-id (f ∘ g) = {!!}
2-non-id (assoc i) = {!!}
2-non-id (identityˡ i) = {!!}
2-non-id (identityʳ i) = {!!}
  where
    -- foo : ∀  (i₀ ∘ p) ∘ (i₀ ∘ p) ≡ i₀ ∘ p
    -- foo =
    --   (i₀ ∘ p) ∘ (i₀ ∘ p) ≡⟨ assoc ⟩
    --   i₀ ∘ (p ∘ i₀ ∘ p) ≡⟨ refl⟩∘⟨ sym assoc ⟩
    --   i₀ ∘ ((p ∘ i₀) ∘ p) ≡⟨ refl⟩∘⟨ uniq ⟩∘⟨refl ⟩
    --   i₀ ∘ id ∘ p ≡⟨ refl⟩∘⟨ identityˡ ⟩
    --   i₀ ∘ p ∎

    -- helper : ∀ {B} {f : I¹ ⇒ I¹} {g : I¹ ⇒ I¹} → 
    --                (f ≡ i₀ ∘ p) ⊎ (f ≡ i₁ ∘ p) →
    --                (g ≡ i₀ ∘ p) ⊎ (g ≡ i₁ ∘ p) →
    --                (f ∘ g ≡ id) ⊎ (f ∘ g ≡ i₀ ∘ p) ⊎ (f ∘ g ≡ i₁ ∘ p)
    -- helper {f = f} (inj₁ x) (inj₁ x₁) = inj₂ (inj₁ {!f ∘ g!})
    -- helper (inj₁ x) (inj₂ y) = {!!}
    -- helper (inj₂ y) (inj₁ x) = {!!}
    -- helper (inj₂ y) (inj₂ y₁) = {!!}
