{-# OPTIONS --cubical --safe #-}
open import Categories.Category

module Categories.Object.Product.Core {o ℓ} (𝓒 : Category o ℓ) where

open import Level
open import Cubical.Foundations.Prelude
open import Categories.Morphism.Core 𝓒
open import Categories.Reasoning.Commutative 𝓒
open import Categories.Reasoning.Hom 𝓒

open Category 𝓒

private
  variable
    A B C : Obj
    h i j : A ⇒ B

record Product (A B : Obj) : Set (o ⊔ ℓ) where

  infix 10 ⟨_,_⟩

  field
    A×B : Obj
    π₁ : A×B ⇒ A
    π₂ : A×B ⇒ B
    ⟨_,_⟩ : (C ⇒ A) → (C ⇒ B) → C ⇒ A×B

    project₁ : π₁ ∘ ⟨ h , i ⟩ ≡ h
    project₂ : π₂ ∘ ⟨ h , i ⟩ ≡ i
    unique   : π₁ ∘ h ≡ i → π₂ ∘ h ≡ j → ⟨ i , j ⟩ ≡ h

up-to-iso : ∀ {A B : Obj} → (p₁ p₂ : Product A B) → Product.A×B p₁ ≅ Product.A×B p₂
up-to-iso {A} {B} p₁ p₂ = record
  { from = repack p₁ p₂
  ; to = repack p₂ p₁
  ; iso = record
    { isoˡ = repack-cancel p₂ p₁
    ; isoʳ = repack-cancel p₁ p₂
    }
  }
  where
    open Product {A} {B} renaming (⟨_,_⟩ to _⟨_,_⟩)

    repack : (p₁ p₂ : Product A B) → A×B p₁ ⇒ A×B p₂
    repack p₁ p₂ = p₂ ⟨ π₁ p₁ , π₂ p₁ ⟩

    repack≡id : (p : Product A B) → repack p p ≡ id
    repack≡id p = unique p identityʳ identityʳ

    repack∘ : (p₁ p₂ : Product A B) → repack p₁ p₂ ∘ repack p₂ p₁ ≡ repack p₂ p₂
    repack∘ p₁ p₂ = sym (unique p₂ (glue-◃ʳ (project₁ p₂) (project₁ p₁))
                                   (glue-◃ʳ (project₂ p₂) (project₂ p₁)))

    repack-cancel : (p₁ p₂ : Product A B) → repack p₁ p₂ ∘ repack p₂ p₁ ≡ id
    repack-cancel p₁ p₂ =
      repack p₁ p₂ ∘ repack p₂ p₁ ≡⟨ repack∘ p₁ p₂  ⟩
      repack p₂ p₂ ≡⟨ repack≡id p₂ ⟩
      id ∎
