{-# OPTIONS --cubical --safe #-}
open import Categories.Category

module Categories.Category.Monoidal {o ℓ} (𝓒 : Category o ℓ) where

open import Data.Product using (curry′; _,_)

open import Cubical.Foundations.Prelude

open import Categories.Category.Product
open import Categories.Reasoning.Hom 𝓒
open import Categories.Functor.Core renaming (id to idF)
open import Categories.NaturalTransformation.NaturalIsomorphism

open import Level

private
  module 𝓒 = Category 𝓒

open Category 𝓒

private
  variable
    X Y Z W A B : Obj
    f g h i a b : X ⇒ Y

⟨⟨-⟩_⟨-⟩⟩_⟨-⟩ : Functor (𝓒 × 𝓒) 𝓒 → Functor (𝓒 × 𝓒) 𝓒 → Functor ((𝓒 × 𝓒) × 𝓒) 𝓒
⟨⟨-⟩ F ⟨-⟩⟩ G ⟨-⟩ = record
  { F₀ = λ ((x , y) , z) → G₀ ((F₀ (x , y)) , z)
  ; F₁ = λ ((f , g), h) → G₁ ((F₁ (f , g)) , h)
  ; identity = 
      G₁ ((F₁ (𝓒.id , 𝓒.id)) , 𝓒.id) ≡⟨ cong G₁ (cong (λ a → (a , 𝓒.id)) F.identity) ⟩
      G₁ ( 𝓒.id , 𝓒.id ) ≡⟨ G.identity ⟩
      𝓒.id ∎
  ; homomorphism = λ {_} {_} {_} {f} {g} i →  {!!}
      -- G₁ ()
    
  }
  where
    module F = Functor F
    module G = Functor G
    open F
    open G renaming (F₀ to G₀; F₁ to G₁)

⟨-⟩_⟨⟨-⟩_⟨-⟩⟩ : Functor (𝓒 × 𝓒) 𝓒 → Functor (𝓒 × 𝓒) 𝓒 → Functor ((𝓒 × 𝓒) × 𝓒) 𝓒
⟨-⟩_⟨⟨-⟩_⟨-⟩⟩ = {!!}

record Monoidal : Set (o ⊔ ℓ) where
  field
    ⊗ : Functor (𝓒 × 𝓒) 𝓒
    unit : Obj

  module ⊗ = Functor ⊗
  open Functor ⊗

  _⊗⟨-⟩ : Obj → Functor 𝓒 𝓒
  X ⊗⟨-⟩ = {!!}

  ⟨-⟩⊗_ : Obj → Functor 𝓒 𝓒
  ⟨-⟩⊗ X = {!!}

  -- Composition of two bifunctors, on the left

  ⟨-⟩ : Functor 𝓒 𝓒
  ⟨-⟩ = idF
  
  -- _⊗₀_ : Obj → Obj → Obj
  -- X ⊗₀ Y = F₀ (X , Y)

  -- _⊗₁_ : (X ⇒ Y) → (Z ⇒ W) → (X ⊗₀ Z ⇒ Y ⊗₀ W)
  -- f ⊗₁ g = F₁ (f , g)

  field
    unitorˡ : unit ⊗⟨-⟩ ≃ ⟨-⟩
    unitorʳ : ⟨-⟩⊗ unit ≃ ⟨-⟩
    associator : ⟨⟨-⟩ ⊗ ⟨-⟩⟩ ⊗ ⟨-⟩ ≃ ⟨-⟩ ⊗ ⟨⟨-⟩ ⊗ ⟨-⟩⟩

--   module unitorˡ X = _≃_ (unitorˡ X)
--   module unitorʳ {X} = _≃_ (unitorʳ {X})
--   module associator {X} {Y} {Z} = _≃_ (associator {X} {Y} {Z})

--   private
--     λ⇒ = unitorˡ.isoˡ
--     λ⇐ = unitorˡ.isoʳ
--     ρ⇒ = unitorʳ.isoˡ
--     ρ⇐ = unitorʳ.isoʳ

--     α⇒ : (X ⊗₀ Y) ⊗₀ Z ⇒ X ⊗₀ (Y ⊗₀ Z)
--     α⇒ = associator.isoˡ

--   field
-- {-
-- (x ⊗ 1) ⊗ y -- α --> x ⊗ (1 ⊗ y)
--         \             /
--          \    comm   /
--        ρ ⊗ id      id ⊗ λ
--            \       /
--             \     /
--              v   v
--              x ⊗ y
-- -}

--     triangle : (ρ⇒ ⊗₁ 𝓒.id) ≡ 𝓒 [ 𝓒.id ⊗₁ λ⇒ ∘ α⇒ ]

