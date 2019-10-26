{-# OPTIONS --cubical --safe #-}
module Categories.Category.Op where

open import Categories.Category.Core

_ᵒᵖ : ∀ {o ℓ} → Category o ℓ → Category o ℓ
C ᵒᵖ = record
  { Obj = C.Obj
  ; _⇒_ = λ a b → b ⇒ a
  ; id = C.id
  ; _∘_ = λ f g → g ∘ f
  ; assoc = {!!}
  ; identityˡ = {!!}
  ; identityʳ = {!!}
  }
  where
    module C = Category C
    open C
