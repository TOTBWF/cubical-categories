{-# OPTIONS --cubical --safe #-}
module Categories.Reasoning.Paths where

open import Level
open import Cubical.Foundations.Prelude

private
  variable
    ℓ : Level
    A : Type ℓ

≡⟨⟩≡∎-syntax : (x : A) (y : A) → x ≡ y → x ≡ y
≡⟨⟩≡∎-syntax _ _ p = p

infixr 3 ≡⟨⟩≡∎-syntax
syntax ≡⟨⟩≡∎-syntax x y p = x ≡⟨ p ⟩≡ y ∎
