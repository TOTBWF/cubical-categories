{-# OPTIONS --cubical --safe #-}
module Categories.Category.Instances.Cat where

open import Level

open import Categories.Category.Core
open import Categories.Functor.Core renaming (id to Id)
open import Categories.Functor.Properties.Core

CAT : ∀ (o ℓ : Level) → Category (suc (o ⊔ ℓ)) (o ⊔ ℓ)
CAT o ℓ = record
  { Obj = Category o ℓ
  ; _⇒_ = λ 𝓒 𝓓 → Functor 𝓒 𝓓
  ; id = Id
  ; _∘_ = _∘F_
  ; assoc = λ {_ _ _ _ F G H}  i → ∘F-assoc F G H i
  ; identityˡ = λ {_ _ F} i → ∘F-identityˡ F i
  ; identityʳ = λ {_ _ F} i → ∘F-identityʳ F i
  }
