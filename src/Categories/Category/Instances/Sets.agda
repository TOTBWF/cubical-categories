{-# OPTIONS --cubical --safe #-}
module Categories.Category.Instances.Sets where

open import Level

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Categories.Category.Core
open import Categories.Functor.Core renaming (id to Id)
open import Categories.Functor.Properties.Core

SET : ∀ (o : Level) → Category (suc o) o
SET o = record
  { Obj = Σ[ A ∈ Set o ] (isSet A)
  ; _⇒_ = λ (A , _) (B , _) → A → B
  ; id = λ x → x
  ; _∘_ = λ f g x → f (g x)
  ; hom-is-set = λ {_} {(_ , B-is-set)} → isSetPi λ _ → B-is-set
  ; assoc = refl
  ; identityˡ = refl
  ; identityʳ = refl
  }
