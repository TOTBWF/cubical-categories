{-# OPTIONS --cubical --safe #-}
module Categories.Functor.Bifunctor where

open import Level

open import Cubical.Foundations.Prelude

open import Categories.Category
open import Categories.Category.Product
open import Categories.Functor

private
  variable
    o ℓ o′ ℓ′ o″ ℓ″ : Level

Bifunctor : Category o ℓ → Category o′ ℓ′ → Category o″ ℓ″ → Set _
Bifunctor 𝓒 𝓓 𝓔 = Functor (𝓒 × 𝓓) 𝓔
