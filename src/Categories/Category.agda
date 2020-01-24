{-# OPTIONS --cubical --safe #-}
module Categories.Category where

open import Categories.Category.Core public

infix 10  _[_,_] _[_∘_]
open Category

_[_,_] : ∀ {o ℓ} → (𝓒 : Category o ℓ) → (X : Obj 𝓒) → (Y : Obj 𝓒) → Set ℓ
_[_,_] = _⇒_

_[_∘_] : ∀ {o ℓ} → (𝓒 : Category o ℓ) → ∀ {X Y Z} (f : 𝓒 [ Y , Z ]) → (g : 𝓒 [ X , Y ]) → 𝓒 [ X , Z ]
_[_∘_] = _∘_
