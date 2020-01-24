{-# OPTIONS --cubical --safe #-}
module Categories.Higher.[N,1]-Category where

open import Categories.Higher.Core public
open [_,1]-Category

infix 10  _[_,_] _[_∘_]

_[_,_] : ∀ {o ℓ n} → (𝓒 : [ n ,1]-Category o ℓ) → (X : Obj 𝓒) → (Y : Obj 𝓒) → Set ℓ
_[_,_] = _⇒_

_[_∘_] : ∀ {o ℓ n} → (𝓒 : [ n ,1]-Category o ℓ) → ∀ {X Y Z} (f : 𝓒 [ Y , Z ]) → (g : 𝓒 [ X , Y ]) → 𝓒 [ X , Z ]
_[_∘_] = _∘_
