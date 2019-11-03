{-# OPTIONS --cubical --safe #-}
module Categories.Category where

open import Categories.Category.Core public

infix 10  _[_,_] _[_∘_]

_[_,_] : ∀ {o ℓ} → (C : Category o ℓ) → (X : Category.Obj C) → (Y : Category.Obj C) → Set ℓ
_[_,_] = Category._⇒_

_[_∘_] : ∀ {o ℓ} → (C : Category o ℓ) → ∀ {X Y Z} (f : C [ Y , Z ]) → (g : C [ X , Y ]) → C [ X , Z ]
_[_∘_] = Category._∘_

