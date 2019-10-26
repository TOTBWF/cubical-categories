{-# OPTIONS --cubical --safe #-}
module Categories.Category.Product where

open import Level

open import Data.Product using (_,_; proj₁; proj₂) renaming (_×_ to _×′_)

open import Categories.Category

private
  variable
    o ℓ o′ ℓ′ : Level

_×_ : ∀ (C : Category o ℓ) → (D : Category o′ ℓ′) → Category (o ⊔ o′) (ℓ ⊔ ℓ′)
C × D = record
  { Obj = C.Obj ×′ D.Obj
  ; _⇒_ = λ A B → C [ proj₁ A , proj₁ B ] ×′ D [ proj₂ A , proj₂ B ]
  ; id = C.id , D.id
  ; _∘_ = λ (f , g) (h , i) → C [ f ∘ h ] , D [ g ∘ i ]
  ; assoc = λ {_ _ _ _ f g h} i →
              C.assoc {f = proj₁ f} {g = proj₁ g} {h = proj₁ h} i ,
              D.assoc {f = proj₂ f} {g = proj₂ g} {h = proj₂ h} i
  ; identityˡ = λ {_ _ f} i →
              (C.identityˡ {f = proj₁ f} i) , (D.identityˡ {f = proj₂ f} i)
  ; identityʳ = λ {_ _ f} i →
              (C.identityʳ {f = proj₁ f} i) , (D.identityʳ {f = proj₂ f} i)
  }
  where
    module C = Category C
    module D = Category D

