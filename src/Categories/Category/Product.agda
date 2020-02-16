{-# OPTIONS --cubical --safe #-}
module Categories.Category.Product where

open import Level

open import Data.Product using (_,_; proj₁; proj₂) renaming (_×_ to _×′_) public

open import Cubical.Foundations.HLevels

open import Categories.Category

private
  variable
    o ℓ o′ ℓ′ : Level

_×_ : ∀ (𝓒 : Category o ℓ) → (𝓓 : Category o′ ℓ′) → Category (o ⊔ o′) (ℓ ⊔ ℓ′)
𝓒 × 𝓓 = record
  { Obj = 𝓒.Obj ×′ 𝓓.Obj
  ; _⇒_ = λ A B → 𝓒 [ proj₁ A , proj₁ B ] ×′ 𝓓 [ proj₂ A , proj₂ B ]
  ; id = 𝓒.id , 𝓓.id
  ; _∘_ = λ (f , g) (h , i) → 𝓒 [ f ∘ h ] , 𝓓 [ g ∘ i ]
  ; hom-is-set = isOfHLevelΣ 2 𝓒.hom-is-set λ _ → 𝓓.hom-is-set
  ; assoc = λ {_ _ _ _ f g h} i →
              𝓒.assoc {f = proj₁ f} {g = proj₁ g} {h = proj₁ h} i ,
              𝓓.assoc {f = proj₂ f} {g = proj₂ g} {h = proj₂ h} i
  ; identityˡ = λ {_ _ f} i →
              (𝓒.identityˡ {f = proj₁ f} i) , (𝓓.identityˡ {f = proj₂ f} i)
  ; identityʳ = λ {_ _ f} i →
              (𝓒.identityʳ {f = proj₁ f} i) , (𝓓.identityʳ {f = proj₂ f} i)
  }
  where
    module 𝓒 = Category 𝓒
    module 𝓓 = Category 𝓓

