{-# OPTIONS --cubical --safe #-}
module Categories.Reasoning.Paths where

open import Level

open import Cubical.Foundations.Prelude

private
  variable
    o : Level
    A B : Set o

cong-homo-filler : ∀ {x y z : A} → 
                     (f : A → B) → (p : x ≡ y) → (q : y ≡ z) →
                     I → I → I → B
cong-homo-filler {x = x} f p q k j i =
  hfill (λ k → λ { (i = i0) → f x
                 ; (i = i1) → cong f q k
                 ; (j = i1) → f (compPath-filler p q k i)
                 }) (inS (cong f p i)) k

cong-homo : ∀ {x y z : A} → (f : A → B) →
          (p : x ≡ y) → (q : y ≡ z) →
          cong f p ∙ cong f q ≡ cong f (p ∙ q)
cong-homo f p q j i = cong-homo-filler f p q i1 j i
