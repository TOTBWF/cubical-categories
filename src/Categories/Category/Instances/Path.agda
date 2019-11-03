
{-# OPTIONS --cubical --safe #-}
module Categories.Category.Instances.Path where

open import Level

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.GroupoidLaws renaming
  ( lUnit to ∙-identityˡ
  ; rUnit to ∙-identityʳ
  ; assoc to ∙-assoc
  )

open import Categories.Category.Core
open import Categories.Functor.Core

private
  variable
    o : Level
    A B : Set o

{-
Unfortunately, `cubical` defines composition
of paths with it's arguments flipped, so we
have to do some munging to get everything to line up.
-}
PATH : ∀ {o} → (A : Set o) → Category o o
PATH A = record
  { Obj = A
  ; _⇒_ = _≡_
  ; id = refl
  ; _∘_ = λ p q → q ∙ p
  ; assoc = λ {_ _ _ _ f g h} j i → ∙-assoc f g h j i
  ; identityˡ = λ {_ _ f} j i → ∙-identityʳ f (~ j) i
  ; identityʳ = λ {_ _ f} j i → ∙-identityˡ f (~ j) i
  }

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

{-
Every function between two types is a functor between 
their underlying groupoids.
-}
liftF : ∀ (f : A → B) → Functor (PATH A) (PATH B)
liftF f = record
  { F₀ = f
  ; F₁ = cong f
  ; identity = λ {a} j i → f a
  ; homomorphism = λ {a b c p q} j i → cong-homo f p q (~ j) i
  }
