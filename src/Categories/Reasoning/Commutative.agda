{-# OPTIONS --cubical --safe #-}
open import Categories.Category

-- Reasoning Combinators when dealing with commutative diagrams.
module Categories.Reasoning.Commutative {o ℓ} (𝓒 : Category o ℓ) where

open import Cubical.Foundations.Prelude
open import Categories.Reasoning.Hom 𝓒
open import Categories.CommutativeDiagram.Square 𝓒
open Category 𝓒

private
  variable
    X Y : Obj
    a a′ a″ b b′ b″ c c′ c″ : X ⇒ Y
    f g h i : X ⇒ Y


module Pulls (a∘b≡c : a ∘ b ≡ c) where

{-
A -- f --> B --- c --> D
            \         ^
             \ comm  /
              b     a
               \   /
                v /
                 C
-}
  pullˡ : a ∘ b ∘ f ≡ c ∘ f
  pullˡ {f = f} =
    a ∘ b ∘ f ≡⟨ sym assoc ⟩
    (a ∘ b) ∘ f ≡⟨ a∘b≡c ⟩∘⟨refl ⟩
    c ∘ f ∎

{-
A --- c --> C -- f --> D
 \         ^
  \ comm  /
   b     a
    \   /
     v /
      B
-}

  pullʳ : (f ∘ a) ∘ b ≡ f ∘ c
  pullʳ {f = f} =
    (f ∘ a) ∘ b ≡⟨ assoc ⟩
    f ∘ a ∘ b ≡⟨ refl⟩∘⟨ a∘b≡c ⟩
    f ∘ c ∎

open Pulls public

module Pushes (c≡a∘b : c ≡ a ∘ b) where

{-
A -- f --> B --- c --> D
            \         ^
             \ comm  /
              b     a
               \   /
                v /
                 C
-}

  pushˡ : c ∘ f ≡ a ∘ (b ∘ f)
  pushˡ {f = f} = sym (pullˡ (sym c≡a∘b))

{-
A --- c --> C -- f --> D
 \         ^
  \ comm  /
   b     a
    \   /
     v /
      B
-}

  pushʳ : f ∘ c ≡ (f ∘ a) ∘ b
  pushʳ {f = f} = sym (pullʳ (sym c≡a∘b))

open Pushes public

module IntroElim (a≡id : a ≡ id) where

{-
  /- a --\
 /        v
A   comm  A -- f --> b
 \        ^
  \- id -/
-}

  elimʳ : f ∘ a ≡ f
  elimʳ {f = f} =
    f ∘ a ≡⟨ refl⟩∘⟨ a≡id ⟩
    f ∘ id ≡⟨ identityʳ ⟩
    f ∎

  introʳ : f ≡ f ∘ a
  introʳ = sym elimʳ

{-
             /- a --\
            /        v
A -- f --> B   comm  B
            \        ^
             \- id -/
-}

  elimˡ : a ∘ f ≡ f
  elimˡ {f = f} =
    a ∘ f ≡⟨ a≡id ⟩∘⟨refl ⟩
    id ∘ f ≡⟨ identityˡ ⟩
    f ∎

  introˡ : f ≡ a ∘ f
  introˡ = sym elimˡ

module Cancellers (inv : h ∘ i ≡ id) where

{-

      A
     ^  ^
    /    \
   f      f
  /  comm  \
 /          \
B --- id --> B
 \          ^
  \  comm  /
   i      h
    \    /
     v  /
      C
-}

  cancelʳ : (f ∘ h) ∘ i ≡ f
  cancelʳ {f = f} = 
    (f ∘ h) ∘ i ≡⟨ pullʳ inv ⟩
    f ∘ id ≡⟨ identityʳ ⟩
    f ∎

{-

      A
     /  \
    /    \
   f      f
  /  comm  \
 v          v
B --- id --> B
 \          ^
  \  comm  /
   i      h
    \    /
     v  /
      C
-}
  cancelˡ : h ∘ i ∘ f ≡ f
  cancelˡ {f = f} = 
    h ∘ i ∘ f ≡⟨ pullˡ inv ⟩
    id ∘ f ≡⟨ identityˡ ⟩
    f ∎

-- essentially composition in the arrow category
{-
   A₁ -- c --> B₁
   |           |
   b′  comm    b
   |           |
   V           V
   A₂ -- c′ -> B₂
   |           |
   a′  comm    a
   |           |
   V           V
   A₃ -- c″ -> B₃

   then the whole diagram commutes
-} 
glue-□ : CommutativeSquare c′ a′ a c″ →
       CommutativeSquare c b′ b c′ →
       CommutativeSquare c (a′ ∘ b′) (a ∘ b) c″
glue-□ {c′ = c′} {a′ = a′} {a = a} {c″ = c″} {c = c} {b′ = b′} {b = b} sq-a sq-b =
  (a ∘ b) ∘ c ≡⟨ pullʳ sq-b ⟩
  a ∘ (c′ ∘ b′) ≡⟨ pullˡ sq-a ⟩
  (c″ ∘ a′) ∘ b′ ≡⟨ assoc ⟩
  c″ ∘ a′ ∘ b′ ∎
  

-- essentially composition in the over category
{-
      C₂
     /  \
    /    \
   b′     a″
  /  comm  \
 v          v
A₁ -- a′ --> B₁
 \          ^
  \  comm  /
   b      a
    \    /
     v  /
      C₁

-}

glue-◃ʳ : a ∘ b ≡ a′ → a′ ∘ b′ ≡ a″ → a ∘ (b ∘ b′) ≡ a″
glue-◃ʳ {a = a} {b = b} {a′ = a′} {b′ = b′} {a″ = a″} a∘b≡a′ a′∘b′≡a″ =
  a ∘ b ∘ b′ ≡⟨ pullˡ a∘b≡a′ ⟩
  a′ ∘ b′ ≡⟨ a′∘b′≡a″ ⟩
  a″ ∎
  
-- essentially composition in the under category
{-
      C₂
     ^  ^
    /    \
   b″     a′
  /  comm  \
 /          \
A₁ -- b′ --> C₁
 \          ^
  \  comm  /
   b      a
    \    /
     v  /
      B₁

-}

glue-◃ˡ : a′ ∘ b′ ≡ b″ → a ∘ b ≡ b′ → (a′ ∘ a) ∘ b ≡ b″
glue-◃ˡ {a′ = a′} {b′ = b′} {b″ = b″} {a = a} {b = b} a′∘b′≡b″ a∘b≡b′ =
  (a′ ∘ a) ∘ b ≡⟨ pullʳ a∘b≡b′ ⟩
  a′ ∘ b′ ≡⟨ a′∘b′≡b″ ⟩
  b″ ∎
