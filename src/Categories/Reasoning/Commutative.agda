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

  pullˡ : a ∘ b ∘ f ≡ c ∘ f
  pullˡ {f = f} =
    a ∘ b ∘ f ≡⟨ sym assoc ⟩
    (a ∘ b) ∘ f ≡⟨ a∘b≡c ⟩∘⟨refl ⟩
    c ∘ f ∎

  pullʳ : (f ∘ a) ∘ b ≡ f ∘ c
  pullʳ {f = f} =
    (f ∘ a) ∘ b ≡⟨ assoc ⟩
    f ∘ a ∘ b ≡⟨ refl⟩∘⟨ a∘b≡c ⟩
    f ∘ c ∎

open Pulls public

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
