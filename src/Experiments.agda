{-# OPTIONS --cubical --safe #-}
module Experiments where

open import Level

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.GroupoidLaws renaming (assoc to ∙-assoc)

open import Categories.Category
open import Categories.Functor.Core
open import Categories.Reasoning.Commutative
open import Categories.NaturalTransformation.Core renaming (id to idN)

open import Data.Nat

private
  variable
    o ℓ o′ ℓ′ : Level
    𝓒 𝓓 𝓔 𝓕 : Category o ℓ
    A B : Set ℓ

-- 𝓓 [ η X ∘ 𝓓.id ] ≡⟨ 𝓓.identityʳ ⟩ η X ∎

∘ᵛ-identityˡ : ∀ {F G : Functor 𝓒 𝓓} → {τ : NaturalTransformation F G} → (τ ∘ᵛ idN) ≡ τ
∘ᵛ-identityˡ {𝓒 = 𝓒} {𝓓 = 𝓓} {F = F} {G = G} {τ = τ} j = record
  { η = λ X → 𝓓.identityʳ {f = η X} j
  ; commute = λ f i → commute-filler f i1 j i
  -- hfill (λ j → λ { (i = i0) → 𝓓.identityʳ {f = {!!}} {!!}
  --                                    ; (i = i1) → {!!}
  --                                    }) (inS (commute f i)) j
  }
  where
    module 𝓓 = Category 𝓓
    module τ = NaturalTransformation τ
    module idN = NaturalTransformation (idN {F = F})
    module F = Functor F
    module G = Functor G
    open F using (F₀; F₁)
    open G renaming (F₀ to G₀; F₁ to G₁)
    open τ

    -- foo : ∀ {X Y} → (f : 𝓒 [ X , Y ]) → 𝓓.∘-congʳ 𝓓.identityʳ ∙ commute f ≡ pullʳ (idN.commute f) ∙ 𝓓.∘-congˡ (𝓓.identityʳ)
    -- foo {X = X} {Y = Y} f j i = ?

    commute-filler : ∀ {X Y} → (f : 𝓒 [ X , Y ]) → I → I → I → 𝓓 [ F₀ X , G₀ Y  ]
    commute-filler {X = X} {Y = Y} f k j i =
      hfill (λ k → λ { (i = i0) → 𝓓 [ 𝓓.identityʳ {f = η Y} (j ∧ k) ∘ F₁ f ]
                     ; (i = i1) → {!!}
                     -- ( 𝓓.∘-congˡ {g = η Y} (𝓓.identityʳ {f = F₁ f} ) ∙ commute f) {!k!}
                     }) (inS (pullʳ 𝓓 (idN.commute f) {f = η Y} i)) k
    --   hfill (λ j → λ { (i = i0) → 𝓓.identityʳ {f = 𝓓 [ η Y ∘ F₁ f ]} {!~ i!}
    --                  ; (i = i1) → {!!}
    --                  }) (inS (commute f i)) j

-- {-
  
--  i0 = 𝓓.identityʳ j ∘ F₁ f
--  i1 = G₁ f ∘ 𝓓.identityʳ j

-- -}

--  {-
 
--   F x -- 𝓓.id --> F x ---- η x ---> G x
--    |                |                |
--    |                |                |

--   F₁ f            F₁ f              G₁ f

--    |                |                |
--    |                |                |
--    v                v                v
--   F y -- 𝓓.id --> F y ---- η y ---> G y

   

--  -}


--   -- [147] hcomp
--   --       (λ { j ((~ i ∨ i) = i1)
--   --              → (λ { (i = i0)
--   --                       → (𝓓 Category.∘
--   --                          (𝓓 Category.∘ NaturalTransformation.η τ Y)
--   --                          (NaturalTransformation.η idN Y))
--   --                         (Functor.F₁ F f)
--   --                   ; (i = i1)
--   --                       → ((𝓓 Category.∘ NaturalTransformation.η τ Y)
--   --                          ((𝓓 Category.∘ Functor.F₁ F f) (NaturalTransformation.η idN X))
--   --                          ≡⟨
--   --                          Categories.Reasoning.Commutative.Pulls.pullˡ 𝓓
--   --                          (NaturalTransformation.commute τ f)
--   --                          ⟩ Category.assoc 𝓓)
--   --                         (i1 ∧ j)
--   --                   })
--   --                _
--   --          ; j (i1 = i0)
--   --              → outS
--   --                (inS
--   --                 (Categories.Reasoning.Commutative.Pulls.pullʳ 𝓓
--   --                  (NaturalTransformation.commute idN f) i))
--   --          })
--   --       (outS
--   --        (inS
--   --         (Categories.Reasoning.Commutative.Pulls.pullʳ 𝓓
--   --          (NaturalTransformation.commute idN f) i)))
--   --         = commute-filler i0 f i0 i
--   --         : (𝓓 Category.⇒ Functor.F₀ F X) (Functor.F₀ G Y)
--   -- [137] NaturalTransformation.commute τ f i
--   --         = commute-filler i1 f i1 i
--   --         : (𝓓 Category.⇒ Functor.F₀ F X) (Functor.F₀ G Y)
--   -- [134] ?0 (j = j) (f = f) (j = j) (i = i1) = G₁ f 𝓓.∘ 𝓓.identityʳ j
--   --         : F₀ X 𝓓.⇒ G₀ Y
--   -- [134] ?0 (j = j) (f = f) (j = j) (i = i0) = 𝓓.identityʳ j 𝓓.∘ F₁ f
--   --         : F₀ X 𝓓.⇒ G₀ Y


-- -- Functors : Category o ℓ → Category o′ ℓ′ →  Category (o ⊔ ℓ ⊔ o′ ⊔ ℓ′) (o ⊔ ℓ ⊔ o′ ⊔ ℓ′)
-- -- Functors 𝓒 𝓓 = record
-- --   { Obj = Functor 𝓒 𝓓
-- --   ; _⇒_ = NaturalTransformation
-- --   ; id = idN
-- --   ; _∘_ = _∘ᵛ_
-- --   ; assoc = {!𝓓.assoc!}
-- --   ; identityˡ = {!!}
-- --   ; identityʳ = {!!}
-- --   }
-- --   where
-- --     module 𝓓 = Category 𝓓

-- -- Presheaves : ∀ {o ℓ o′ ℓ′ : Level} → Category o ℓ → Category (o ⊔ ℓ ⊔ suc (o′ ⊔ ℓ)) (o ⊔ ℓ ⊔ suc (o′ ⊔ ℓ′))
-- -- Presheaves 𝓒 = {!!}
