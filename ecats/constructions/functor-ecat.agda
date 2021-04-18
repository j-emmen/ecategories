
{-# OPTIONS --without-K #-}

module ecats.constructions.functor-ecat where

open import ecats.basic-defs.ecat-def&not
open import ecats.functors.defs.efunctor-d&n
open import ecats.functors.defs.natural-transformation


---------------------------------------------------------------------
-- Large category of efunctors between two locally small ecategories
---------------------------------------------------------------------

Fctr : (ℂ 𝔻 : ecategory) → large-ecategory
Fctr ℂ 𝔻 = record
  { Obj = efunctor ℂ 𝔻
  ; Hom = Nat {ℂ} {𝔻}
  ; isecat = record
           { _∘_ = natt-vcmp {ℂ} {𝔻}
           ; idar = λ F → natt-id {ℂ} {𝔻} {F}
           ; ∘ext = λ _ _ _ _ pff pfg X → 𝔻.∘ext _ _ _ _ (pff X) (pfg X)
           ; lidax = λ f X → 𝔻.lidax (fnc f {X})
           ; ridax = λ f X → 𝔻.ridax (fnc f {X})
           ; assoc = λ f g h X → 𝔻.assoc (fnc f {X}) (fnc g) (fnc h)
           }
  }
  where module 𝔻 = ecategory 𝔻
        open natural-transformation

