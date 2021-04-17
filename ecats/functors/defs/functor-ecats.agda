
{-# OPTIONS --without-K #-}

module ecats.functors.defs.functor-ecats where

open import tt-basics.setoids
open import ecats.basic-defs.ecat-def&not
open import ecats.basic-defs.isomorphism
open import ecats.basic-defs.epi&mono
open import ecats.basic-props.epi&mono
open import ecats.functors.defs.efunctor-d&n
open import ecats.functors.defs.natural-transformation



Fun : (𝔸 𝔹 : ecategory) → ecategory
Fun 𝔸 𝔹 = record
  { Obj = efunctor 𝔸 𝔹
  ; Hom = λ F G → {!!}
  ; isecat = {!!}
  }
