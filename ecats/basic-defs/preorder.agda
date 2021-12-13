
{-# OPTIONS --without-K #-}

module ecats.basic-defs.preorder where

open import tt-basics.all-basics renaming (||_|| to ||_||std)
open import ecats.basic-defs.ecat-def&not
open import ecats.basic-defs.isomorphism
open import ecats.basic-props.isomorphism
open import ecats.basic-defs.commut-shapes
open import ecats.constructions.free-ecat-on-graph
open import ecats.concr-ecats.Std-lev
open import ecats.functors.defs.efunctor
open import ecats.functors.defs.natural-iso
open import ecats.functors.defs.natural-transformation


record is-preorder {ℓ₁ ℓ₂ ℓ₃ : Level}(ℂ : ecategoryₗₑᵥ ℓ₁ ℓ₂ ℓ₃) : Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃) where
  open ecat ℂ
  field
    pf : {X Y : Obj}{f f' : || Hom X Y ||} → f ~ f'


record preorder (ℓ₁ ℓ₂ ℓ₃ : Level) : Set (sucₗₑᵥ (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃)) where
  field
    ℂ : ecategoryₗₑᵥ ℓ₁ ℓ₂ ℓ₃
    ispreord : is-preorder ℂ
  module ispreord = is-preorder ispreord
