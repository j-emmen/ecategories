
{-# OPTIONS --without-K #-}

module ecats.isomorphism where

open import ecats.basic-defs.ecategory
open import ecats.basic-defs.isomorphism public
open import ecats.basic-props.isomorphism public


module iso-d&p {ℓ₁ ℓ₂ ℓ₃ : Level}(ℂ : ecategoryₗₑᵥ ℓ₁ ℓ₂ ℓ₃) where
  open iso-defs ℂ public
  open iso-props ℂ public
  --open iso-transports ℂ public
