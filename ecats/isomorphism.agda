
{-# OPTIONS --without-K #-}

module ecats.isomorphism where

open import ecats.basic-defs.ecat-def&not
open import ecats.basic-defs.isomorphism public
open import ecats.basic-props.isomorphism public


module iso-d&p {ℓ₁ ℓ₂ ℓ₃ : Level}(ℂ : ecategoryₗₑᵥ ℓ₁ ℓ₂ ℓ₃) where
  open iso-defs ℂ public
  open iso-props ℂ public
  --open iso-transports ℂ public


module ecat-with-isos {ℓ₁ ℓ₂ ℓ₃ : Level}(ℂ : ecategoryₗₑᵥ ℓ₁ ℓ₂ ℓ₃) where
  open ecat ℂ public
  open iso-d&p ℂ public


module ecategory-aux-with-isos {ℓ₁ ℓ₂ ℓ₃ : Level}(ℂ : ecategoryₗₑᵥ ℓ₁ ℓ₂ ℓ₃) where
  open ecategory-aux ℂ public
  open iso-d&p ℂ public
