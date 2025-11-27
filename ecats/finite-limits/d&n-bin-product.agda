
{-# OPTIONS --without-K #-}

module ecats.finite-limits.d&n-bin-product where

open import ecats.basic-defs.ecategory
open import ecats.finite-limits.defs.bin-product public --hiding (has-weak-pullbacks)
open import ecats.finite-limits.not.bin-product public


module binary-products {ℓₒ ℓₐ ℓ~ : Level}(ℂ : ecategoryₗₑᵥ ℓₒ ℓₐ ℓ~) where
  open bin-product-defs ℂ public
  open bin-product-spans ℂ public
-- end binary-products
