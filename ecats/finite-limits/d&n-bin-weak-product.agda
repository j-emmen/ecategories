
{-# OPTIONS --without-K #-}

module ecats.finite-limits.d&n-bin-weak-product where

open import ecats.basic-defs.ecategory
open import ecats.finite-limits.defs.bin-weak-product public
open import ecats.finite-limits.not.bin-weak-product public



module binary-wproducts (ℂ : ecategory) where
  open bin-wproduct-defs ℂ public
  open bin-wproduct-spans ℂ public
-- end binary-wproducts
