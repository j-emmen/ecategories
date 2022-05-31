
{-# OPTIONS --without-K #-}

module ecats.finite-limits.defs&not where

open import ecats.basic-defs.ecategory
open import ecats.finite-limits.defs.all public
open import ecats.finite-limits.not.all public


module binary-wproducts (ℂ : ecategory) where
  open bin-wproduct-defs ℂ public
  open bin-wproduct-spans ℂ public
-- end binary-wproducts


module binary-products (ℂ : ecategory) where
  open bin-product-defs ℂ public
  open bin-product-spans ℂ public
-- end binary-products


module wpullback-squares (ℂ : ecategory) where
  open wpullback-defs ℂ public
  open wpullback-squares-not ℂ public
-- end wpullback-squares


module pullback-squares (ℂ : ecategory) where
  open pullback-defs ℂ public
  open pullback-squares-not ℂ public
-- end pullback-squares


module connected-weak-limits (ℂ : ecategory) where
  open connected-weak-limits-defs ℂ public
  open connected-weak-limits-not ℂ public
--  end connected-weak-limits


module finite-weak-limits (ℂ : ecategory) where
  open finite-weak-limits-defs ℂ public
  open finite-weak-limits-not ℂ public
--  end finite-weak-limits


module connected-limits (ℂ : ecategory) where
  open connected-limits-defs ℂ public
  open connected-limits-not ℂ public
-- end connected-limits


module finite-limits (ℂ : ecategory) where
  open finite-limits-defs ℂ public
  open finite-limits-not ℂ public
-- end finite-limits
