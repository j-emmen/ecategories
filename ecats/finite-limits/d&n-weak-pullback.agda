
{-# OPTIONS --without-K #-}

module ecats.finite-limits.d&n-weak-pullback where

open import ecats.basic-defs.ecategory
open import ecats.finite-limits.defs.weak-pullback public
open import ecats.finite-limits.not.weak-pullback public




module wpullback-squares (ℂ : ecategory) where
  open wpullback-defs ℂ public
  open wpullback-squares-not ℂ public
-- end wpullback-squares
