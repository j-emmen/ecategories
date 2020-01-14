
-- disable the K axiom:

{-# OPTIONS --without-K #-}

-- Agda version 2.5.4.1

module ecats.finite-limits.not.all where

open import ecats.basic-defs.ecategory
open import ecats.finite-limits.not.bin-weak-product public
open import ecats.finite-limits.not.bin-product public
open import ecats.finite-limits.not.weak-pullback public
open import ecats.finite-limits.not.pullback public



module connected-weak-limits-not (ℂ : ecategory) where
  open wpullback-squares-not ℂ public


module finite-weak-limits-not (ℂ : ecategory) where
  open bin-wproduct-spans ℂ public
  open wpullback-squares-not ℂ public


module connected-limits-not (ℂ : ecategory) where
  open pullback-squares-not ℂ public


module finite-limits-not (ℂ : ecategory) where
  open bin-product-spans ℂ public
  open pullback-squares-not ℂ public
