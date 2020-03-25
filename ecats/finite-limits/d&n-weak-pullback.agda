 
-- disable the K axiom:

{-# OPTIONS --without-K #-}

-- Agda version 2.5.4.1

module ecats.finite-limits.d&n-weak-pullback where

open import ecats.basic-defs.ecategory
open import ecats.finite-limits.defs.weak-pullback public
open import ecats.finite-limits.not.weak-pullback public




module wpullback-squares (ℂ : ecategory) where
  open wpullback-defs ℂ public
  open wpullback-squares-not ℂ public
-- end wpullback-squares
