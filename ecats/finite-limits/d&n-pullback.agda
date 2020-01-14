 
-- disable the K axiom:

{-# OPTIONS --without-K #-}

-- Agda version 2.5.4.1

module ecats.finite-limits.d&n-pullback where

open import ecats.basic-defs.ecategory
open import ecats.finite-limits.defs.pullback public
open import ecats.finite-limits.not.pullback public



module pullback-squares (ℂ : ecategory) where
  open pullback-defs ℂ public
  open pullback-squares-not ℂ public
-- end pullback-squares
