 
-- disable the K axiom:

{-# OPTIONS --without-K #-}

-- Agda version 2.5.4.1

module ecats.finite-limits.weak-pullback-dnp where

open import ecats.basic-defs.ecategory
open import ecats.finite-limits.wpb-d&n public
open import ecats.finite-limits.props.weak-pullback public



module wpullback-squares-d&p (ℂ : ecategory) where
  open wpullback-squares ℂ public
  open weak-pullback-sq-props ℂ public
-- end wpullback-squares-d&p

