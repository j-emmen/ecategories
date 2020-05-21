 
-- disable the K axiom:

{-# OPTIONS --without-K #-}

-- Agda version 2.5.4.1

module ecats.finite-limits.equaliser-dnp where

open import ecats.basic-defs.ecategory
open import ecats.finite-limits.defs.equaliser
open import ecats.finite-limits.props.equaliser




module equalisers-d&p (ℂ : ecategory) where
  open equaliser-defs ℂ public
  open equalisers-props ℂ public
-- end equliasers-d&p

