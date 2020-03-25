 
-- disable the K axiom:

{-# OPTIONS --without-K #-}

-- Agda version 2.5.4.1

module ecats.finite-limits.pullback-dnp where

open import ecats.basic-defs.ecategory
open import ecats.finite-limits.pb-d&n
open import ecats.finite-limits.props.pullback



module pullback-squares-d&p (ℂ : ecategory) where
  open pullback-squares ℂ public
  open pullback-squares-props ℂ public
-- end pullback-squares-d&p
