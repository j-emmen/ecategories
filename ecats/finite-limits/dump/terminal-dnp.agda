 
-- disable the K axiom:

{-# OPTIONS --without-K #-}

-- Agda version 2.5.4.1

module ecats.finite-limits.terminal-dnp where

open import ecats.basic-defs.ecategory
open import ecats.finite-limits.defs.terminal
open import ecats.finite-limits.props.terminal



module terminal-d&p (ℂ : ecategory) where
  open terminal-defs ℂ public
  open terminal-props ℂ public
-- end terminal-d&p

