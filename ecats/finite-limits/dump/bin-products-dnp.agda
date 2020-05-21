 
-- disable the K axiom:

{-# OPTIONS --without-K #-}

-- Agda version 2.5.4.1

module ecats.finite-limits.bin-products-dnp where

open import ecats.basic-defs.ecategory
open import ecats.finite-limits.prd-d&n
open import ecats.finite-limits.props.bin-product



module binary-products-d&p (ℂ : ecategory) where
  open binary-products ℂ public
  open bin-products-props ℂ public
-- end binary-products-d&p
