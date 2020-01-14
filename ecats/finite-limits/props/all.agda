
-- disable the K axiom:

{-# OPTIONS --without-K #-}

-- Agda version 2.5.4.1

module ecats.finite-limits.props.all where

open import ecats.basic-defs.ecategory
open import ecats.finite-limits.props.relations-among-limits public
-- The following has to be removed if the -dnp versions are used
open import ecats.finite-limits.props.terminal public
open import ecats.finite-limits.props.bin-product public
open import ecats.finite-limits.props.equaliser public
open import ecats.finite-limits.props.weak-pullback public
open import ecats.finite-limits.props.pullback public
open import ecats.finite-limits.props.relations-among-limits public


module connected-weak-limits-props (ℂ : ecategory) where
  open weak-pullback-props ℂ public
-- end connected-weak-limits-props


module finite-weak-limits-props (ℂ : ecategory) where
  open weak-pullback-props ℂ public
-- end finite-weak-limits-props


module connected-limits-props (ℂ : ecategory) where
  open equaliser-props ℂ public
  open pullback-props ℂ public
-- end connected-limits-props


module finite-limits-props (ℂ : ecategory) where
  open terminal-props ℂ public
  open bin-product-props ℂ public
  open equaliser-props ℂ public
  open pullback-props ℂ public
-- end finite-limits-props
