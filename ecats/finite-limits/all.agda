
{-# OPTIONS --without-K #-}

module ecats.finite-limits.all where

open import ecats.basic-defs.ecategory
open import ecats.finite-limits.defs&not public
open import ecats.finite-limits.props.all public


module connected-weak-limits-d&p (ℂ : ecategory) where
  open connected-weak-limits ℂ public
  open connected-weak-limits-props ℂ public


module finite-weak-limits-d&p (ℂ : ecategory) where
  open finite-weak-limits ℂ public
  open finite-weak-limits-props ℂ public


module connected-limits-d&p (ℂ : ecategory) where
  open connected-limits ℂ public
  open connected-limits-props ℂ public


module finite-limits-d&p (ℂ : ecategory) where
  open finite-limits ℂ public
  open finite-limits-props ℂ public

