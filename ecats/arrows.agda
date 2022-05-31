
{-# OPTIONS --without-K #-}

module ecats.arrows where

open import ecats.basic-defs.ecategory
open import ecats.isomorphism public
open import ecats.basic-defs.arrows public
open import ecats.basic-props.arrows public


module epi&mono-d&p (ℂ : ecategory) where
  open epi&mono-defs ℂ public
  open epi&mono-props-all ℂ  public

module arrows-d&p (ℂ : ecategory) where
  open arrows-defs ℂ public
  open arrows-props ℂ public
