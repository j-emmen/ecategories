
{-# OPTIONS --without-K #-}

module ecats.basic-props.arrows where

open import ecats.basic-defs.ecategory
open import ecats.basic-defs.arrows
open import ecats.basic-props.isomorphism public
open import ecats.basic-props.epi&mono-basic public
open import ecats.basic-props.epi&mono public


module arrows-props (ℂ : ecategory) where
  open iso-props ℂ public
  open iso-transports ℂ public
  open epi&mono-props-all ℂ public
