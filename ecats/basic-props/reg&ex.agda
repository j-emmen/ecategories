
{-# OPTIONS --without-K #-}

module ecats.basic-props.reg&ex where

open import ecats.basic-defs.ecategory
open import ecats.basic-defs.exact-ecat
open import ecats.basic-props.image-fact public
open import ecats.basic-props.regular-ecat public
open import ecats.basic-props.exact-ecat public



module exact-cat-props {𝔼 : ecategory} (ex : is-exact 𝔼) where
  open exact-cat-props-only ex public
  open regular-cat-props is-reg public
-- end exact-cat-prop
