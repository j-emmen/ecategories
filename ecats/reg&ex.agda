
{-# OPTIONS --without-K #-}

module ecats.reg&ex where

open import ecats.basic-defs.ecategory
open import ecats.basic-defs.reg&ex public
open import ecats.basic-props.reg&ex public


module regular-cat-d&p {ℂ : ecategory} (reg : is-regular ℂ) where
  open is-regular reg public
  open regular-cat-props reg public
-- end regular-cat-d&p


module exact-cat-d&p {𝔼 : ecategory} (ex : is-exact 𝔼) where
  open is-exact ex public
  open exact-cat-props ex public
--end exact-cat-d&p
