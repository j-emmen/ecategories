
-- disable the K axiom:

{-# OPTIONS --without-K #-}

-- Agda version 2.5.4.1

module ecats.finite-limits.defs.all where

open import ecats.basic-defs.ecategory

open import ecats.finite-limits.defs.weak-terminal public
open import ecats.finite-limits.defs.terminal public
open import ecats.finite-limits.defs.terminal-is-weak public

open import ecats.finite-limits.defs.bin-weak-product public
open import ecats.finite-limits.defs.bin-product public
open import ecats.finite-limits.defs.bin-product-is-weak public

open import ecats.finite-limits.defs.weak-equaliser public
open import ecats.finite-limits.defs.equaliser public
open import ecats.finite-limits.defs.equaliser-is-weak public

open import ecats.finite-limits.defs.weak-pullback public
open import ecats.finite-limits.defs.pullback public
open import ecats.finite-limits.defs.pullback-is-weak public
open import ecats.finite-limits.defs.weak-Wlimit public

open import ecats.finite-limits.defs.weak-bow public
open import ecats.finite-limits.defs.bow public
open import ecats.finite-limits.defs.bow-is-weak public

open import ecats.finite-limits.defs.collective public


module connected-weak-limits-defs (ℂ : ecategory) where
  open wpullback-defs ℂ public
  open wequaliser-defs ℂ public
  open weak-bow-defs ℂ public
  open wWlim-defs ℂ public


module finite-weak-limits-defs (ℂ : ecategory) where
  open wterminal-defs ℂ public
  open bin-wproduct-defs ℂ public
  open wpullback-defs ℂ public
  open wequaliser-defs ℂ public
  open weak-bow-defs ℂ public
  open wWlim-defs ℂ public


module connected-limits-defs (ℂ : ecategory) where
  open pullback-defs ℂ public
  open equaliser-defs ℂ public
  open bow-defs ℂ public


module finite-limits-defs (ℂ : ecategory) where
  open terminal-defs ℂ public
  open bin-product-defs ℂ public
  open pullback-defs ℂ public
  open equaliser-defs ℂ public
  open bow-defs ℂ public
  

module limits→weak-limits (ℂ : ecategory) where
  open terminal→weak-terminal ℂ public
  open bin-product→bin-weak-product ℂ public
  open pullback→weak-pullback ℂ public
  open equaliser→weak-equaliser ℂ public
  open bow→weak-bow ℂ public


