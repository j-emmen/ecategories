
{-# OPTIONS --without-K #-}

module ecats.basic-defs.arrows where

open import ecats.basic-defs.ecategory
open import ecats.basic-defs.commut-shapes public
open import ecats.basic-defs.isomorphism public
open import ecats.basic-defs.epi&mono public
open import ecats.basic-defs.surjective public
open import ecats.basic-defs.kernel-pair public
open import ecats.basic-defs.eqv-rel public
open import ecats.basic-defs.generator public


module arrows-defs (ℂ : ecategory) where
  open comm-shapes ℂ public
  open iso-defs ℂ public
  open epi&mono-defs ℂ public
  --open weak-kernel-pairs-defs ℂ public
  open kernel-pairs-defs ℂ public
  --open pseudo-eq-rel-defs ℂ public
  open eq-rel-defs ℂ public
  --open surjective-defs {ℂ} public
  open generator-defs ℂ public
