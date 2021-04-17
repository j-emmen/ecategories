
-- disable the K axiom:

{-# OPTIONS --without-K #-}

-- Agda version 2.5.4.1

module ecats.basic-defs.all-arrows where

open import ecats.basic-defs.ecategory
open import ecats.basic-defs.commut-shapes public
open import ecats.basic-defs.isomorphism public
open import ecats.basic-defs.epi&mono public
open import ecats.basic-defs.surjective public
open import ecats.basic-defs.kernel-pair public
open import ecats.basic-defs.image-fact public
open import ecats.basic-defs.eqv-rel public
open import ecats.basic-defs.generator public


module arrows-defs (ℂ : ecategory) where
  open comm-shapes ℂ public
  open epis&monos-defs ℂ public
  open image-fact-defs ℂ public
  open iso-defs ℂ public
  open weak-kernel-pairs-defs ℂ public
  open kernel-pairs-defs ℂ public
  open pseudo-eq-rel-defs ℂ public
  open eq-rel-defs ℂ public
  open surjective-defs {ℂ} public
  open generator-defs ℂ public
