
{-# OPTIONS --without-K #-}

module ecats.small-limits.defs.pullback where

open import tt-basics.basics
open import ecats.basic-defs.ecat-def&not
open import ecats.basic-defs.commut-shapes
open import ecats.functors.defs.efunctor-d&n
open import ecats.functors.defs.cone
open import ecats.functors.defs.natural-transformation
open import ecats.constructions.functor-ecat
open import ecats.constructions.slice-ecat
open import ecats.finite-limits.defs.terminal
open import ecats.small-limits.defs.small-limit
open import ecats.concr-ecats.finite-ecat

module pullback-diag-defs {ℓ₁ ℓ₂ ℓ₃ : Level}(ℂ : ecategoryₗₑᵥ ℓ₁ ℓ₂ ℓ₃) where
  private
    module ℂ where
      open ecat ℂ public
      open comm-shapes ℂ public
      open cospan-in-ecat ℂ public
      open small-limit-defs ℂ public

  is-pullback-cone : {cosp : Cospan diag-in ℂ}(sp : Cone/.Obj cosp) → Set ℂ.ℓₐₗₗ
  is-pullback-cone sp = ℂ.is-limit-cone sp

  pullback-cone-of : (cosp : Cospan diag-in ℂ) → Set ℂ.ℓₐₗₗ
  pullback-cone-of cosp = ℂ.limit-of cosp

-- end pullback-diag-defs
