
{-# OPTIONS --without-K #-}

module ecats.small-limits.props.pullback where

open import ecats.basic-defs.ecat-def&not
open import ecats.basic-defs.commut-shapes
open import ecats.functors.defs.efunctor-d&n
open import ecats.functors.defs.cone
open import ecats.functors.defs.natural-transformation
open import ecats.constructions.functor-ecat
open import ecats.constructions.slice-ecat
open import ecats.finite-limits.defs.terminal
open import ecats.finite-limits.defs.pullback
open import ecats.small-limits.defs.small-limit
open import ecats.small-limits.defs.pullback
open import ecats.small-limits.defs.pullback-not
open import ecats.concr-ecats.finite-ecat


module pullback-diag-locsm (ℂ : ecategory) where
  private
    module ℂ where
      open ecat ℂ public
      open comm-shapes ℂ public
      open cospan-in-ecat ℂ public
      open small-limit-defs ℂ public
      open pullback-defs ℂ public
      open pullback-diag-defs ℂ public
      open pullback-diag-not ℂ public
    module Csp = Cospan-aux

  cone/cosp2comm-sq : {cosp : Cospan diag-in ℂ}(sp : Cone/.Obj cosp) → ℂ.comm-square
  cone/cosp2comm-sq {cosp} sp = record
    { dl = cosp.O1
    ; ur = cosp.O2
    ; dr = cosp.O12
    ; down = cosp.a1
    ; right = cosp.a2
    ; sq/ = record
          { upleft = ℂ.mkspan/ (sp.leg Csp.v₁) (sp.leg Csp.v₂)
          ; sq-pf = sp.tr Csp.a₁ ⊙ sp.tr Csp.a₂ ˢ
          }
    }
    where module cosp = ℂ.cospan (ℂ.diag2cosp cosp)
          module sp = Cone/.ₒ cosp sp
          open ecategory-aux-only ℂ using (_⊙_; _ˢ)

  is-lim-cn2is-pb-sq : {cosp : Cospan diag-in ℂ}(sp : Cone/.Obj cosp)
                             → ℂ.is-pullback-cone sp → ℂ.is-pb-square (cone/cosp2comm-sq sp)
  is-lim-cn2is-pb-sq {cosp} sp ispbcn = record
    { ⟨_,_⟩[_] = pbcn.⟨_,_⟩[_]
    ; ×/tr₁ = pbcn.tr₁
    ; ×/tr₂ = pbcn.tr₂
    ; ×/uq = pbcn.π-jm
    }
    where module pbcn = ℂ.is-pullback-cone ispbcn
  

-- end pullback-diag-props
