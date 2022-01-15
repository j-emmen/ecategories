
{-# OPTIONS --without-K #-}

module ecats.small-limits.props.pullback where

open import tt-basics.basics
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
    module CspC = Cospan-aux
    module CspG = Cospan-graph

  cone/cosp2comm-sq : {cosp : Cospan diag-in ℂ}(sp : Cone/.Obj cosp) → ℂ.comm-square
  cone/cosp2comm-sq {cosp} sp = record
    { dl = cosp.O1
    ; ur = cosp.O2
    ; dr = cosp.O12
    ; down = cosp.a1
    ; right = cosp.a2
    ; sq/ = record
          { upleft = ℂ.mkspan/ (sp.leg CspC.v₁) (sp.leg CspC.v₂)
          ; sq-pf = sp.tr CspC.a₁ ⊙ sp.tr CspC.a₂ ˢ
          }
    }
    where module cosp = ℂ.cospan (ℂ.diag2cosp cosp)
          module sp = Cone/.ₒ cosp sp
          open ecategory-aux-only ℂ using (_⊙_; _ˢ)

  comm-sq2cosp : ℂ.comm-square → Cospan diag-in ℂ
  comm-sq2cosp sq = Cospan-free.unv.fctr ℂ {GE = GE} GEext
                  where module sq = ℂ.comm-square sq
                        open ecategory-aux-only ℂ using (r)
                        GO : CspG.V → ℂ.Obj
                        GO (inl x) = sq.dr
                        GO (inr (inl x)) = sq.dl
                        GO (inr (inr x)) = sq.ur
                        GE : {u v : CspG.V} → CspG.E u v → || ℂ.Hom (GO u) (GO v) ||
                        GE {inr (inl x)} {inl y} uv = sq.down
                        GE {inr (inr x)} {inl y} uv = sq.right
                        GEext : {u v : CspG.V} {uv uv' : || CspG.ES u v ||}
                                   → uv CspG.~ uv' → GE uv ℂ.~ GE uv'
                        GEext {inr (inl x)} {inl y} eq = r
                        GEext {inr (inr x)} {inl y} eq = r

  comm-sq2cone/cosp : (sq : ℂ.comm-square) → Cone/.Obj (comm-sq2cosp sq)
  comm-sq2cone/cosp sq = record
    { L = sq.ul
    ; ar = record
         { fnc = λ {A} → fnc A
         ; nat = nat
         }
    }
    where module sq = ℂ.comm-square sq
          module csp = ℂ.cospan-dg-aux (comm-sq2cosp sq)
          open ecategory-aux-only ℂ
          fnc : (A : CspC.Obj) → || ℂ.Hom sq.ul (csp.ₒ A) ||
          fnc (inl x) = sq.down ℂ.∘ sq.left
          fnc (inr (inl x)) = sq.left
          fnc (inr (inr x)) = sq.up
          nat : {A B : CspC.Obj} (f : || CspC.Hom A B ||)
                   → fnc B ℂ.∘ ℂ.idar sq.ul ℂ.~ csp.ₐ f ℂ.∘ fnc A
          nat {inl 0₁} {inl 0₁} f = ridgen (lidggˢ r (csp.id {inl 0₁}))
          nat {inr (inl x)} {inl y} f = rid
          nat {inr (inl 0₁)} {inr (inl 0₁)} f = ridgen (lidggˢ r (csp.id {inr (inl 0₁)}))
          nat {inr (inr x)} {inl y} f = ridgen sq.sq-pf
          nat {inr (inr 0₁)} {inr (inr 0₁)} f = ridgen (lidggˢ r (csp.id {inr (inr 0₁)}))

  
  is-lim-cn2is-pb-sq : {cosp : Cospan diag-in ℂ}(sp : Cone/.Obj cosp)
                             → ℂ.is-pullback-cone sp → ℂ.is-pb-square (cone/cosp2comm-sq sp)
  is-lim-cn2is-pb-sq {cosp} sp ispbcn = record
    { ⟨_,_⟩[_] = pbcn.⟨_,_⟩[_]
    ; ×/tr₁ = pbcn.tr₁
    ; ×/tr₂ = pbcn.tr₂
    ; ×/uq = pbcn.π-jm
    }
    where module pbcn = ℂ.is-pullback-cone ispbcn

  is-pb-sq2is-lim-cn : {sq : ℂ.comm-square} → ℂ.is-pb-square sq
                           → ℂ.is-pullback-cone (comm-sq2cone/cosp sq)
  is-pb-sq2is-lim-cn {sq} ispbsq = ℂ.mk-is-pullback-cone
    (comm-sq2cone/cosp sq)
    pbsq.⟨_,_⟩[_]
    pbsq.×/tr₁
    pbsq.×/tr₂
    pbsq.×/uq
    where module pbsq = ℂ.is-pb-square ispbsq

-- end pullback-diag-props
