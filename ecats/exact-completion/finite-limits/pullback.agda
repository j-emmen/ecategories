
-- disable the K axiom:

{-# OPTIONS --without-K #-}

-- Agda version 2.5.4.1

module ecats.exact-completion.finite-limits.pullback where

open import ecats.basic-defs.ecat-def&not
open import ecats.basic-defs.commut-shapes
open import ecats.basic-defs.epi&mono
open import ecats.basic-defs.eqv-rel
open import ecats.finite-limits.defs.collective
open import ecats.finite-limits.props.relations-among-weak-limits
open import ecats.finite-limits.d&n-pullback
open import ecats.finite-limits.d&n-weak-pullback
open import ecats.finite-limits.props.weak-pullback
open import ecats.finite-limits.defs.weak-Wlimit
open import ecats.finite-limits.defs.weak-bow
--open import ecats.functors.defs.efunctor
open import ecats.exact-completion.CVconstruction
open import ecats.exact-completion.exact.canonical-epi&mono

-- Pullbacks

module exact-compl-has-pullbacks-from-connected {ℂ : ecategory} (hasfwl : has-fin-weak-limits ℂ) where
  private
    module ℂ where
      open ecategory ℂ public
      open comm-shapes ℂ public
      open pseudo-eq-rel-defs ℂ public
      open wpullback-squares ℂ public
      open weak-pullback-props ℂ public
      open weak-bow-defs ℂ public
    module fwlℂ where
      open has-fin-weak-limits hasfwl public using (haswpb; haswbw)
      open has-weak-pullbacks haswpb public using (wpb-of)
      open has-weak-bows haswbw public using (wbw-of)
      open has-weak-Wlimits (has-wpb⇒has-wWlim haswpb) public
    module Exℂ where
      open ecategory Ex ℂ [ hasfwl ] public
      open comm-shapes Ex ℂ [ hasfwl ] public
      open epis&monos-defs Ex ℂ [ hasfwl ] public
      open pullback-squares Ex ℂ [ hasfwl ] public
    infixr 2  _~_
    infixr 5 _∘_
    _~_ : {A B : ℂ.Obj} (f f' : || ℂ.Hom A B ||) → Set
    _~_ =  ℂ._~_
    _∘_ : {A B C : ℂ.Obj} →  || ℂ.Hom B C ||  → || ℂ.Hom A B || → || ℂ.Hom A C ||
    _∘_ = ℂ._∘_


  module Peq-pb-of {R S T : Exℂ.Obj} (f : || Exℂ.Hom R T ||) (g : || Exℂ.Hom S T ||) where
    open can-epi&mono-defs hasfwl
    private
      module R = ℂ.Peq R
      module S = ℂ.Peq S
      module T = ℂ.Peq T
      module f = ℂ.Peq-mor f
      module g = ℂ.Peq-mor g
    module pbLo = fwlℂ.wW-of f.lo T.sp/ g.lo
    module Hisp where
      open canonical-mono-sp R.peqover S.peqover (ℂ.mkspan/ pbLo.πl pbLo.πr) public
      open Exℂ.span/ cmsp public
    private
      module π/₁ = ℂ.Peq-mor Hisp.a1
      module π/₂ = ℂ.Peq-mor Hisp.a2

    Peq-pbob : Exℂ.Obj
    Peq-pbob = Hisp.O12

    Peq-π/₁ : || Exℂ.Hom Peq-pbob R ||
    Peq-π/₁ = Hisp.a1
    Peq-π/₂ : || Exℂ.Hom Peq-pbob S ||
    Peq-π/₂ = Hisp.a2
    Peq-sqpf : f Exℂ.∘ Peq-π/₁ Exℂ.~ g Exℂ.∘ Peq-π/₂
    Peq-sqpf = record
             { hty = pbLo.πc
             ; hty₀ = pbLo.sqpfl ˢ
             ; hty₁ = pbLo.sqpfr ˢ
             }
             where open ecategory-aux-only ℂ

    module Peq-univ (U : Exℂ.Obj) (h : || Exℂ.Hom U R ||) (k : || Exℂ.Hom U S ||)
                    (pf : f Exℂ.∘ h Exℂ.~ g Exℂ.∘ k)
                    where
      open ecategory-aux-only ℂ
      private
        module U = ℂ.Peq U
        module h = ℂ.Peq-mor h
        module k = ℂ.Peq-mor k
        module pf = ℂ.Peq-mor-eq pf
        module stdm = is-Ex-monic-sp Hisp.cmsp-is-Ex-monic
        unlo : || ℂ.Hom U.Lo pbLo.wWOb ||
        unlo = pbLo.⟨ h.lo , pf.hty , k.lo ⟩[ pf.hty₀ ˢ , pf.hty₁ ˢ ]
        unhi₁₀ = π/₁.lo ∘ unlo ∘ U.%0    ~[ ass ⊙ ∘e r (pbLo.trl (pf.hty₀ ˢ) (pf.hty₁ ˢ)) ⊙ h.cmptb₀ ˢ ]
                 R.%0 ∘ h.hi
        unhi₁₁ = π/₁.lo ∘ unlo ∘ U.%1    ~[ ass ⊙ ∘e r (pbLo.trl (pf.hty₀ ˢ) (pf.hty₁ ˢ)) ⊙ h.cmptb₁ ˢ ]
                 R.%1 ∘ h.hi
        unhi₂₀ = π/₂.lo ∘ unlo ∘ U.%0    ~[ ass ⊙ ∘e r (pbLo.trr (pf.hty₀ ˢ) (pf.hty₁ ˢ)) ⊙ k.cmptb₀ ˢ ]
                 S.%0 ∘ k.hi
        unhi₂₁ = π/₂.lo ∘ unlo ∘ U.%1    ~[ ass ⊙ ∘e r (pbLo.trr (pf.hty₀ ˢ) (pf.hty₁ ˢ)) ⊙ k.cmptb₁ ˢ ]
                 S.%1 ∘ k.hi
      Peq-univ : || Exℂ.Hom U Peq-pbob ||
      Peq-univ = record
        { lo = unlo
        ; isext = record
          { hi = stdm.⟨ unlo ∘ U.%0 , h.hi , k.hi , unlo ∘ U.%1 ⟩[ unhi₁₀ , unhi₁₁ , unhi₂₀ , unhi₂₁ ]
          ; cmptb₀ = stdm.trl₀ unhi₁₀ unhi₁₁ unhi₂₀ unhi₂₁
          ; cmptb₁ = stdm.trl₁ unhi₁₀ unhi₁₁ unhi₂₀ unhi₂₁
          }
        }

      Peq-tr₁ : Peq-π/₁ Exℂ.∘ Peq-univ Exℂ.~ h
      Peq-tr₁ = ℂ.Peq-mor-eq-ext (pbLo.trl (pf.hty₀ ˢ) (pf.hty₁ ˢ))
      Peq-tr₂ : Peq-π/₂ Exℂ.∘ Peq-univ Exℂ.~ k
      Peq-tr₂ = ℂ.Peq-mor-eq-ext (pbLo.trr (pf.hty₀ ˢ) (pf.hty₁ ˢ))
    -- end Peq-univ

    Peq-sq/ : Exℂ.square/cosp f g
    Peq-sq/ = Exℂ.mksq/ Peq-sqpf
    Peq-is-pbsq : Exℂ.is-pb-square (Exℂ.mksq Peq-sq/)
    Peq-is-pbsq = record
      { ⟨_,_⟩[_] = λ {U} h k → Peq-univ U h k
      ; ×/tr₁ = λ {U} {h} {k} → Peq-tr₁ U h k
      ; ×/tr₂ = λ {U} {h} {k} → Peq-tr₂ U h k
      ; ×/uq = λ {U} {h} {h'} pf₁ pf₂ → stdm-jm.jm-pf {U} {h} {h'} pf₁ pf₂
      }
      where open Peq-univ
            module stdm-jm = Exℂ.is-jointly-monic/ Hisp.cmsp-is-jm/
            
    Peq-pb-of : Exℂ.pullback-of f g
    Peq-pb-of = record
              { ×/sq/ = Peq-sq/
              ; ×/ispbsq = Peq-is-pbsq
              }
  -- end Peq-pb-of

  ex-cmpl-pb : has-pullbacks Ex ℂ [ hasfwl ]
  ex-cmpl-pb = record { pb-of = Peq-pb-of }
             where open Peq-pb-of using (Peq-pb-of)
  
-- end exact-compl-has-pullbacks-from-connected


exact-compl-has-pullbacks : {ℂ : ecategory} (hasfwl : has-fin-weak-limits ℂ) → has-pullbacks Ex ℂ [ hasfwl ]
exact-compl-has-pullbacks hasfwl = ex-cmpl-pb
                                where open exact-compl-has-pullbacks-from-connected hasfwl using (ex-cmpl-pb)

exact-compl-qcart-has-pullbacks : {ℂ : ecategory} (qcart : is-quasi-cartesian ℂ) → has-pullbacks Ex ℂ qc[ qcart ]
exact-compl-qcart-has-pullbacks qcart = exact-compl-has-pullbacks (qcart→has-fwlim qcart)
