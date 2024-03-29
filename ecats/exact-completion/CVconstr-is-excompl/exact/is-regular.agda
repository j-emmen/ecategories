
{-# OPTIONS --without-K #-}

module ecats.exact-completion.CVconstr-is-excompl.exact.is-regular where

open import ecats.basic-defs.ecat-def&not
open import ecats.basic-defs.arrows
open import ecats.basic-props.isomorphism
open import ecats.basic-props.epi&mono-basic
open import ecats.basic-defs.image-fact
open import ecats.basic-props.image-fact
open import ecats.basic-defs.regular-ecat
open import ecats.finite-limits.all
open import ecats.exact-completion.CVconstruction
open import ecats.exact-completion.CVconstr-is-excompl.finite-limits.fin-limits
open import ecats.exact-completion.CVconstr-is-excompl.finite-limits.pullback
open import ecats.exact-completion.CVconstr-is-excompl.exact.canonical-epi&mono



----------------------------------
-- Regular epi-Mono factorisation
----------------------------------

module exact-compl-has-repi-mono-fact {ℂ : ecategory} (hasfwl : has-fin-weak-limits ℂ) where
  private
    module ℂ where
      open ecategory ℂ public
      open pseudo-eq-rel-defs ℂ public
      open can-epi&mono-defs hasfwl public
    module Exℂ where
      open ecategory Ex ℂ [ hasfwl ] public
      open comm-shapes Ex ℂ [ hasfwl ] public
      open epi&mono-defs Ex ℂ [ hasfwl ] public
      open image-fact-defs Ex ℂ [ hasfwl ] public
      open epi&mono-props-basic Ex ℂ [ hasfwl ] public
      open image-fact-props Ex ℂ [ hasfwl ] public
      open pullback-squares Ex ℂ [ hasfwl ] public

  module rem-fact-objarr {A B : Exℂ.Obj} (f : || Exℂ.Hom A B ||) where
    private
      module A = ℂ.peq A
      module B = ℂ.peq B
      module f = ℂ.peq-mor f
    cmf-data : ℂ.canonical-mono f.lo B.peqover
    cmf-data = ℂ.can-mono-over f.lo B.peqover
    module cmf = ℂ.canonical-mono cmf-data
    crf-data : ℂ.canonical-repi A.peqover cmf.Ob/
    crf-data = record
      { crepi-hi = cmf.⟨ A.%0 , f.hi , A.%1 ⟩[ f.cmptb₀ ˢ , f.cmptb₁ ˢ ]
      ; crepi-ax₀ = cmf.trl (f.cmptb₀ ˢ) (f.cmptb₁ ˢ)
      ; crepi-ax₁ = cmf.trr (f.cmptb₀ ˢ) (f.cmptb₁ ˢ)
      }
      where open ecategory-aux-only ℂ
    module crf = ℂ.canonical-repi crf-data
    rem-tr : cmf.ar Exℂ.∘ crf.ar Exℂ.~ f
    rem-tr = record { hty = B.ρ ℂ.∘ f.lo
                    ; hty₀ = ass ⊙ lidgg ridˢ B.ρ-ax₀
                    ; hty₁ = ass ⊙ lidgg r B.ρ-ax₁
                    }
                    where open ecategory-aux-only ℂ
  -- end rem-fact-objarr

  rmf-of : {A B : Exℂ.Obj} (f : || Exℂ.Hom A B ||) → Exℂ.repi-mono-fact-of f
  rmf-of f = record
         { Ob = cmf.Ob
         ; M = cmf.ar
         ; C = crf.ar
         ; tr = rem-tr
         ; isrem = record
                 { M-is-monic = cmf.ar-monic
                 ; C-is-repi = crf.can-repi-is-repi
                 }
         }
         where open rem-fact-objarr f
         
  remM-is-can-monic : {A B : Exℂ.Obj} (f : || Exℂ.Hom A B ||)
                            → ℂ.canonical-mono (ℂ.peq-mor.lo f) (ℂ.peq.peqover B)
  remM-is-can-monic f = cmf-data
                      where open rem-fact-objarr f using (cmf-data)
                         
  remC-is-can-repi : {A B : Exℂ.Obj} (f : || Exℂ.Hom A B ||)
                        → ℂ.canonical-repi (ℂ.peq.peqover A) (ℂ.peq.peqover (Exℂ.repi-mono-fact-of.Ob (rmf-of f)))
  remC-is-can-repi f = crf-data
                     where open rem-fact-objarr f using (crf-data)
-- end exact-compl-has-repi-mono-fact


------------------------------------------------
-- Exact completion has repi-mono factorisation
------------------------------------------------

ex-cmpl-rm-fact : {ℂ : ecategory} (hasfwl : has-fin-weak-limits ℂ) → has-repi-mono-fact Ex ℂ [ hasfwl ]
ex-cmpl-rm-fact {ℂ} hasfwl = record { rmf-of = rmf-of }
                           where open exact-compl-has-repi-mono-fact hasfwl



-- Regular epis are stable under pullback

module exact-compl-has-pb-stable-repis {ℂ : ecategory} (hasfwl : has-fin-weak-limits ℂ) where
  private
    module ℂ where
      open ecategory ℂ public
      open comm-shapes ℂ public
      open pseudo-eq-rel-defs ℂ public
      open can-epi&mono-defs hasfwl public
    module Exℂ where
      open ecategory Ex ℂ [ hasfwl ] public
      open comm-shapes Ex ℂ [ hasfwl ] public
      open iso-defs Ex ℂ [ hasfwl ] public
      open iso-transports Ex ℂ [ hasfwl ] public
      open epi&mono-defs Ex ℂ [ hasfwl ] public
      open epi&mono-props-basic Ex ℂ [ hasfwl ] public
      open image-fact-defs Ex ℂ [ hasfwl ] public
      open image-fact-props Ex ℂ [ hasfwl ] public
      open pullback-squares Ex ℂ [ hasfwl ] public
      open pullback-props Ex ℂ [ hasfwl ] public
    module flExℂ where
      open has-fin-limits (exact-compl-has-fin-limits hasfwl) public
      open has-pullbacks haspb public using (pb-of)
    module rmfExℂ = exact-compl-has-repi-mono-fact hasfwl
    module rmfof {A B : Exℂ.Obj} (f : || Exℂ.Hom A B ||) = Exℂ.repi-mono-fact-of (rmfExℂ.rmf-of f)
    infixr 2  _~_
    infixr 5 _∘_
    _~_ : {A B : ℂ.Obj} (f f' : || ℂ.Hom A B ||) → Set
    _~_ =  ℂ._~_
    _∘_ : {A B C : ℂ.Obj} →  || ℂ.Hom B C ||  → || ℂ.Hom A B || → || ℂ.Hom A C ||
    _∘_ = ℂ._∘_
    module ×/of = Exℂ.pullback-of-not


  -- chosen pullback of a canonical repi is a regular epi
  module pb-of-can-repi-is-repi {X : ℂ.Obj} {R S : ℂ.peqOver X} (fdata : ℂ.canonical-repi R S)
                                {A : Exℂ.Obj} (g : || Exℂ.Hom A (ℂ.mkpeq-c S) ||)
                                where
    private
      module cre = ℂ.canonical-repi fdata
      module A = ℂ.peq A
      module R = ℂ.peqOver R
      module S = ℂ.peqOver S
      module g = ℂ.peq-mor g
      g×/cre : Exℂ.pullback-of g cre.ar
      g×/cre = flExℂ.pb-of g cre.ar
      module g×/cre = Exℂ.pullback-of g×/cre
      module g*cre = ℂ.peq-mor g×/cre.π/₁
      module rmf[g*cre] = rmfof (g×/cre.π/₁)
      module Ig*cre = ℂ.peq rmf[g*cre].Ob
      module Mg*cre = ℂ.canonical-mono (rmfExℂ.remM-is-can-monic g×/cre.π/₁)
      --ℂ.is-std-Ex-monic (rmfExℂ.remM-is-std-Ex-monic g×/cre.π/₁)
    Mg*cre-is-sepi : Exℂ.is-split-epi rmf[g*cre].M
    Mg*cre-is-sepi = record
      { rinv = record
             { lo = minv-lo
             ; isext = record
               { hi = minv-hi
               ; cmptb₀ = Mg*cre.trl minv-hi₀ minv-hi₁
               ; cmptb₁ = Mg*cre.trr minv-hi₀ minv-hi₁
               }
             }
      ; rinv-ax = record
                { hty = A.ρ
                ; hty₀ = A.ρ-ax₀ ⊙ pbLo.trl minv-lo₀ minv-lo₁ ˢ
                ; hty₁ = A.ρ-ax₁
                }
      }
      where open ecategory-aux-only ℂ
            open exact-compl-has-pullbacks-from-connected hasfwl
            open peq-pb-of g cre.ar
            module peq-pbob = ℂ.peq peq-pbob
            minv-lo₀ = g.lo ∘ ℂ.idar A.Lo      ~[ lidggˢ rid S.ρ-ax₀ ⊙ assˢ ]
                       S.%0 ∘ S.ρ ∘ g.lo
            minv-lo₁ = ℂ.idar X ∘ g.lo          ~[ lidggˢ lid S.ρ-ax₁ ⊙ assˢ ]
                       S.%1 ∘ S.ρ ∘ g.lo                  
            minv-lo : || ℂ.Hom A.Lo peq-pbob.Lo ||
            minv-lo = pbLo.⟨ ℂ.idar A.Lo , S.ρ ∘ g.lo , g.lo ⟩[ minv-lo₀ , minv-lo₁ ]
            minv-hi₀ = g*cre.lo ∘ minv-lo ∘ A.%0   ~[ ass ⊙ lidgg ridˢ (pbLo.trl minv-lo₀ minv-lo₁) ]
                       A.%0 ℂ.∘ ℂ.idar A.Hi
            minv-hi₁ = g*cre.lo ∘ minv-lo ∘ A.%1   ~[ ass ⊙ lidgg ridˢ (pbLo.trl minv-lo₀ minv-lo₁) ]
                       A.%1 ℂ.∘ ℂ.idar A.Hi
            minv-hi : || ℂ.Hom A.Hi Ig*cre.Hi ||
            minv-hi = Mg*cre.⟨ minv-lo ∘ A.%0 , ℂ.idar A.Hi , minv-lo ∘ A.%1 ⟩[ minv-hi₀ , minv-hi₁ ]
    Mg*cre-is-iso : Exℂ.is-iso rmf[g*cre].M
    Mg*cre-is-iso = Exℂ.monic-sepi-is-iso (rmfof.M-is-monic g×/cre.π/₁) Mg*cre-is-sepi
    g*cre-is-repi : Exℂ.is-regular-epi g×/cre.π/₁
    g*cre-is-repi = Exℂ.iso-to-repi-is-repi-cod Mg*cre-is-iso rmf[g*cre].tr rmf[g*cre].C-is-repi
                  where module creg*cre = ℂ.canonical-repi (rmfExℂ.remC-is-can-repi g×/cre.π/₁)
  -- end pb-of-can-repi-is-repi


  -- any pullback of a canonical repi is a regular epi
  module pbsq-of-can-repi-is-repi {X : ℂ.Obj} {R S : ℂ.peqOver X} (fdata : ℂ.canonical-repi R S)
                                  {A : Exℂ.Obj} (g : || Exℂ.Hom A (ℂ.mkpeq-c S) ||)
                                  where
    private
      module cre = ℂ.canonical-repi fdata
      g×/cre : Exℂ.pullback-of g cre.ar
      g×/cre = flExℂ.pb-of g cre.ar
      module g×/cre = Exℂ.pullback-of g×/cre
      module pbof = Exℂ.pullback-of-not
    iso-tr : (pb : Exℂ.pullback-of g cre.ar) → pbof.π/₁ pb Exℂ.∘ Exℂ.pbs-unv12 g×/cre pb Exℂ.~ g×/cre.π/₁
    iso-tr pb = pbof.×/tr₁ pb g×/cre.×/sqpf
    pb-crepi-is-repi : (pb : Exℂ.pullback-of g cre.ar) → Exℂ.is-regular-epi (pbof.π/₁ pb)
    pb-crepi-is-repi pb = Exℂ.iso-to-repi-is-repi-dom (Exℂ.pbs-unv-is-iso g×/cre pb) (iso-tr pb) g*cre-is-repi
                        where open pb-of-can-repi-is-repi fdata g
  -- end pbsq-of-can-repi-is-repi


  -- any pullback of a regular epi is a regular epi
  module pbsq-of-repi-is-repi {A B : Exℂ.Obj} {f : || Exℂ.Hom A B ||} {C : Exℂ.Obj} {g : || Exℂ.Hom C B ||}
                              (g×/f : Exℂ.pullback-of g f) (frepi : Exℂ.is-regular-epi f)
                              where
    open ecategory-aux-only Ex ℂ [ hasfwl ]
    private
      module f = Exℂ.is-regular-epi frepi
      module rmff = rmfof f
      module g×/f = Exℂ.pullback-of-not g×/f
      Mf-iso : Exℂ.is-iso rmff.M
      Mf-iso = cov-pf rmff.tr rmff.M-is-monic
             where open Exℂ.is-cover (Exℂ.repi-is-cover frepi)
      module Mf = Exℂ.is-iso Mf-iso
      trf⁻¹ = Mf.⁻¹ Exℂ.∘ f ~[ ∘e (rmff.tr ˢ) r ⊙ ass {_} {rmff.Ob} {B} ⊙ lidgg r Mf.iddom
              ] rmff.C
      crf-sqpf : (Mf.⁻¹ Exℂ.∘ g) Exℂ.∘ g×/f.π/₁ Exℂ.~ rmff.C Exℂ.∘ g×/f.π/₂
      crf-sqpf = ~proof (Mf.⁻¹ Exℂ.∘ g) Exℂ.∘ g×/f.π/₁               ~[ assˢ {_} {C} {B} ⊙ ∘e g×/f.×/sqpf r ] /
                         Mf.⁻¹ Exℂ.∘ f Exℂ.∘ g×/f.π/₂                ~[ ass {_} {A} {B} ⊙ ∘e r trf⁻¹ ]∎
                         rmff.C Exℂ.∘ g×/f.π/₂ ∎
      crf-pb : Exℂ.is-pb-square (Exℂ.mksq {C} {A} (Exℂ.mksq/ crf-sqpf))
      crf-pb = Exℂ.subsq-of-pb-is-pb g×/f crf-sqpf (ass {_} {B} {rmff.Ob} ⊙ lidgg r Mf.idcod) rmff.tr
    isrepi : Exℂ.is-regular-epi g×/f.π/₁
    isrepi = pb-crepi-is-repi (Exℂ.mkpb-of crf-pb)
           where open pbsq-of-can-repi-is-repi (rmfExℂ.remC-is-can-repi f) (Mf.⁻¹ Exℂ.∘ g)
  -- end pbsq-of-repi-is-repi


  repi-is-pbof-stb : Exℂ.is-pbof-stable Exℂ.is-regular-epi
  repi-is-pbof-stb = record { pres-rl = isrepi }
                   where open pbsq-of-repi-is-repi
      
-- end exact-compl-has-pb-stable-repis



-------------------------------
-- Exact completion is regular
-------------------------------

exact-compl-is-regular : {ℂ : ecategory} (hasfwl : has-fin-weak-limits ℂ)
                            → is-regular Ex ℂ [ hasfwl ]
exact-compl-is-regular {ℂ} hasfwl = record
                                  { hasfl = exact-compl-has-fin-limits hasfwl
                                  ; hasrmf = ex-cmpl-rm-fact hasfwl
                                  ; repi-pbof-stable = repi-is-pbof-stb
                                  }
                                  where open exact-compl-has-pb-stable-repis hasfwl


exact-compl-qcart-is-regular : {ℂ : ecategory} (qcart : is-quasi-cartesian ℂ)
                                  → is-regular Ex ℂ qc[ qcart ]
exact-compl-qcart-is-regular qcart = exact-compl-is-regular (qcart→has-fwlim qcart)
