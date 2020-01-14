
-- disable the K axiom:

{-# OPTIONS --without-K #-}

-- Agda version 2.5.4.1

module ecats.exact-completion.exact.is-regular where

open import ecats.basic-defs.ecat-def&not
open import ecats.basic-defs.all-arrows
open import ecats.basic-props.epi&mono
open import ecats.basic-props.image-fact
open import ecats.basic-defs.regular-ecat
{-open import ecats.basic-defs.commut-shapes
open import ecats.basic-defs.isomorphism
open import ecats.basic-defs.epi&mono
open import ecats.basic-defs.image-fact
open import ecats.basic-defs.eqv-rel-}
open import ecats.finite-limits.all
open import ecats.exact-completion.construction
open import ecats.exact-completion.finite-limits.fin-limits
open import ecats.exact-completion.finite-limits.pullback
open import ecats.exact-completion.exact.canonical-epi&mono



-----------------------
-- Image factorisation
-----------------------

module exact-compl-has-image-fact {ℂ : ecategory} (hasfwl : has-fin-weak-limits ℂ) where
  private
    module ℂ where
      open ecategory ℂ public
      open pseudo-eq-rel-defs ℂ public
      open can-epi&mono-defs hasfwl public
    module Exℂ where
      open ecategory Ex ℂ [ hasfwl ] public
      open comm-shapes Ex ℂ [ hasfwl ] public
      open epis&monos-defs Ex ℂ [ hasfwl ] public
      open image-fact-defs Ex ℂ [ hasfwl ] public
      open epis&monos-props Ex ℂ [ hasfwl ] public
      open image-fact-props Ex ℂ [ hasfwl ] public
      open pullback-squares Ex ℂ [ hasfwl ] public

  module img-fact-objarr {A B : Exℂ.Obj} (f : || Exℂ.Hom A B ||) where
    private
      module A = ℂ.Peq A
      module B = ℂ.Peq B
      module f = ℂ.Peq-mor f
      module cmf = ℂ.canonical-mono B.peqover f.lo
      module imgOb = ℂ.Peq cmf.cmPeq    
    cmf-data : ℂ.is-std-Ex-monic cmf.cmar
    cmf-data = cmf.cmar-is-std-Ex-monic
    cref-data : ℂ.canonical-repi A.peqover imgOb.peqover
    cref-data = record
      { crepi-hi = cmf-stdm.⟨ A.%0 , f.hi , A.%1 ⟩[ f.cmptb₀ ˢ , f.cmptb₁ ˢ ]
      ; crepi-ax₀ = cmf-stdm.trl (f.cmptb₀ ˢ) (f.cmptb₁ ˢ)
      ; crepi-ax₁ = cmf-stdm.trr (f.cmptb₀ ˢ) (f.cmptb₁ ˢ)
      }
      where open ecategory-aux-only ℂ
            module cmf-stdm = ℂ.is-std-Ex-monic cmf.cmar-is-std-Ex-monic
    private
      module cref = ℂ.canonical-repi cref-data
      img-tr : cmf.cmar Exℂ.∘ cref.can-repi Exℂ.~ f
      img-tr = record { hty = B.ρ ℂ.∘ f.lo
                      ; hty₀ = ass ⊙ lidgg ridˢ B.ρ-ax₀
                      ; hty₁ = ass ⊙ lidgg r B.ρ-ax₁
                      }
                      where open ecategory-aux-only ℂ
    
    is-img : Exℂ.is-img-fact img-tr
    is-img = Exℂ.repi-mono-is-img-fact img-tr cref.can-repi-is-repi cmf.cmar-is-monic
  -- end img-fact-objarr

  img-of : {A B : Exℂ.Obj} (f : || Exℂ.Hom A B ||) → Exℂ.img-fact-of f
  img-of f = record { isimg = is-img }
           where open img-fact-objarr f using (is-img)

  imgM-is-std-Ex-monic : {A B : Exℂ.Obj} (f : || Exℂ.Hom A B ||) → ℂ.is-std-Ex-monic (Exℂ.img-fact-of.M (img-of f))
  imgM-is-std-Ex-monic f = cmf-data
                         where open img-fact-objarr f using (cmf-data)

  imgC-is-can-repi : {A B : Exℂ.Obj} (f : || Exℂ.Hom A B ||)
                        → ℂ.canonical-repi (ℂ.Peq.peqover A) (ℂ.Peq.peqover (Exℂ.img-fact-of.Ob (img-of f)))
  imgC-is-can-repi f = cref-data
                     where open img-fact-objarr f using (cref-data)
-- end exact-compl-has-image-fact



--------------------------------------------
-- Exact completion has image factorisation
--------------------------------------------

ex-cmpl-img-fact : {ℂ : ecategory} (hasfwl : has-fin-weak-limits ℂ) → has-img-fact Ex ℂ [ hasfwl ]
ex-cmpl-img-fact {ℂ} hasfwl = record { img-of = img-of }
                            where open exact-compl-has-image-fact hasfwl




-- Pulling back this factorisation produces an image factorisation

module exact-compl-has-pb-stable-image-fact {ℂ : ecategory} (hasfwl : has-fin-weak-limits ℂ) where
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
      open epis&monos-defs Ex ℂ [ hasfwl ] public
      open epis&monos-props Ex ℂ [ hasfwl ] public
      open image-fact-defs Ex ℂ [ hasfwl ] public
      open image-fact-props Ex ℂ [ hasfwl ] public
      open pullback-squares Ex ℂ [ hasfwl ] public
      open pullback-props Ex ℂ [ hasfwl ] public
    module flExℂ where
      open has-fin-limits (exact-compl-has-fin-limits hasfwl) public
      open has-pullbacks haspb public using (pb-of)
    module imgExℂ = exact-compl-has-image-fact hasfwl
    module imgof {A B : Exℂ.Obj} (f : || Exℂ.Hom A B ||) = Exℂ.img-fact-of (imgExℂ.img-of f)
    infixr 2  _~_
    infixr 5 _∘_
    _~_ : {A B : ℂ.Obj} (f f' : || ℂ.Hom A B ||) → Set
    _~_ =  ℂ._~_
    _∘_ : {A B C : ℂ.Obj} →  || ℂ.Hom B C ||  → || ℂ.Hom A B || → || ℂ.Hom A C ||
    _∘_ = ℂ._∘_
    module ×/of = Exℂ.pullback-of-not



  module pb-of-can-repi-is-strepi {X : ℂ.Obj} {R S : ℂ.PeqOver X} (fdata : ℂ.canonical-repi R S)
                                  {A : Exℂ.Obj} (g : || Exℂ.Hom A (ℂ.mkpeq-c S) ||)
                                  where
    private
      module cre = ℂ.canonical-repi fdata
      module A = ℂ.Peq A
      module R = ℂ.PeqOver R
      module S = ℂ.PeqOver S
      module g = ℂ.Peq-mor g
      g×/cre : Exℂ.pullback-of g cre.can-repi
      g×/cre = flExℂ.pb-of g cre.can-repi
      module g×/cre = Exℂ.pullback-of g×/cre
      module g*cre = ℂ.Peq-mor g×/cre.π/₁
      module img[g*cre] = imgof (g×/cre.π/₁)
      module Ig*cre = ℂ.Peq img[g*cre].Ob
      module Mg*cre = ℂ.is-std-Ex-monic (imgExℂ.imgM-is-std-Ex-monic g×/cre.π/₁)

    Mg*cre-is-sepi : Exℂ.is-split-epi img[g*cre].M
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
            open Peq-pb-of g cre.can-repi
            module Peq-pbob = ℂ.Peq Peq-pbob
            minv-lo₀ = g.lo ∘ ℂ.idar A.Lo      ~[ lidggˢ rid S.ρ-ax₀ ⊙ assˢ ]
                       S.%0 ∘ S.ρ ∘ g.lo
            minv-lo₁ = ℂ.idar X ∘ g.lo          ~[ lidggˢ lid S.ρ-ax₁ ⊙ assˢ ]
                       S.%1 ∘ S.ρ ∘ g.lo                  
            minv-lo : || ℂ.Hom A.Lo Peq-pbob.Lo ||
            minv-lo = pbLo.⟨ ℂ.idar A.Lo , S.ρ ∘ g.lo , g.lo ⟩[ minv-lo₀ , minv-lo₁ ]
            minv-hi₀ = g*cre.lo ∘ minv-lo ∘ A.%0   ~[ ass ⊙ lidgg ridˢ (pbLo.trl minv-lo₀ minv-lo₁) ]
                       A.%0 ℂ.∘ ℂ.idar A.Hi
            minv-hi₁ = g*cre.lo ∘ minv-lo ∘ A.%1   ~[ ass ⊙ lidgg ridˢ (pbLo.trl minv-lo₀ minv-lo₁) ]
                       A.%1 ℂ.∘ ℂ.idar A.Hi
            minv-hi : || ℂ.Hom A.Hi Ig*cre.Hi ||
            minv-hi = Mg*cre.⟨ minv-lo ∘ A.%0 , ℂ.idar A.Hi , minv-lo ∘ A.%1 ⟩[ minv-hi₀ , minv-hi₁ ]

    Mg*cre-is-iso : Exℂ.is-iso img[g*cre].M
    Mg*cre-is-iso = Exℂ.monic-sepi-is-iso (imgof.M-is-monic g×/cre.π/₁) Mg*cre-is-sepi

    g*cre-is-strong-epi : Exℂ.is-strong-epi g×/cre.π/₁
    g*cre-is-strong-epi = trnsp-tr-codlr Mg*cre-is-iso (Exℂ.repi-is-strong creg*cre.can-repi-is-repi)
                        where open Exℂ.iso-transp Exℂ.is-strong-epi Exℂ.strepi-is-transportable
                              open iso-transp-tr-codlr (Exℂ.mktriang (imgof.tr g×/cre.π/₁))
                              module creg*cre = ℂ.canonical-repi (imgExℂ.imgC-is-can-repi g×/cre.π/₁)
  -- end pb-of-can-repi-is-strepi


  module pbsq-of-can-repi-is-strepi {X : ℂ.Obj} {R S : ℂ.PeqOver X} (fdata : ℂ.canonical-repi R S)
                                    {A : Exℂ.Obj} (g : || Exℂ.Hom A (ℂ.mkpeq-c S) ||)
                                    where
    open pb-of-can-repi-is-strepi fdata g
    private
      module cre = ℂ.canonical-repi fdata
      g×/cre : Exℂ.pullback-of g cre.can-repi
      g×/cre = flExℂ.pb-of g cre.can-repi
      module g×/cre = Exℂ.pullback-of g×/cre
      module pbof = Exℂ.pullback-of-not

    iso-tr : (pb : Exℂ.pullback-of g cre.can-repi) → pbof.π/₁ pb Exℂ.∘ Exℂ.pbs-iso-ar g×/cre pb Exℂ.~ g×/cre.π/₁
    iso-tr pb = pbof.×/tr₁ pb g×/cre.×/sqpf

    pb-crepi-is-strepi : (pb : Exℂ.pullback-of g cre.can-repi) → Exℂ.is-strong-epi (pbof.π/₁ pb)
    pb-crepi-is-strepi pb = trnsp-tr-domlr (Exℂ.pbs-iso g×/cre pb) g*cre-is-strong-epi
                              where open Exℂ.iso-transp Exℂ.is-strong-epi Exℂ.strepi-is-transportable
                                    open iso-transp-tr-domlr (Exℂ.mktriang (iso-tr pb))
  -- end pbsq-of-can-repi-is-strepi


  module can-repi-can-mono-is-pbsq-stable {A B C : Exℂ.Obj} {f : || Exℂ.Hom A B ||} {g : || Exℂ.Hom C B ||}
                                          (g×/f : Exℂ.pullback-of g f) (g×/Mf : Exℂ.pullback-of g (imgof.M f))
                                          {pbC : || Exℂ.Hom (×/of.ul g×/f) (×/of.ul g×/Mf) ||}
                                          (pbtr : ×/of.π/₁ g×/Mf Exℂ.∘ pbC Exℂ.~ ×/of.π/₁ g×/f)
                                          where
    open ecategory-aux-only Ex ℂ [ hasfwl ]
    private
      module imgf = imgof f
      module Mf = Exℂ.is-monic imgf.M-is-monic
      module g×/f = Exℂ.pullback-of-not g×/f
      module g×/Mf = Exℂ.pullback-of-not g×/Mf
      module cref = ℂ.canonical-repi (imgExℂ.imgC-is-can-repi f)
    open pbsq-of-can-repi-is-strepi (imgExℂ.imgC-is-can-repi f) g×/Mf.π/₂
    upsqpf : g×/Mf.π/₂ Exℂ.∘ pbC Exℂ.~ imgof.C f Exℂ.∘ g×/f.π/₂
    upsqpf = Mf.mono-pf (~proof
      imgf.M Exℂ.∘ g×/Mf.π/₂ Exℂ.∘ pbC      ~[ ass {_} {g×/Mf.ul} {imgf.Ob} ⊙ ∘e r (g×/Mf.×/sqpf ˢ)
                                              ⊙ assˢ {_} {g×/Mf.ul} {C} ] /
      g Exℂ.∘ g×/Mf.π/₁ Exℂ.∘ pbC           ~[ ∘e pbtr r ] /
      g Exℂ.∘ g×/f.π/₁                      ~[ g×/f.×/sqpf ⊙ ∘e r (imgf.tr ˢ) ⊙ assˢ {_} {A} {imgf.Ob} ]∎
      imgf.M Exℂ.∘ imgf.C Exℂ.∘ g×/f.π/₂ ∎)
    upsq : Exℂ.comm-square
    upsq = Exℂ.mksq (Exℂ.mksq/ {g×/Mf.ul} {imgf.Ob} {A} upsqpf)
    upispb : Exℂ.is-pb-square upsq
    upispb = upper-is-pbsq imgf.tr pbtr upsqpf
           where open Exℂ.lower-and-outer-so-upper g×/Mf g×/f
    pbimg : Exℂ.is-img-fact pbtr
    pbimg = Exℂ.strepi-mono-is-img-fact pbtr
                                        (pb-crepi-is-strepi (Exℂ.mkpb-of upispb))
                                        (Exℂ.mono-pb-stable g×/Mf.×/of imgf.M-is-monic)
  -- end can-repi-can-mono-is-pbsq-stable
    
      

  can-repi-can-mono-is-pbsq-stable : {A B C : Exℂ.Obj} {f : || Exℂ.Hom A B ||} {g : || Exℂ.Hom C B ||}
                                     (g×/f : Exℂ.pullback-of g f) (g×/Mf : Exℂ.pullback-of g (imgof.M f))
                                     {pbC : || Exℂ.Hom (×/of.ul g×/f) (×/of.ul g×/Mf) ||}
                                     (pbtr : ×/of.π/₁ g×/Mf Exℂ.∘ pbC Exℂ.~ ×/of.π/₁ g×/f)
                                     → Exℂ.img-fact-is-pb-stable (imgExℂ.img-of f) g×/f g×/Mf pbtr
  can-repi-can-mono-is-pbsq-stable {A} {B} {C} {f} {g} g×/f g×/Mf {pbC} pbtr = record
    { img-pb-stable = pbimg
    }
    where open can-repi-can-mono-is-pbsq-stable {A} {B} {C} {f} {g} g×/f g×/Mf {pbC} pbtr
-- end exact-compl-has-pb-stable-image-fact



------------------------------------------------------------
-- Exact completion has pullback-stable image factorisation
------------------------------------------------------------

ex-cmpl-pbsqst-img-fact : {ℂ : ecategory} (hasfwl : has-fin-weak-limits ℂ) → has-pb-stable-img-fact Ex ℂ [ hasfwl ]
ex-cmpl-pbsqst-img-fact {ℂ} hasfwl = record { imgfact = ex-cmpl-img-fact hasfwl
                                            ; pb-stb = can-repi-can-mono-is-pbsq-stable
                                            }
                                            where open exact-compl-has-pb-stable-image-fact hasfwl

ex-cmpl-qcart-pbsqst-img-fact : {ℂ : ecategory} (qcart : is-quasi-cartesian ℂ)
                                   → has-pb-stable-img-fact Ex ℂ qc[ qcart ]
ex-cmpl-qcart-pbsqst-img-fact {ℂ} qcart = ex-cmpl-pbsqst-img-fact (qcart→has-fwl qcart)


-------------------------------
-- Exact completion is regular
-------------------------------

exact-compl-is-regular//has-finlim : {ℂ : ecategory} (hasfwl : has-fin-weak-limits ℂ)
                                        → is-regular//has-finlim {Ex ℂ [ hasfwl ]} (exact-compl-has-fin-limits hasfwl)
exact-compl-is-regular//has-finlim {ℂ} hasfwl = record
  { pb-stb-imgfact = ex-cmpl-pbsqst-img-fact hasfwl
  }
  where open ecategory Ex ℂ [ hasfwl ]
        open exact-compl-has-image-fact hasfwl
        open can-epi&mono-defs hasfwl
        module cre {A B : Obj} (f : || Hom A B ||) = canonical-repi (imgC-is-can-repi f)


exact-compl-is-regular : {ℂ : ecategory} (hasfwl : has-fin-weak-limits ℂ)
                            → is-regular Ex ℂ [ hasfwl ]
exact-compl-is-regular hasfwl = record
  { hasfl = exact-compl-has-fin-limits hasfwl
  ; isreg/fl = exact-compl-is-regular//has-finlim hasfwl
  }



exact-compl-qcart-is-regular//has-finlim : {ℂ : ecategory} (qcart : is-quasi-cartesian ℂ)
                            → is-regular//has-finlim {Ex ℂ qc[ qcart ]} (exact-compl-qcart-has-fin-limits qcart)
exact-compl-qcart-is-regular//has-finlim qcart = exact-compl-is-regular//has-finlim (qcart→has-fwl qcart)

exact-compl-qcart-is-regular : {ℂ : ecategory} (qcart : is-quasi-cartesian ℂ)
                            → is-regular Ex ℂ qc[ qcart ]
exact-compl-qcart-is-regular qcart = exact-compl-is-regular (qcart→has-fwl qcart)
