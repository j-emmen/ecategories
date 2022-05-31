
{-# OPTIONS --without-K  #-}

module ecats.exact-completion.CVconstr-is-excompl.embedding.universal-property.is-exact-fun where

open import ecats.basic-defs.ecat-def&not
open import ecats.basic-defs.arrows
open import ecats.basic-defs.image-fact
open import ecats.basic-props.epi&mono-basic
open import ecats.reg&ex
open import ecats.finite-limits.defs.collective
open import ecats.functors.defs.efunctor-d&n
open import ecats.functors.defs.natural-transformation
open import ecats.functors.defs.basic-defs
open import ecats.functors.defs.preserving-functor
open import ecats.functors.defs.left-covering
open import ecats.functors.props.basic-props
open import ecats.functors.props.left-covering
open import ecats.constructions.ecat-eqrel
open import ecats.exact-completion.CVconstruction
open import ecats.exact-completion.CVconstr-is-excompl.finite-limits.fin-limits
open import ecats.exact-completion.CVconstr-is-excompl.exact.is-regular
open import ecats.exact-completion.CVconstr-is-excompl.embedding.universal-property.def
open import ecats.exact-completion.CVconstr-is-excompl.embedding.universal-property.is-left-covering



module exact-compl-universal-is-exact {ℂ : ecategory} (hasfwl : has-fin-weak-limits ℂ) where
  private
    module ℂ where
      open ecategory ℂ public
      open pseudo-eq-rel-defs ℂ public
    module Exℂ where
      open ecategory Ex ℂ [ hasfwl ] public
      open iso-defs Ex ℂ [ hasfwl ] public
      open epi&mono-defs Ex ℂ [ hasfwl ] public
      open epi&mono-props-basic Ex ℂ [ hasfwl ] public
      open image-fact-defs Ex ℂ [ hasfwl ] public
    module CVex = efunctor-aux CVex ℂ [ hasfwl ]
  open exact-compl-universal-def hasfwl

  module extension-is-exact {𝔼 : ecategory} (ex𝔼 : is-exact 𝔼)
                            {F : efunctor ℂ 𝔼} (lcovF : is-left-covering F)
                            where
    private
      module 𝔼 where
        open ecategory 𝔼 public
        open iso-defs 𝔼 public
        open epi&mono-defs 𝔼 public
        open epi&mono-props-basic 𝔼 public
        open eq-rel-defs 𝔼 public
        open kernel-pairs-defs 𝔼 public
      module ex𝔼 where
        open exact-cat-d&p ex𝔼 public
      module F = efunctor-aux F
      module lcF = is-left-covering lcovF
      F↑ex : efunctor Ex ℂ [ hasfwl ] 𝔼
      F↑ex = ↑ex ex𝔼 lcovF
      module F↑ex = efunctor-aux F↑ex
      reg𝔼 : is-regular 𝔼
      reg𝔼 = ex𝔼.is-reg
      -- it seems that declaring reg𝔼 explicitly is crucial
      -- for typechecking Q/F↑ex.Ob A = F↑ex.ₒ A
      FRel : efunctor Ex ℂ [ hasfwl ] (EqRel 𝔼)
      FRel = Rel reg𝔼 lcovF
      module FRel where
        open efunctor-aux FRel public
        private
          module tmpOb (A : Exℂ.Obj) = 𝔼.eqrel (ₒ A)
          module tmpAr {A B : Exℂ.Obj} (f : || Exℂ.Hom A B ||) = 𝔼.eqrel-mor (ₐ f)
        open tmpOb public
        open tmpAr public
      Q/F↑ex : (A : Exℂ.Obj) → 𝔼.coeq-of (FRel.r₁ A) (FRel.r₂ A)
      Q/F↑ex A = ex𝔼.eqr-has-coeq (FRel.eqrelover A)
      module Q/F↑ex (A : Exℂ.Obj) = 𝔼.coeq-of (Q/F↑ex A)


    -- Preserves regular epis
    
    module preserves-repis {A B : Exℂ.Obj} {f : || Exℂ.Hom A B ||} (frepi : Exℂ.is-regular-epi f) where
      open ecategory-aux-only 𝔼
      private
        module A = ℂ.peq A
        module B = ℂ.peq B
        module imgf where
          open has-repi-mono-fact (ex-cmpl-rm-fact hasfwl)
          open Exℂ.repi-mono-fact-of (rmf-of f) public

      F↑Ob : 𝔼.Obj
      F↑Ob = F↑ex.ₒ imgf.Ob
      F↑C : || 𝔼.Hom (F↑ex.ₒ A) F↑Ob ||
      F↑M : || 𝔼.Hom F↑Ob (F↑ex.ₒ B) ||
      F↑C = F↑ex.ₐ imgf.C
      F↑M = F↑ex.ₐ imgf.M
      F↑tr : F↑M 𝔼.∘ F↑C 𝔼.~ F↑ex.ₐ f
      F↑tr = F↑ex.∘ax {f = imgf.C} {imgf.M} {f} imgf.tr
      M-iso : Exℂ.is-iso imgf.M
      M-iso = cov-pf imgf.tr imgf.M-is-monic
            where open Exℂ.is-cover (Exℂ.repi-is-cover frepi)
      F↑M-iso : 𝔼.is-iso F↑M
      F↑M-iso = Fpres-iso {f = imgf.M} M-iso
              where open efunctor-props F↑ex using (Fpres-iso)
                    open Exℂ.is-iso M-iso
      F↑M-repi : 𝔼.is-regular-epi F↑M
      F↑M-repi = 𝔼.split-epi-is-repi (𝔼.iso-is-split-epi F↑M-iso)

      Q/F↑A-ob Q/F↑Ob-ob : 𝔼.Obj
      Q/F↑A-ob = FRel.baseOb A
      Q/F↑Ob-ob = FRel.baseOb imgf.Ob
      Q/F↑A : || 𝔼.Hom Q/F↑A-ob (F↑ex.ₒ A) ||
      Q/F↑A = Q/F↑ex.ar A
      Q/F↑Ob : || 𝔼.Hom Q/F↑Ob-ob F↑Ob ||
      Q/F↑Ob = Q/F↑ex.ar imgf.Ob
      Q/F↑C-tr : F↑C 𝔼.∘ Q/F↑A 𝔼.~ Q/F↑Ob
      Q/F↑C-tr = ~proof F↑C 𝔼.∘ Q/F↑A                  ~[ q-sq (FRel.ₐ imgf.C) ] /
                        Q/F↑Ob 𝔼.∘ F.ₐ (ℂ.idar A.Lo)   ~[ ridgg r F.id ]∎
                        Q/F↑Ob ∎
               where open quot-of-eqrel-funct ex𝔼 using (q-sq)
      Q/F↑Ob-repi : 𝔼.is-regular-epi Q/F↑Ob
      Q/F↑Ob-repi = record { coeq = Q/F↑ex.iscoeq imgf.Ob }
      F↑C-repi : 𝔼.is-regular-epi F↑C
      F↑C-repi = ex𝔼.repi-triang Q/F↑C-tr Q/F↑Ob-repi

      F↑exf-repi : 𝔼.is-regular-epi (F↑ex.ₐ f)
      F↑exf-repi = ex𝔼.repi-cmp {f = F↑C} {F↑M} F↑C-repi F↑M-repi F↑tr
    -- end preserves-repis

    F↑ex-pres-repi : preserves-regular-epis F↑ex
    F↑ex-pres-repi = record { pres-repi-pf = F↑exf-repi }
                   where open preserves-repis

    F↑ex-pres-flim : preserves-fin-limits F↑ex
    F↑ex-pres-flim = lcov→pres-flim reg𝔼
                                     (has-flim→has-fwlim (exact-compl-has-fin-limits hasfwl))
                                     (↑ex-is-left-covering ex𝔼 lcovF)
                   where open exact-compl-universal-is-left-cov hasfwl
    
    F↑ex-is-exact : is-exact-functor F↑ex
    F↑ex-is-exact = record
      { presfl = F↑ex-pres-flim
      ; presre = F↑ex-pres-repi
      }

  -- end extension-is-exact


  ↑ex-is-exact : {𝔼 : ecategory} (ex𝔼 : is-exact 𝔼)
                 {F : efunctor ℂ 𝔼} (lcovF : is-left-covering F)
                        → is-exact-functor (↑ex ex𝔼 lcovF)
  ↑ex-is-exact ex𝔼 lcovF = F↑ex-is-exact
                          where open extension-is-exact ex𝔼 lcovF

-- end exact-compl-universal-is-exact
