
{-# OPTIONS --without-K #-}

module ecats.exact-completion.CVconstr-is-excompl.embedding.universal-property.uniqueness where

open import ecats.basic-defs.ecat-def&not
open import ecats.basic-defs.arrows
open import ecats.basic-props.epi&mono-basic
open import ecats.reg&ex
open import ecats.finite-limits.defs.collective
open import ecats.functors.defs.efunctor-d&n
open import ecats.functors.defs.natural-transformation
open import ecats.functors.defs.natural-iso
open import ecats.functors.defs.basic-defs
open import ecats.functors.defs.preserving-functor
open import ecats.functors.defs.left-covering
open import ecats.constructions.ecat-eqrel
open import ecats.exact-completion.CVconstruction
open import ecats.exact-completion.CVconstr-is-excompl.exact.canonical-epi&mono
open import ecats.exact-completion.CVconstr-is-excompl.embedding.universal-property.def


-- Definition of the functor Ex ℂ [ hasfwl ] → 𝔼 induced by a left covering ℂ → 𝔼 into 𝔼 exact.

module exact-compl-universal-uniq {ℂ : ecategory} (hasfwl : has-fin-weak-limits ℂ) where
  private
    module ℂ where
      open ecategory ℂ public
      open pseudo-eq-rel-defs ℂ public
      open can-epi&mono-defs hasfwl public
    module Exℂ = ecategory Ex ℂ [ hasfwl ]
    module CVex = efunctor-aux CVex ℂ [ hasfwl ]
  
  module exact-functor-determined-by-free-peq {𝔼 : ecategory} (ex𝔼 : is-exact 𝔼)
                                              {F : efunctor ℂ 𝔼} (lcovF : is-left-covering F)
                                              {G : efunctor Ex ℂ [ hasfwl ] 𝔼} (exG : is-exact-functor G)
                                              (Gtr : natural-iso (G ○ CVex ℂ [ hasfwl ]) F)
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
      module ER𝔼 = ecategory (EqRel 𝔼)
      module F = efunctor-aux F
      module lcF = is-left-covering lcovF
      module G = efunctor-aux G
      module exG = is-exact-functor exG
      module F↑ex = efunctor-aux (F CV↑ex[ hasfwl , ex𝔼 , lcovF ])
      reg𝔼 : is-regular 𝔼
      reg𝔼 = ex𝔼.is-reg
      -- it seems that declaring reg𝔼 explicitly is crucial
      -- for typechecking F↑ex-coeq.Ob A = F↑ex.ₒ A
      FRel : efunctor Ex ℂ [ hasfwl ] (EqRel 𝔼)
      FRel = Peq2Rel hasfwl reg𝔼 lcovF
      FRel-sq : natural-iso (FRel ○ CVex ℂ [ hasfwl ]) (ΔER 𝔼 ○ F)
      FRel-sq = Peq2Rel-sq hasfwl reg𝔼 lcovF
      module FRel where
        open efunctor-aux FRel public
        private
          module tmpOb (A : Exℂ.Obj) = 𝔼.eqrel (ₒ A)
          module tmpAr {A B : Exℂ.Obj} (f : || Exℂ.Hom A B ||) = 𝔼.eqrel-mor (ₐ f)
        open tmpOb public
        open tmpAr public
      module Q = efunctor-aux (QER ex𝔼)
      module GΓex = efunctor (G ○ CVex ℂ [ hasfwl ])
      module GΓex≅F = natural-iso Gtr
      module cxs = ℂ.canonical-ex-seq
      module CRF% (A : Exℂ.Obj) where
        open eqrel-from-peq-funct hasfwl
        open eqrel-from-peq-via-left-covering reg𝔼 lcovF
        open eqrel-as-repi-mono-fact A public
        open rmfF% public
        open CF% public
      F↑ex-coeq : (A : Exℂ.Obj) → 𝔼.coeq-of (FRel.r₁ A) (FRel.r₂ A)
      F↑ex-coeq A = ex𝔼.eqr-has-coeq (FRel.eqrelover A)
      module F↑ex-coeq (A : Exℂ.Obj) = 𝔼.coeq-of (F↑ex-coeq A)

    Gcxs-is-exs : (A : Exℂ.Obj) → 𝔼.is-exact-seq (G.ₐ (cxs.kp₁ A)) (G.ₐ (cxs.kp₂ A)) (G.ₐ (cxs.cre.ar A))
    Gcxs-is-exs A = exG.pres-ex-seq-pf {cxs.kpOb A} {cxs.freeLo A} {A} (cxs.isexseq A)
    private module Gcxs (A : Exℂ.Obj) = 𝔼.is-exact-seq (Gcxs-is-exs A)
    
    Gcre-coeq-of-GΓex : (A : Exℂ.Obj) → 𝔼.is-coeq (G.ₐ (CVex.ₐ (ℂ.peq.%0 A))) (G.ₐ (CVex.ₐ (ℂ.peq.%1 A))) (G.ₐ (cxs.cre.ar A))
    Gcre-coeq-of-GΓex A = 𝔼.epi/coeq-so-coeq {G.ₒ (cxs.kpOb A)} {G.ₒ (CVex.ₒ A.Lo)} {G.ₒ A}
                                              {G.ₐ (cxs.kp₁ A)} {G.ₐ (cxs.kp₂ A)} {R' = G.ₒ (CVex.ₒ A.Hi)}
                                              {G.ₐ (cxs.cc.ar A)} (𝔼.repi-is-epic Gcc-repi)
                                              (G.∘ax (cxs.cc.tr₁ A)) (G.∘ax (cxs.cc.tr₂ A))
                                              (Gcxs.iscoeq A)
                        where module A = ℂ.peq A
                              Gcc-repi : 𝔼.is-regular-epi (G.ₐ (cxs.cc.ar A))
                              Gcc-repi = exG.pres-repi-pf (cxs.cc.can-repi-is-repi A)
    private module GΓex-coeq (A : Exℂ.Obj) = 𝔼.coeq-of (𝔼.mkcoeq-of (Gcre-coeq-of-GΓex A))
    F↑ex-coeq-of-F : (A : Exℂ.Obj) → 𝔼.is-coeq (F.ₐ (ℂ.peq.%0 A)) (F.ₐ (ℂ.peq.%1 A)) (F↑ex-coeq.ar A)
    F↑ex-coeq-of-F A = 𝔼.epi/coeq-so-coeq (𝔼.repi-is-epic (CRF%.C-is-repi A))
                                          (CRF%.rmfF%tr₁ A)
                                          (CRF%.rmfF%tr₂ A)
                                          (F↑ex-coeq.iscoeq A)

    private
      module fnc (A : Exℂ.Obj) where
        open 𝔼.uniq-of-coequalisers (Gcre-coeq-of-GΓex A)
        private module A = ℂ.peq A
        isoHi : 𝔼.is-iso (GΓex≅F.fnc {A.Hi})
        isoHi = (𝔼.mkis-iso (GΓex≅F.isiso {A.Hi}))
        isoLo : 𝔼.is-iso (GΓex≅F.fnc {A.Lo})
        isoLo = (𝔼.mkis-iso (GΓex≅F.isiso {A.Lo}))
        open iso-rel-so-iso-coeq (F↑ex-coeq-of-F A) isoHi isoLo (GΓex≅F.nat A.%0) (GΓex≅F.nat A.%1)
                                 public
      -- end fnc

    Γexsq : {A B : Exℂ.Obj} (f : || Exℂ.Hom A B ||)
               → f Exℂ.∘ cxs.cre.ar A Exℂ.~ cxs.cre.ar B Exℂ.∘ CVex.ₐ (ℂ.peq-mor.lo f)
    Γexsq {A} {B} f = record
      { hty = B.ρ ℂ.∘ f.lo
      ; hty₀ = ass ⊙ lidgg ridˢ B.ρ-ax₀
      ; hty₁ = ass ⊙ lidgg lidˢ B.ρ-ax₁
      
      }
      where open ecategory-aux-only ℂ
            module A = ℂ.peq A
            module B = ℂ.peq B
            module f = ℂ.peq-mor f

    γ : natural-transformation G (F CV↑ex[ hasfwl , ex𝔼 , lcovF ])
    γ = record
      { fnc = λ {A} → fnc.ar A
      ; nat = λ {A} {B} f → GΓex-coeq.epi-pf A (~proof
        (fnc.ar B 𝔼.∘ G.ₐ f) 𝔼.∘ GΓex-coeq.ar A                                ~[ assˢ ⊙ ∘e (G.∘∘ (Γexsq f)) r ] /
        fnc.ar B 𝔼.∘ GΓex-coeq.ar B 𝔼.∘ GΓex.ₐ (ℂ.peq-mor.lo f)                ~[ ass ⊙ ∘e r (fnc.ar-sq B) ⊙ assˢ ] /
        F↑ex-coeq.ar B 𝔼.∘ GΓex≅F.fnc {ℂ.peq.Lo B} 𝔼.∘ GΓex.ₐ (ℂ.peq-mor.lo f) ~[ ∘e (GΓex≅F.nat (ℂ.peq-mor.lo f)) r ] /
        F↑ex-coeq.ar B 𝔼.∘ (FRel.base-ar f) 𝔼.∘ GΓex≅F.fnc {ℂ.peq.Lo A}           ~[ ass ⊙ ∘e r (q-sq (FRel.ₐ f) ˢ) ⊙ assˢ ] /
        F↑ex.ₐ f 𝔼.∘ F↑ex-coeq.ar A 𝔼.∘ GΓex≅F.fnc {ℂ.peq.Lo A}                ~[ ∘e (fnc.ar-sq A ˢ) r ⊙ ass ]∎
        (F↑ex.ₐ f 𝔼.∘ fnc.ar A) 𝔼.∘ GΓex-coeq.ar A ∎)
      -- 
      }
      where open ecategory-aux-only 𝔼
            open quot-of-eqrel-funct ex𝔼

    γ⁻¹ : natural-transformation (F CV↑ex[ hasfwl , ex𝔼 , lcovF ]) G
    γ⁻¹ = record
      { fnc = λ {A} → fnc.ar⁻¹ A
      ; nat = λ {A} {B} f → F↑ex-coeq.epi-pf A (~proof
        (fnc.ar⁻¹ B 𝔼.∘ F↑ex.ₐ f) 𝔼.∘ F↑ex-coeq.ar A                             ~[ assˢ ⊙ ∘e (q-sq (FRel.ₐ f)) r ] /
        fnc.ar⁻¹ B 𝔼.∘ F↑ex-coeq.ar B 𝔼.∘ FRel.base-ar f                            ~[ ass ⊙ ∘e r (fnc.ar⁻¹-sq B) ⊙ assˢ ] /
        GΓex-coeq.ar B 𝔼.∘ GΓex≅F.fnc⁻¹ {ℂ.peq.Lo B} 𝔼.∘ FRel.base-ar f             ~[ ∘e (GΓex≅F.nat⁻¹ (ℂ.peq-mor.lo f)) r ] /
        GΓex-coeq.ar B 𝔼.∘ GΓex.ₐ (ℂ.peq-mor.lo f) 𝔼.∘ GΓex≅F.fnc⁻¹ {ℂ.peq.Lo A} ~[ ass ⊙ ∘e r (G.∘∘ (Γexsq f) ˢ) ⊙ assˢ ] /
        G.ₐ f 𝔼.∘ GΓex-coeq.ar A 𝔼.∘ GΓex≅F.fnc⁻¹ {ℂ.peq.Lo A}                   ~[ ∘e (fnc.ar⁻¹-sq A ˢ) r ⊙ ass ]∎
        (G.ₐ f 𝔼.∘ fnc.ar⁻¹ A) 𝔼.∘ F↑ex-coeq.ar A ∎)
      }
      where open ecategory-aux-only 𝔼
            open quot-of-eqrel-funct ex𝔼

    G≅F↑ex : natural-iso G (F CV↑ex[ hasfwl , ex𝔼 , lcovF ])
    G≅F↑ex = record
      { natt = γ
      ; natt⁻¹ = γ⁻¹
      ; isiso = λ {A} → fnc.isop A
      }
  -- end exact-functor-determined-by-free-peq

  CV↑ex-uq : {𝔼 : ecategory} (ex𝔼 : is-exact 𝔼)
           {F : efunctor ℂ 𝔼} (lcovF : is-left-covering F)
           {G : efunctor Ex ℂ [ hasfwl ] 𝔼} (exG : is-exact-functor G)
           (Gtr : natural-iso (G ○ CVex ℂ [ hasfwl ]) F)
             → natural-iso G (F CV↑ex[ hasfwl , ex𝔼 , lcovF ])
  CV↑ex-uq ex𝔼 lcovF exG Gtr = G≅F↑ex
                            where open exact-functor-determined-by-free-peq ex𝔼 lcovF exG Gtr  
-- end exact-compl-universal-uniq
