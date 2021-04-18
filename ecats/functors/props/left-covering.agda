
{-# OPTIONS --without-K #-}

module ecats.functors.props.left-covering where

open import ecats.basic-defs.ecat-def&not
open import ecats.arrows
open import ecats.reg&ex
open import ecats.finite-limits.all
open import ecats.functors.defs.efunctor-d&n
open import ecats.functors.defs.natural-transformation
open import ecats.functors.defs.basic-defs
open import ecats.functors.defs.preserving-functor
open import ecats.functors.defs.left-covering



-- Relationship between left covering and preservations properties when the target category is regular.
-- See after the module for a collection of theorems.

module left-cov-relations-into-regular-cat {ℂ 𝔼 : ecategory} (F : efunctor ℂ 𝔼) (regE : is-regular 𝔼) where
  private
    module ℂ where
      open ecategory ℂ public
      open comm-shapes ℂ public
      open epi&mono-d&p ℂ public
      --open epis&monos-props ℂ public
      open finite-limits-d&p ℂ public
      open finite-weak-limits-d&p ℂ public
      open limits→weak-limits ℂ public
      --open relations-among-limit-diagrams ℂ public
    module 𝔼 where
      open ecategory 𝔼 public
      open comm-shapes 𝔼 public
      open iso-d&p 𝔼 public
      open epi&mono-d&p 𝔼 public
      open finite-limits-d&p 𝔼 public
      open finite-weak-limits-d&p 𝔼 public
      open limits→weak-limits 𝔼 public
      open relations-among-limit-diagrams 𝔼 public
    module r𝔼 where
      open is-regular regE public
      open has-terminal hastrm public
      open has-bin-products hasprd using (prd-of) public
      open has-equalisers haseql using (eql-of) public
      open has-pullbacks haspb using (pb-of) public
      open has-bows hasbw using (bw-of) public
      open regular-cat-props regE public
    module F = efunctor-aux F


  -- Proofs that a left covering in some limits is left covering in some other.


  -- This module proves lc-×+eql→lc-pb when ℂ has binary products.
  -- Next module proves it when ℂ has weak products and weak equalisers.
  
  module w/prd-lc-prd-eql2lc-pb (prdC : has-bin-products ℂ)
                                (lcprd : is-left-covering-prd F) (lceql : is-left-covering-eql F)
                                where
    open is-left-covering-prd lcprd
    open is-left-covering-eql lceql
    open has-bin-products prdC using (prd-of)
    private
      module wpbof = ℂ.wpullback-of
      module wpbsq = ℂ.wpullback-sq
      module pbof = 𝔼.pullback-of
      module pbsq = 𝔼.pb-square
      module weqlof = ℂ.wequaliser-of
      module eqlof = 𝔼.equaliser-of

    module pbuniv-is-repi {X Y Z : ℂ.Obj} {f : || ℂ.Hom X Z ||} {g : || ℂ.Hom Y Z ||}
                          (wpbC : ℂ.wpullback-of f g) (pbE : 𝔼.pullback-of (F.ₐ f) (F.ₐ g))
                          {covpb : || 𝔼.Hom (F.ₒ (wpbof.ul wpbC)) (pbof.ul pbE) ||}
                          (tr₁ : pbof.π/₁ pbE 𝔼.∘ covpb 𝔼.~ F.ₐ (wpbof.wπ/₁ wpbC))
                          (tr₂ : pbof.π/₂ pbE 𝔼.∘ covpb 𝔼.~ F.ₐ (wpbof.wπ/₂ wpbC))
                          where
      private
        module wpbC = ℂ.wpullback-of-not wpbC
        module pbE = 𝔼.pullback-of-not pbE
        X×Y : ℂ.product-of X Y
        X×Y = prd-of X Y
        FX×FY : 𝔼.product-of (F.ₒ X) (F.ₒ Y)
        FX×FY = r𝔼.prd-of (F.ₒ X) (F.ₒ Y)
        module X×Y = ℂ.product-of-not X×Y
        module FX×FY = 𝔼.product-of-not FX×FY
      weql : ℂ.wequaliser-of (f ℂ.∘ X×Y.π₁) (g ℂ.∘ X×Y.π₂)
      weql = ℂ.wpbof2weqlof X×Y.×of wpbC
      eqlF : 𝔼.equaliser-of (F.ₐ (f ℂ.∘ X×Y.π₁)) (F.ₐ (g ℂ.∘ X×Y.π₂))
      eqlF = r𝔼.eql-of (F.ₐ (f ℂ.∘ X×Y.π₁)) (F.ₐ (g ℂ.∘ X×Y.π₂))
      private
        module weql = ℂ.wequaliser-of weql
        module eqlF = 𝔼.equaliser-of eqlF

      coveqlF-pf = F.∘∘ (~proof (f ℂ.∘ X×Y.π₁) ℂ.∘ X×Y.< wpbC.wπ/₁ , wpbC.wπ/₂ >   ~[ assˢ ⊙ ∘e X×Y.×tr₁ r ] /
                               f ℂ.∘ wpbC.wπ/₁                             ~[ wpbC.w×/sqpf ] /
                               g ℂ.∘ wpbC.wπ/₂                             ~[ ∘e (X×Y.×tr₂ˢ {f = wpbC.wπ/₁}) r ⊙ ass ]∎
                               (g ℂ.∘ X×Y.π₂) ℂ.∘ X×Y.< wpbC.wπ/₁ , wpbC.wπ/₂ > ∎)
                 where open ecategory-aux-only ℂ
      coveqlF : || 𝔼.Hom (F.ₒ wpbC.ul) eqlF.Eql ||
      coveqlF = F.ₐ (X×Y.< wpbC.wπ/₁ , wpbC.wπ/₂ >) eqlF.|eql[ coveqlF-pf ]
      coveqlF-repi : 𝔼.is-regular-epi coveqlF
      coveqlF-repi = eqluniv-is-repi weql eqlF (eqlF.eqltr coveqlF-pf)

      eqlD : 𝔼.equaliser-of (F.ₐ f 𝔼.∘ FX×FY.π₁) (F.ₐ g 𝔼.∘ FX×FY.π₂)
      eqlD = 𝔼.pbof→eqlofπ's FX×FY.×of pbE
      private module eqlD = 𝔼.equaliser-of eqlD
      covprd : || 𝔼.Hom (F.ₒ X×Y.O12) FX×FY.O12 ||
      covprd = FX×FY.< F.ₐ X×Y.π₁ , F.ₐ X×Y.π₂ >
      covprd-repi : 𝔼.is-regular-epi covprd
      covprd-repi = prduniv-is-repi (ℂ.prd-of⇒wprd-of X×Y.×of) FX×FY.×of FX×FY.×tr₁ FX×FY.×tr₂

      coveqlD-pf : (F.ₐ f 𝔼.∘ FX×FY.π₁) 𝔼.∘ covprd 𝔼.∘ eqlF.eqlar
                        𝔼.~ (F.ₐ g 𝔼.∘ FX×FY.π₂) 𝔼.∘ covprd 𝔼.∘ eqlF.eqlar
      coveqlD-pf = epi-pf (~proof
        ((F.ₐ f 𝔼.∘ FX×FY.π₁) 𝔼.∘ covprd 𝔼.∘ eqlF.eqlar) 𝔼.∘ coveqlF
                              ~[ ∘e r ass ⊙ assˢ ⊙ ∘e (eqlF.eqltr coveqlF-pf) (assˢ ⊙ ∘e FX×FY.×tr₁ r) ] /
        (F.ₐ f 𝔼.∘ F.ₐ X×Y.π₁) 𝔼.∘ F.ₐ (X×Y.< wpbC.wπ/₁ , wpbC.wπ/₂ >)
                              ~[ ∘e r F.∘ax-rf ⊙ coveqlF-pf ⊙ ∘e r F.∘ax-rfˢ ] /
        (F.ₐ g 𝔼.∘ F.ₐ X×Y.π₂) 𝔼.∘ F.ₐ (X×Y.< wpbC.wπ/₁ , wpbC.wπ/₂ >)
           ~[ ∘e (eqlF.eqltr coveqlF-pf ˢ) (∘e (FX×FY.×tr₂ˢ {f = F.ₐ X×Y.π₁}) r ⊙ ass) ⊙ ass ⊙ ∘e r assˢ ]∎
        ((F.ₐ g 𝔼.∘ FX×FY.π₂) 𝔼.∘ covprd 𝔼.∘ eqlF.eqlar) 𝔼.∘ coveqlF ∎)
                 where open 𝔼.is-epic (𝔼.repi-is-epic coveqlF-repi)
                       open ecategory-aux-only 𝔼
      coveqlD : || 𝔼.Hom eqlF.Eql eqlD.Eql ||
      coveqlD = (covprd 𝔼.∘ eqlF.eqlar) eqlD.|eql[ coveqlD-pf ]
      coveqlD-pb : 𝔼.pullback-of eqlD.eqlar covprd
      coveqlD-pb = record
        { ×/sq/ = 𝔼.mksq/ (eqlD.eqltr coveqlD-pf)
        ; ×/ispbsq = record
                   { ⟨_,_⟩[_] = λ h k pf → eqlF._|eql[_] k (⟨⟩pf pf)
                   ; ×/tr₁ = λ pf → eqlD.eqluq (ass ⊙ ∘e r (eqlD.eqltr coveqlD-pf) ⊙ assˢ ⊙ ∘e (eqlF.eqltr (⟨⟩pf pf)) r ⊙ pf ˢ)
                   ; ×/tr₂ = λ pf → eqlF.eqltr (⟨⟩pf pf)
                   ; ×/uq = λ pf1 pf2 → eqlF.eqluq pf2
                   }
        }
        where open ecategory-aux-only 𝔼
              ⟨⟩pf : {C : 𝔼.Obj} {h : || 𝔼.Hom C eqlD.Eql ||} {k : || 𝔼.Hom C (F.ₒ X×Y.O12) ||}
                     (pf : eqlD.eqlar 𝔼.∘ h 𝔼.~ covprd 𝔼.∘ k)
                       → F.ₐ (f ℂ.∘ X×Y.π₁) 𝔼.∘ k 𝔼.~ F.ₐ (g ℂ.∘ X×Y.π₂) 𝔼.∘ k
              ⟨⟩pf {C} {h} {k} pf = ~proof
                   F.ₐ (f ℂ.∘ X×Y.π₁) 𝔼.∘ k
                      ~[ ∘e r (F.∘ax-rfˢ ⊙ ∘e (FX×FY.×tr₁ˢ {g = F.ₐ X×Y.π₂}) r) ⊙ assˢ ⊙ ∘e assˢ r ] /
                   F.ₐ f 𝔼.∘ FX×FY.π₁ 𝔼.∘ covprd 𝔼.∘ k          ~[ ass ⊙ ∘e (pf ˢ) r ] /
                   (F.ₐ f 𝔼.∘ FX×FY.π₁) 𝔼.∘ eqlD.eqlar 𝔼.∘ h    ~[ ass ⊙ ∘e r eqlD.eqleq ⊙ assˢ ] /
                   (F.ₐ g 𝔼.∘ FX×FY.π₂) 𝔼.∘ eqlD.eqlar 𝔼.∘ h    ~[ ∘e pf r ⊙ assˢ ] /
                   F.ₐ g 𝔼.∘ FX×FY.π₂ 𝔼.∘ covprd 𝔼.∘ k
                                            ~[ ∘e (ass ⊙ ∘e r FX×FY.×tr₂) r ⊙ ass ⊙ ∘e r F.∘ax-rf ]∎
                   F.ₐ (g ℂ.∘ X×Y.π₂) 𝔼.∘ k ∎
      coveqlD-repi : 𝔼.is-regular-epi coveqlD
      coveqlD-repi = pres-rl coveqlD-pb covprd-repi
                   where open 𝔼.is-pbof-stable r𝔼.repi-pbof-stable

      covtr : coveqlD 𝔼.∘ coveqlF 𝔼.~ covpb
      covtr = eqlD.eqluq (~proof
        eqlD.eqlar 𝔼.∘ coveqlD 𝔼.∘ coveqlF      ~[ ass ⊙ ∘e r (eqlD.eqltr coveqlD-pf) ⊙ assˢ ] /
        covprd 𝔼.∘ eqlF.eqlar 𝔼.∘ coveqlF       ~[ ∘e (eqlF.eqltr coveqlF-pf) r ] /
        covprd 𝔼.∘ F.ₐ (X×Y.< wpbC.wπ/₁ , wpbC.wπ/₂ >)
                           ~[ FX×FY.<>ar~<>ar (F.∘ax X×Y.×tr₁ ⊙ tr₁ ˢ) (F.∘ax X×Y.×tr₂ ⊙ tr₂ ˢ) ]∎
        eqlD.eqlar 𝔼.∘ covpb ∎ )
            where open ecategory-aux-only 𝔼
      covpb-repi : 𝔼.is-regular-epi covpb
      covpb-repi =  r𝔼.repi-cmp coveqlF-repi coveqlD-repi covtr      
    -- end pbuniv-is-repi
    
    lcpb : is-left-covering-pb F
    lcpb = record
      { pbuniv-is-repi = covpb-repi
      }
      where open pbuniv-is-repi
  -- end w/prd-lc-prd-eql2lc-pb



  ×→[lcov-×+eql→lcov-×/] : (prdC : has-bin-products ℂ) 
                                 → is-left-covering-prd F → is-left-covering-eql F
                                   → is-left-covering-pb F
  ×→[lcov-×+eql→lcov-×/] prdC lc× lceql = lcpb
                                          where open w/prd-lc-prd-eql2lc-pb prdC lc× lceql









  module lc-prd-eql2lc-pb (C-has-wprd : has-bin-weak-products ℂ) (C-has-weql : has-weak-equalisers ℂ)
                          (lcprd : is-left-covering-prd F) (lceql : is-left-covering-eql F)
                          where
    open has-bin-weak-products C-has-wprd using (wprd-of)
    open has-weak-equalisers C-has-weql using (weql-of)
    open is-left-covering-prd lcprd
    open is-left-covering-eql lceql
    private
      module wpbof = ℂ.wpullback-of
      module wpbsq = ℂ.wpullback-sq
      module pbof = 𝔼.pullback-of
      module pbsq = 𝔼.pb-square
      module weqlof = ℂ.wequaliser-of
      module eqlof = 𝔼.equaliser-of
      

    module pbuniv-is-repi {X Y Z : ℂ.Obj} {f : || ℂ.Hom X Z ||} {g : || ℂ.Hom Y Z ||}
                          (wpbC : ℂ.wpullback-of f g) (pbE : 𝔼.pullback-of (F.ₐ f) (F.ₐ g))
                          {covpb : || 𝔼.Hom (F.ₒ (wpbof.ul wpbC)) (pbof.ul pbE) ||}
                          (tr₁ : pbof.π/₁ pbE 𝔼.∘ covpb 𝔼.~ F.ₐ (wpbof.wπ/₁ wpbC))
                          (tr₂ : pbof.π/₂ pbE 𝔼.∘ covpb 𝔼.~ F.ₐ (wpbof.wπ/₂ wpbC))
                          where

      Xw×Y : ℂ.wproduct-of X Y
      Xw×Y = wprd-of X Y
      FX×FY : 𝔼.product-of (F.ₒ X) (F.ₒ Y)
      FX×FY = r𝔼.prd-of (F.ₒ X) (F.ₒ Y)
      private
        module Xw×Y = ℂ.wproduct-of-not Xw×Y
        module FX×FY = 𝔼.product-of-not FX×FY
        module fw×g = ℂ.wpullback-of-not wpbC
        module eql = 𝔼.equaliser-of (𝔼.pbof→eqlofπ's FX×FY pbE)
        -- this is Ff×Fg turned into an equaliser
      
      fwπ gwπ : || ℂ.Hom Xw×Y.O12 Z ||
      fwπ = f ℂ.∘ Xw×Y.wπ₁
      gwπ = g ℂ.∘ Xw×Y.wπ₂
      Ffπ Fgπ : || 𝔼.Hom FX×FY.O12 (F.ₒ Z) ||
      Ffπ = F.ₐ f 𝔼.∘ FX×FY.π₁
      Fgπ = F.ₐ g 𝔼.∘ FX×FY.π₂
      weql : ℂ.wequaliser-of fwπ gwπ
      weql = weql-of fwπ gwπ
      eqlF : 𝔼.equaliser-of (F.ₐ fwπ) (F.ₐ gwπ)
      eqlF = r𝔼.eql-of (F.ₐ fwπ) (F.ₐ gwπ)      
      private
        module weql = ℂ.wequaliser-of weql
        module eqlF = 𝔼.equaliser-of eqlF

      med-ar-pf : f ℂ.∘ Xw×Y.wπ₁ ℂ.∘ weql.weqlar ℂ.~ g ℂ.∘ Xw×Y.wπ₂ ℂ.∘ weql.weqlar
      med-ar-pf = ass ⊙ weql.weqleq ⊙ assˢ
                where open ecategory-aux-only ℂ
      med-ar : || ℂ.Hom weql.wEql fw×g.ul ||
      med-ar = fw×g.w⟨ Xw×Y.wπ₁ ℂ.∘ weql.weqlar , Xw×Y.wπ₂ ℂ.∘ weql.weqlar ⟩[ med-ar-pf ]

      covprd : || 𝔼.Hom (F.ₒ Xw×Y.O12) FX×FY.O12 ||
      covprd = FX×FY.< F.ₐ Xw×Y.wπ₁ , F.ₐ Xw×Y.wπ₂ >
      covprd-repi : 𝔼.is-regular-epi covprd
      covprd-repi = prduniv-is-repi Xw×Y FX×FY FX×FY.×tr₁ FX×FY.×tr₂
      covf-pf : Ffπ 𝔼.∘ covprd 𝔼.~ F.ₐ fwπ
      covf-pf = ~proof Ffπ 𝔼.∘ covprd         ~[ assˢ ⊙ ∘e FX×FY.×tr₁ r ] /
                       F.ₐ f 𝔼.∘ F.ₐ Xw×Y.wπ₁    ~[ F.∘ax-rf ]∎
                       F.ₐ fwπ ∎
              where open ecategory-aux-only 𝔼
      covg-pf : Fgπ 𝔼.∘ covprd 𝔼.~ F.ₐ gwπ
      covg-pf = ~proof Fgπ 𝔼.∘ covprd         ~[ assˢ ⊙ ∘e FX×FY.×tr₂ r ] /
                       F.ₐ g 𝔼.∘ F.ₐ Xw×Y.wπ₂    ~[ F.∘ax-rf ]∎
                       F.ₐ gwπ ∎
              where open ecategory-aux-only 𝔼
      coveqlF : || 𝔼.Hom (F.ₒ weql.wEql) eqlF.Eql ||
      coveqlF = F.ₐ weql.weqlar  eqlF.|eql[ F.∘∘ weql.weqleq ]
      coveqlF-repi : 𝔼.is-regular-epi coveqlF
      coveqlF-repi = eqluniv-is-repi weql eqlF (eqlF.eqltr (F.∘∘ weql.weqleq))

      covEql-pf = ~proof Ffπ 𝔼.∘ covprd 𝔼.∘ eqlF.eqlar       ~[ ass ⊙ ∘e r covf-pf ] /
                         F.ₐ fwπ 𝔼.∘ eqlF.eqlar              ~[ eqlF.eqleq ] /
                         F.ₐ gwπ 𝔼.∘ eqlF.eqlar              ~[ ∘e r (covg-pf ˢ) ⊙ assˢ ]∎
                         Fgπ 𝔼.∘ covprd 𝔼.∘ eqlF.eqlar ∎
                where open ecategory-aux-only 𝔼

      covEql : || 𝔼.Hom eqlF.Eql eql.Eql ||
      covEql = (covprd 𝔼.∘ eqlF.eqlar) eql.|eql[ covEql-pf ]
      covEql-sq : 𝔼.comm-square
      covEql-sq = 𝔼.mksq (𝔼.mksq/ (eql.eqltr covEql-pf))
      
      covEql-pb : 𝔼.pullback-of eql.eqlar covprd
      covEql-pb = record
        { ×/sq/ = 𝔼.mksq/ (eql.eqltr covEql-pf)
        ; ×/ispbsq = record
          { ⟨_,_⟩[_] = λ h k pf → un {_} {h} {k} pf
          ; ×/tr₁ = λ {_} {h} {k} pf → eql.eqluq (~proof
                  eql.eqlar 𝔼.∘ covEql 𝔼.∘ un pf            ~[ ass ⊙ ∘e r (eql.eqltr covEql-pf) ⊙ assˢ ] /
                  covprd 𝔼.∘ eqlF.eqlar 𝔼.∘ un pf           ~[ ∘e (eqlF.eqltr (un-pf pf)) r ] /
                  covprd 𝔼.∘ k                             ~[ pf ˢ ]∎
                  eql.eqlar 𝔼.∘ h ∎)
          ; ×/tr₂ = λ pf → eqlF.eqltr (un-pf pf)
          ; ×/uq = λ _ pf₂ → eqlF.eqluq pf₂
          }
        }
        where open ecategory-aux-only 𝔼
              un-pf : {C : 𝔼.Obj} {h : || 𝔼.Hom C eql.Eql ||} {k : || 𝔼.Hom C (F.ₒ Xw×Y.O12) ||}
                      (pf : eql.eqlar 𝔼.∘ h 𝔼.~ covprd 𝔼.∘ k)
                        → F.ₐ fwπ 𝔼.∘ k 𝔼.~ F.ₐ gwπ 𝔼.∘ k
              un-pf {_} {h} {k} pf = ~proof F.ₐ fwπ 𝔼.∘ k               ~[ ∘e r (covf-pf ˢ) ⊙ assˢ ] /
                                            Ffπ 𝔼.∘ covprd 𝔼.∘ k        ~[ ∘e (pf ˢ) r ] /
                                            Ffπ 𝔼.∘ eql.eqlar 𝔼.∘ h     ~[ ass ⊙ ∘e r eql.eqleq ⊙ assˢ ] /
                                            Fgπ 𝔼.∘ eql.eqlar 𝔼.∘ h     ~[ ∘e pf r ] /
                                            Fgπ 𝔼.∘ covprd 𝔼.∘ k        ~[ ass ⊙ ∘e r covg-pf ]∎
                                            F.ₐ gwπ 𝔼.∘ k ∎
              
              un : {C : 𝔼.Obj} {h : || 𝔼.Hom C eql.Eql ||} {k : || 𝔼.Hom C (F.ₒ Xw×Y.O12) ||} (pf : eql.eqlar 𝔼.∘ h 𝔼.~ covprd 𝔼.∘ k)
                       → || 𝔼.Hom C eqlF.Eql ||
              un {_} {h} {k} pf = k eqlF.|eql[ un-pf pf ]

      covEql-repi : 𝔼.is-regular-epi covEql
      covEql-repi = pres-rl covEql-pb covprd-repi
                  where open 𝔼.is-pbof-stable r𝔼.repi-pbof-stable
      covcovE-repi : 𝔼.is-regular-epi (covEql 𝔼.∘ coveqlF)
      covcovE-repi = ∘c covEql-repi coveqlF-repi
                   where open is-ecat-congr r𝔼.regular-epi-is-congr
      covpb-pf : covpb 𝔼.∘ F.ₐ med-ar 𝔼.~ covEql 𝔼.∘ coveqlF
      covpb-pf = eql.eqluq (~proof
        eql.eqlar 𝔼.∘ covpb 𝔼.∘ F.ₐ med-ar            ~[ ass ⊙ ∘e r (FX×FY.<>ar~<> tr₁ tr₂) ] /
        FX×FY.< F.ₐ fw×g.wπ/₁ , F.ₐ fw×g.wπ/₂ > 𝔼.∘  F.ₐ med-ar
                    ~[ FX×FY.<>ar~<>ar (F.∘∘ (fw×g.w×/tr₁ med-ar-pf)) (F.∘∘ (fw×g.w×/tr₂ med-ar-pf)) ] /
        covprd 𝔼.∘ F.ₐ weql.weqlar                     ~[ ∘e (eqlF.eqltr (F.∘∘ weql.weqleq) ˢ) r ] /
        covprd 𝔼.∘ eqlF.eqlar 𝔼.∘ coveqlF             ~[ ass ⊙ ∘e r (eql.eqltr covEql-pf ˢ) ⊙ assˢ ]∎
        eql.eqlar 𝔼.∘ covEql 𝔼.∘ coveqlF ∎)
                where open ecategory-aux-only 𝔼
      covpb-repi : 𝔼.is-regular-epi covpb
      covpb-repi = r𝔼.repi-triang covpb-pf covcovE-repi      
    -- end pbuniv-is-repi
    
    lc-pb : is-left-covering-pb F
    lc-pb = record
      { pbuniv-is-repi = covpb-repi
      }
      where open pbuniv-is-repi
  -- end lc-prd-eql2lc-pb




  lcov-×+eql→lcov-×/ : (wprdC : has-bin-weak-products ℂ) (weqlC : has-weak-equalisers ℂ) 
                          → is-left-covering-prd F → is-left-covering-eql F
                            → is-left-covering-pb F
  lcov-×+eql→lcov-×/ wprdC weqlC lc× lceql = lc-pb
                                            where open lc-prd-eql2lc-pb wprdC weqlC lc× lceql










  module lc-eql-pb2lc-bw (Cweql : has-weak-equalisers ℂ) (Cwpb : has-weak-pullbacks ℂ)
                         (lceql : is-left-covering-eql F) (lcpb : is-left-covering-pb F)
                         where
    open has-weak-equalisers Cweql using (weql-of)
    open has-weak-pullbacks Cwpb using (wpb-of)
    open is-left-covering-pb lcpb
    open is-left-covering-eql lceql
    private
      module wbwof = ℂ.wbow-of
      module bwof = 𝔼.bow-of

    module bwuniv-is-repi {DL DR : ℂ.Obj} {sp₁ sp₂ : ℂ.span/ DL DR} (wbw : ℂ.wbow-of sp₁ sp₂)
                          (bw : 𝔼.bow-of (F.span/ sp₁) (F.span/ sp₂))
                          {covbw : || 𝔼.Hom (F.ₒ (wbwof.Ob wbw)) (bwof.Ob bw) ||}
                          (pf₁ : bwof.π//₁ bw 𝔼.∘ covbw 𝔼.~ F.ₐ (wbwof.wπ//₁ wbw))
                          (pf₂ : bwof.π//₂ bw 𝔼.∘ covbw 𝔼.~ F.ₐ (wbwof.wπ//₂ wbw))
                          where
      private
        module wbw-aux = weql+wpb⇒wbw.wbows-from-weql+wpb Cweql Cwpb
        module sp₁ = ℂ.span/ sp₁
        module sp₂ = ℂ.span/ sp₂
        module Fsp₁ = 𝔼.span/ (F.span/ sp₁)
        module Fsp₂ = 𝔼.span/ (F.span/ sp₂)
        module wbw = ℂ.wbow-of wbw
        module wbwc = ℂ.wbow-of (wbw-aux.wbw-of sp₁ sp₂)
        module bw = 𝔼.bow-of bw
        module wpba1 = ℂ.wpullback-of-not (wbw-aux.wpb-a1 sp₁ sp₂)
        module weqla2 = ℂ.wequaliser-of (wbw-aux.weql-a2 sp₁ sp₂)
        module pbFa1 = 𝔼.pullback-of-not (r𝔼.pb-of Fsp₁.a1 Fsp₂.a1)
        module eqlFa2 = 𝔼.equaliser-of (r𝔼.eql-of (F.ₐ (sp₁.a2 ℂ.∘ wpba1.wπ/₁)) (F.ₐ (sp₂.a2 ℂ.∘ wpba1.wπ/₂)))

      med-wbw-pf₁ : sp₁.a1 ℂ.∘ wpba1.wπ/₁ ℂ.∘ weqla2.weqlar ℂ.~ sp₂.a1 ℂ.∘ wpba1.wπ/₂ ℂ.∘ weqla2.weqlar
      med-wbw-pf₁ = ass ⊙ ∘e r wpba1.w×/sqpf ⊙ assˢ
                  where open ecategory-aux-only ℂ
      med-wbw-pf₂ : sp₁.a2 ℂ.∘ wpba1.wπ/₁ ℂ.∘ weqla2.weqlar ℂ.~ sp₂.a2 ℂ.∘ wpba1.wπ/₂ ℂ.∘ weqla2.weqlar
      med-wbw-pf₂ = ass ⊙ weqla2.weqleq ⊙ assˢ
                  where open ecategory-aux-only ℂ      
      med-wbw : || ℂ.Hom weqla2.wEql wbw.Ob ||
      med-wbw = wbw.⟨ wpba1.wπ/₁ ℂ.∘ weqla2.weqlar , wpba1.wπ/₂ ℂ.∘ weqla2.weqlar ⟩[ med-wbw-pf₁ , med-wbw-pf₂ ]
      med-bw : || 𝔼.Hom bw.Ob pbFa1.ul ||
      med-bw = pbFa1.⟨ bw.π//₁ , bw.π//₂ ⟩[ bw.sqpf₁ ]

      covEql : || 𝔼.Hom (F.ₒ weqla2.wEql) eqlFa2.Eql ||
      covEql = F.ₐ weqla2.weqlar eqlFa2.|eql[ F.∘∘ weqla2.weqleq ]
      covEql-repi : 𝔼.is-regular-epi covEql
      covEql-repi = eqluniv-is-repi (wbw-aux.weql-a2 sp₁ sp₂)
                                    (r𝔼.eql-of (F.ₐ (sp₁.a2 ℂ.∘ wpba1.wπ/₁)) (F.ₐ (sp₂.a2 ℂ.∘ wpba1.wπ/₂)))
                                    (eqlFa2.eqltr (F.∘∘ weqla2.weqleq))

      covPb : || 𝔼.Hom (F.ₒ wpba1.ul) pbFa1.ul ||
      covPb = pbFa1.⟨ F.ₐ wpba1.wπ/₁ , F.ₐ wpba1.wπ/₂ ⟩[ F.∘∘ wpba1.w×/sqpf ]
      covPb-repi : 𝔼.is-regular-epi covPb
      covPb-repi = pbuniv-is-repi (wbw-aux.wpb-a1 sp₁ sp₂)
                                  (r𝔼.pb-of Fsp₁.a1 Fsp₂.a1)
                                  (pbFa1.×/tr₁ (F.∘∘ wpba1.w×/sqpf))
                                  (pbFa1.×/tr₂ (F.∘∘ wpba1.w×/sqpf))

      covBw-pf₁ : F.ₐ sp₁.a1 𝔼.∘ F.ₐ wpba1.wπ/₁ 𝔼.∘ eqlFa2.eqlar 𝔼.~ F.ₐ sp₂.a1 𝔼.∘ F.ₐ wpba1.wπ/₂ 𝔼.∘ eqlFa2.eqlar
      covBw-pf₁ = ass ⊙ ∘e r (F.∘∘ wpba1.w×/sqpf) ⊙ assˢ
                where open ecategory-aux-only 𝔼
      covBw-pf₂ : F.ₐ sp₁.a2 𝔼.∘ F.ₐ wpba1.wπ/₁ 𝔼.∘ eqlFa2.eqlar 𝔼.~ F.ₐ sp₂.a2 𝔼.∘ F.ₐ wpba1.wπ/₂ 𝔼.∘ eqlFa2.eqlar
      covBw-pf₂ = ass ⊙ ∘e r F.∘ax-rf ⊙ eqlFa2.eqleq ⊙ ∘e r F.∘ax-rfˢ ⊙ assˢ 
                where open ecategory-aux-only 𝔼
      covBw : || 𝔼.Hom eqlFa2.Eql bw.Ob ||
      covBw = bw.⟨ F.ₐ wpba1.wπ/₁ 𝔼.∘ eqlFa2.eqlar , F.ₐ wpba1.wπ/₂ 𝔼.∘ eqlFa2.eqlar ⟩[ covBw-pf₁ , covBw-pf₂ ]      
      covBw-sq-aux₁ : bw.π//₁ 𝔼.∘ covBw 𝔼.~ pbFa1.π/₁ 𝔼.∘ covPb 𝔼.∘ eqlFa2.eqlar
      covBw-sq-aux₁ = ~proof bw.π//₁ 𝔼.∘ covBw                     ~[ bw.tr₁ covBw-pf₁ covBw-pf₂ ] /
                             F.ₐ wpba1.wπ/₁ 𝔼.∘ eqlFa2.eqlar        ~[ ∘e r (pbFa1.×/tr₁ (F.∘∘ wpba1.w×/sqpf) ˢ) ⊙ assˢ ]∎
                             pbFa1.π/₁ 𝔼.∘ covPb 𝔼.∘ eqlFa2.eqlar ∎
                    where open ecategory-aux-only 𝔼
      covBw-sq-aux₂ : bw.π//₂ 𝔼.∘ covBw 𝔼.~ pbFa1.π/₂ 𝔼.∘ covPb 𝔼.∘ eqlFa2.eqlar
      covBw-sq-aux₂ = ~proof bw.π//₂ 𝔼.∘ covBw                     ~[ bw.tr₂ covBw-pf₁ covBw-pf₂ ] /
                             F.ₐ wpba1.wπ/₂ 𝔼.∘ eqlFa2.eqlar        ~[ ∘e r (pbFa1.×/tr₂ (F.∘∘ wpba1.w×/sqpf) ˢ) ⊙ assˢ ]∎
                             pbFa1.π/₂ 𝔼.∘ covPb 𝔼.∘ eqlFa2.eqlar ∎
                    where open ecategory-aux-only 𝔼
      covBw-sqpf : med-bw 𝔼.∘ covBw 𝔼.~ covPb 𝔼.∘ eqlFa2.eqlar
      covBw-sqpf = pbFa1.×/uq (~proof pbFa1.π/₁ 𝔼.∘ med-bw 𝔼.∘ covBw         ~[ ass ⊙ ∘e r (pbFa1.×/tr₁ bw.sqpf₁) ] /
                                      bw.π//₁ 𝔼.∘ covBw                     ~[ covBw-sq-aux₁ ]∎
                                      pbFa1.π/₁ 𝔼.∘ covPb 𝔼.∘ eqlFa2.eqlar ∎)
                              (~proof pbFa1.π/₂ 𝔼.∘ med-bw 𝔼.∘ covBw         ~[ ass ⊙ ∘e r (pbFa1.×/tr₂ bw.sqpf₁) ] /
                                      bw.π//₂ 𝔼.∘ covBw                     ~[ covBw-sq-aux₂ ]∎
                                      pbFa1.π/₂ 𝔼.∘ covPb 𝔼.∘ eqlFa2.eqlar ∎)
                 where open ecategory-aux-only 𝔼
      covBw-ispb : 𝔼.is-pb-square (𝔼.mksq (𝔼.mksq/ covBw-sqpf))
      covBw-ispb = record
        { ⟨_,_⟩[_] = λ h k pf → k eqlFa2.|eql[ un-pf pf ]
        ; ×/tr₁ = tr₁-pf
        ; ×/tr₂ = λ pf → eqlFa2.eqltr (un-pf pf)
        ; ×/uq = λ _ pf₂ → eqlFa2.eqluq pf₂
        }
        where open ecategory-aux-only 𝔼
              un-pf : {C : 𝔼.Obj} {h : || 𝔼.Hom C bw.Ob ||} {k : || 𝔼.Hom C (F.ₒ wpba1.ul) ||} (pf : med-bw 𝔼.∘ h 𝔼.~ covPb 𝔼.∘ k)
                         → F.ₐ (sp₁.a2 ℂ.∘ wpba1.wπ/₁) 𝔼.∘ k 𝔼.~ F.ₐ (sp₂.a2 ℂ.∘ wpba1.wπ/₂) 𝔼.∘ k
              un-pf {_} {h} {k} pf = ~proof
                F.ₐ (sp₁.a2 ℂ.∘ wpba1.wπ/₁) 𝔼.∘ k                  ~[ ∘e r (F.∘ax-rfˢ ⊙ ∘e (pbFa1.×/tr₁ (F.∘∘ wpba1.w×/sqpf) ˢ) r) ⊙ assˢ ] /
                F.ₐ sp₁.a2 𝔼.∘ (pbFa1.π/₁ 𝔼.∘ covPb) 𝔼.∘ k          ~[ ∘e (assˢ ⊙ ∘e (pf ˢ) r ⊙ ass) r ] /
                F.ₐ sp₁.a2 𝔼.∘ (pbFa1.π/₁ 𝔼.∘ med-bw) 𝔼.∘ h         ~[ ∘e (∘e r (pbFa1.×/tr₁ bw.sqpf₁)) r ] /
                F.ₐ sp₁.a2 𝔼.∘ bw.π//₁ 𝔼.∘ h                       ~[ ass ⊙ ∘e r bw.sqpf₂ ⊙ assˢ ] /
                F.ₐ sp₂.a2 𝔼.∘ bw.π//₂ 𝔼.∘ h                       ~[ ∘e (∘e r (pbFa1.×/tr₂ bw.sqpf₁ ˢ)) r ] /
                F.ₐ sp₂.a2 𝔼.∘ (pbFa1.π/₂ 𝔼.∘ med-bw) 𝔼.∘ h         ~[ ∘e (assˢ ⊙ ∘e pf r ⊙ ass) r ] /
                F.ₐ sp₂.a2 𝔼.∘ (pbFa1.π/₂ 𝔼.∘ covPb) 𝔼.∘ k          ~[ ass ⊙ ∘e r (∘e (pbFa1.×/tr₂ (F.∘∘ wpba1.w×/sqpf)) r ⊙ F.∘ax-rf) ]∎
                F.ₐ (sp₂.a2 ℂ.∘ wpba1.wπ/₂) 𝔼.∘ k ∎

              tr₁-pf : {C : 𝔼.Obj} {h : || 𝔼.Hom C bw.Ob ||} {k : || 𝔼.Hom C (F.ₒ wpba1.ul) ||} (pf : med-bw 𝔼.∘ h 𝔼.~ covPb 𝔼.∘ k)
                          → covBw 𝔼.∘ k eqlFa2.|eql[ un-pf pf ] 𝔼.~ h
              tr₁-pf {_} {h} {k} pf = bw.uq
                (~proof bw.π//₁ 𝔼.∘ covBw 𝔼.∘ k eqlFa2.|eql[ un-pf pf ]                     ~[ ass ⊙ ∘e r covBw-sq-aux₁ ⊙ assˢ ⊙ ∘e assˢ r ] /
                        pbFa1.π/₁ 𝔼.∘ covPb 𝔼.∘ eqlFa2.eqlar 𝔼.∘ k eqlFa2.|eql[ un-pf pf ]   ~[ ∘e (∘e (eqlFa2.eqltr (un-pf pf)) r) r ] /
                        pbFa1.π/₁ 𝔼.∘ covPb 𝔼.∘ k                                           ~[ ∘e (pf ˢ) r ] /
                        pbFa1.π/₁ 𝔼.∘ med-bw 𝔼.∘ h                                          ~[ ass ⊙ ∘e r (pbFa1.×/tr₁ bw.sqpf₁) ]∎
                        bw.π//₁ 𝔼.∘ h ∎)
                (~proof bw.π//₂ 𝔼.∘ covBw 𝔼.∘ k eqlFa2.|eql[ un-pf pf ]                     ~[ ass ⊙ ∘e r covBw-sq-aux₂ ⊙ assˢ ⊙ ∘e assˢ r ] /
                        pbFa1.π/₂ 𝔼.∘ covPb 𝔼.∘ eqlFa2.eqlar 𝔼.∘ k eqlFa2.|eql[ un-pf pf ]   ~[ ∘e (∘e (eqlFa2.eqltr (un-pf pf)) r) r ] /
                        pbFa1.π/₂ 𝔼.∘ covPb 𝔼.∘ k                                           ~[ ∘e (pf ˢ) r ] /
                        pbFa1.π/₂ 𝔼.∘ med-bw 𝔼.∘ h                                          ~[ ass ⊙ ∘e r (pbFa1.×/tr₂ bw.sqpf₁) ]∎
                        bw.π//₂ 𝔼.∘ h ∎)

      covBw-pbsq : 𝔼.pb-square
      covBw-pbsq =  record
        { ×/sq = (𝔼.mksq (𝔼.mksq/ covBw-sqpf))
        ; ×/ispbsq = covBw-ispb
        }
      covBw-repi : 𝔼.is-regular-epi covBw
      covBw-repi = pres-rl covBw-pbsq covPb-repi
                 where open 𝔼.is-pbsq-stable r𝔼.repi-pbsq-stable

      cov-eq : covbw 𝔼.∘ F.ₐ med-wbw 𝔼.~ covBw 𝔼.∘ covEql
      cov-eq = bw.uq
        (~proof bw.π//₁ 𝔼.∘ covbw 𝔼.∘ F.ₐ med-wbw              ~[ ass ⊙ ∘e r pf₁ ] /
                F.ₐ wbw.wπ//₁ 𝔼.∘ F.ₐ med-wbw                  ~[ F.∘∘ (wbw.tr₁ med-wbw-pf₁ med-wbw-pf₂) ] /
                F.ₐ wpba1.wπ/₁ 𝔼.∘ F.ₐ weqla2.weqlar           ~[ ∘e (eqlFa2.eqltr (F.∘∘ weqla2.weqleq) ˢ) r ] /
                F.ₐ wpba1.wπ/₁ 𝔼.∘ eqlFa2.eqlar 𝔼.∘ covEql     ~[ ass ⊙ ∘e r (bw.tr₁ covBw-pf₁ covBw-pf₂ ˢ) ⊙ assˢ ]∎
                bw.π//₁ 𝔼.∘ covBw 𝔼.∘ covEql ∎)
        (~proof bw.π//₂ 𝔼.∘ covbw 𝔼.∘ F.ₐ med-wbw              ~[ ass ⊙ ∘e r pf₂ ] /
                F.ₐ wbw.wπ//₂ 𝔼.∘ F.ₐ med-wbw                  ~[ F.∘∘ (wbw.tr₂ med-wbw-pf₁ med-wbw-pf₂) ] /
                F.ₐ wpba1.wπ/₂ 𝔼.∘ F.ₐ weqla2.weqlar           ~[ ∘e (eqlFa2.eqltr (F.∘∘ weqla2.weqleq) ˢ) r ] /
                F.ₐ wpba1.wπ/₂ 𝔼.∘ eqlFa2.eqlar 𝔼.∘ covEql     ~[ ass ⊙ ∘e r (bw.tr₂ covBw-pf₁ covBw-pf₂ ˢ) ⊙ assˢ ]∎
                bw.π//₂ 𝔼.∘ covBw 𝔼.∘ covEql ∎)
             where open ecategory-aux-only 𝔼
      covbw-repi : 𝔼.is-regular-epi covbw
      covbw-repi = r𝔼.repi-triang cov-eq (∘c covBw-repi covEql-repi)
                 where open is-ecat-congr r𝔼.regular-epi-is-congr      
    -- end bwuniv-is-repi

    is-lcbw : is-left-covering-bw F
    is-lcbw = record
      { bwuniv-is-repi = covbw-repi
      }
      where open bwuniv-is-repi
  -- end lc-eql-pb2lc-bw



  lcov-eql+pb→lcov-bw : (Cweql : has-weak-equalisers ℂ) (Cwpb : has-weak-pullbacks ℂ) 
                           → is-left-covering-eql F → is-left-covering-pb F
                             →  is-left-covering-bw F
  lcov-eql+pb→lcov-bw weqlC wpbC lceql lcpb = is-lcbw
                                                  where open lc-eql-pb2lc-bw weqlC wpbC lceql lcpb








  -- Proofs that a left covering preserves stuff


  module lc-bw2pres-jm (Cwbw : has-weak-bows ℂ)  (lcbw : is-left-covering-bw F)
                       where
    open is-left-covering-bw lcbw
    open has-weak-bows Cwbw using (wbw-of)

    module pres-jointly-monic {X Y : ℂ.Obj} {sp/ : ℂ.span/ X Y} (isjm/ : ℂ.is-jointly-monic/ sp/) where
      Fsp : 𝔼.span/ (F.ₒ X) (F.ₒ Y)
      Fsp = F.span/ sp/
      trkp : ℂ.bow-of sp/ sp/
      trkp = record { is-bw = ℂ.jm/→idiskpsp/ isjm/ }
      kpsp : 𝔼.bow-of Fsp Fsp
      kpsp = r𝔼.bw-of Fsp Fsp
      private
        module sp where
          open ℂ.span/ sp/ public
          open ℂ.is-jointly-monic/ isjm/ public
        module Fsp = 𝔼.span/ Fsp
        module trkp = ℂ.bow-of trkp
        module kpsp = 𝔼.bow-of kpsp
      covbw : || 𝔼.Hom (F.ₒ sp.O12) kpsp.Ob ||
      covbw = kpsp.⟨ F.ₐ trkp.π//₁ , F.ₐ trkp.π//₂ ⟩[ F.∘∘ trkp.sqpf₁ , F.∘∘ trkp.sqpf₂ ]
      covbw-repi : 𝔼.is-regular-epi covbw
      covbw-repi = bwuniv-is-repi (ℂ.bw-of→wbw-of trkp)
                                  kpsp
                                  (kpsp.tr₁ (F.∘∘ trkp.sqpf₁) (F.∘∘ trkp.sqpf₂))
                                  (kpsp.tr₂ (F.∘∘ trkp.sqpf₁) (F.∘∘ trkp.sqpf₂))
      private module cbw = 𝔼.is-regular-epi covbw-repi
      kp₁~kp₂ : kpsp.π//₁ 𝔼.~ kpsp.π//₂
      kp₁~kp₂ = cbw.epi-pf (kpsp.tr₁ (F.∘∘ trkp.sqpf₁) (F.∘∘ trkp.sqpf₂) ⊙ kpsp.tr₂ (F.∘∘ trkp.sqpf₁) (F.∘∘ trkp.sqpf₂) ˢ)
              where open ecategory-aux-only 𝔼              
      Fsp-is-jm/ : 𝔼.is-jointly-monic/ Fsp
      Fsp-is-jm/ = 𝔼.π//₁~π//₂→jm/ kpsp kp₁~kp₂      
    -- end pres-jointly-monic

    pres-jm/ : preserves-jointly-monic/ F
    pres-jm/ = record
             { pres-jm/-pf = Fsp-is-jm/
             }
             where open pres-jointly-monic
  -- end lc-bw2pres-jm
                                                                                                         

  lcov-bw→pres-jm/ : (Cwbw : has-weak-bows ℂ) 
                           → is-left-covering-bw F → preserves-jointly-monic/ F
  lcov-bw→pres-jm/ wbwC lcbw = pres-jm/
                              where open lc-bw2pres-jm wbwC lcbw



  module lc-eql-pb2pres-jm (Cweql : has-weak-equalisers ℂ) (Cwpb : has-weak-pullbacks ℂ)
                            (lceql : is-left-covering-eql F) (lcpb : is-left-covering-pb F)
                           = lc-bw2pres-jm (has-weql+wpb⇒has-wbw Cweql Cwpb)
                                           (lcov-eql+pb→lcov-bw Cweql Cwpb lceql lcpb)

  lcov-eql+pb→pres-jm/ : (Cweql : has-weak-equalisers ℂ) (Cwpb : has-weak-pullbacks ℂ) 
                            → is-left-covering-eql F → is-left-covering-pb F
                              → preserves-jointly-monic/ F
  lcov-eql+pb→pres-jm/ weqlC wpbC lceql lcpb = pres-jm/
                                              where open lc-eql-pb2pres-jm weqlC wpbC lceql lcpb

  
  module lc-prd-eql2pres-jm (wprdC : has-bin-weak-products ℂ) (weqlC : has-weak-equalisers ℂ)
                             (lcprd : is-left-covering-prd F) (lceql : is-left-covering-eql F) =
                            lc-eql-pb2pres-jm weqlC
                                              (has-wprd+weql⇒has-wpb wprdC weqlC)
                                              lceql
                                              (lcov-×+eql→lcov-×/ wprdC weqlC lcprd lceql)


  lcov-prd+eql→pres-jm/ : (Cwprd : has-bin-weak-products ℂ) (Cweql : has-weak-equalisers ℂ) 
                            → is-left-covering-prd F → is-left-covering-eql F
                              → preserves-jointly-monic/ F
  lcov-prd+eql→pres-jm/ wprdC weqlC lcprd lceql = pres-jm/
                                                      where open lc-prd-eql2pres-jm wprdC weqlC lcprd lceql


  



  module lc-trm-prd-preserves-trm (lctrm : is-left-covering-trm F) (lcprd : is-left-covering-prd F)
                                  where
    open is-left-covering-prd lcprd
    open is-left-covering-trm lctrm
    private
      module TE = 𝔼.is-terminal r𝔼.istrm

    module trmuniv-is-iso {TC : ℂ.Obj} (TCistrm : ℂ.is-terminal TC) where
      private
        module TC = ℂ.is-terminal TCistrm
        module FT×FT = 𝔼.product-of-not (r𝔼.prd-of (F.ₒ TC) (F.ₒ TC))

      covtrm : || 𝔼.Hom (F.ₒ TC) r𝔼.trmOb ||
      covtrm = TE.! (F.ₒ TC)
      covtrm-repi : 𝔼.is-regular-epi covtrm
      covtrm-repi = trmuniv-is-repi (ℂ.is-trm⇒is-wtrm TCistrm) r𝔼.istrm covtrm
      trm-prd : ℂ.product-of TC TC
      trm-prd = record
        { ×sp/ = ℂ.mkspan/ (ℂ.idar TC) (ℂ.idar TC)
        ; ×isprd = record
                 { <_,_> = λ f g → f
                 ; ×tr₁ = λ {A} {f} {g} → ℂ.lidax f
                 ; ×tr₂ = λ {A} {f} {g} → TC.!uqg
                 ; ×uq = λ pf1 pf2 → TC.!uqg
                 }
        }

      covprd : || 𝔼.Hom (F.ₒ TC) FT×FT.O12 ||
      covprd = FT×FT.< F.ₐ (ℂ.idar TC) , F.ₐ (ℂ.idar TC) >
      covprd-repi : 𝔼.is-regular-epi covprd
      covprd-repi = prduniv-is-repi (ℂ.prd-of⇒wprd-of trm-prd) FT×FT.×of FT×FT.×tr₁ FT×FT.×tr₂
                  where open ecategory-aux-only 𝔼
      covprd-mono : 𝔼.is-monic covprd
      covprd-mono = record
        { mono-pf = λ {_} {h} {h'} pf → 
                  ~proof h                       ~[ lidggˢ r (FT×FT.×tr₁ ⊙ F.id) ⊙ assˢ ] /
                         FT×FT.π₁ 𝔼.∘ covprd 𝔼.∘ h    ~[ ∘e pf r ] /
                         FT×FT.π₁ 𝔼.∘ covprd 𝔼.∘ h'   ~[ ass ⊙ lidgg r (FT×FT.×tr₁ ⊙ F.id) ]∎
                         h' ∎
        }
        where open ecategory-aux-only 𝔼
      covprd-iso : 𝔼.is-iso covprd
      covprd-iso = cov-pf (𝔼.ridax covprd) covprd-mono
                 where open epi&mono-props-all 𝔼
                       open 𝔼.is-cover (repi-is-cover covprd-repi)

      covtrm-kp : 𝔼.pullback-of covtrm covtrm
      covtrm-kp = 𝔼.mkpb-of (𝔼.×is-pb-on! r𝔼.istrm FT×FT.×isprd )
      private
        module kp = 𝔼.pullback-of covtrm-kp
      kp₁~kp₂ : kp.π/₁ 𝔼.~ kp.π/₂
      kp₁~kp₂ = ~proof
        kp.π/₁                             ~[ ridggˢ  r idcod ] /
        kp.π/₁ 𝔼.∘ covprd 𝔼.∘ covprd⁻¹    ~[ ass ⊙ ∘e r (FT×FT.×tr₁ ⊙ FT×FT.×tr₂ˢ {f = F.ₐ (ℂ.idar TC)}) ⊙ assˢ ] /
        kp.π/₂ 𝔼.∘ covprd 𝔼.∘ covprd⁻¹    ~[ ridgg r idcod ]∎
        kp.π/₂ ∎
              where open 𝔼.is-iso covprd-iso renaming (invf to covprd⁻¹)
                    open ecategory-aux-only 𝔼
      covtrm-mono : 𝔼.is-monic covtrm
      covtrm-mono = 𝔼.π/₁~π/₂→mono covtrm-kp kp₁~kp₂
      covtrm-iso : 𝔼.is-iso covtrm
      covtrm-iso = cov-pf (𝔼.ridax covtrm) covtrm-mono
                 where open 𝔼.is-cover (𝔼.repi-is-cover covtrm-repi)

      Ftrm-is-trm : 𝔼.is-terminal (F.ₒ TC)
      Ftrm-is-trm = 𝔼.iso!-is! (𝔼.mk≅ (𝔼.inv-iso-pair isisopair)) r𝔼.istrm
                  where open 𝔼.is-iso covtrm-iso
    -- end trmuniv-is-iso
    
    pres-trm : preserves-terminal F
    pres-trm = record
      { pres-!-pf = Ftrm-is-trm
      }
      where open trmuniv-is-iso
  -- end lc-trm-prd-preserves-trm



  lcov!×→pres-trm : is-left-covering-trm F → is-left-covering-prd F
                                         → preserves-terminal F
  lcov!×→pres-trm lc! lc× = pres-trm
                           where open lc-trm-prd-preserves-trm lc! lc×








  module lc-prd-eql-preserves-prd (Cwprd : has-bin-weak-products ℂ) (Cweql : has-weak-equalisers ℂ)
                                  (lcprd : is-left-covering-prd F) (lceql : is-left-covering-eql F)
                                  where
    open is-left-covering-prd lcprd

    module pres-prd {sp : ℂ.span} (is× : ℂ.is-product sp) where
      open ℂ.span sp
      private
        module Fsp = 𝔼.span (F.span sp)
        module ×sp = ℂ.bin-product-not (ℂ.mk× is×)
        module ×F = 𝔼.product-of-not (r𝔼.prd-of (F.ₒ O1) (F.ₒ O2))

      cov× : || 𝔼.Hom (F.ₒ O12) ×F.O12 ||
      cov× = ×F.< F.ₐ ×sp.π₁ , F.ₐ ×sp.π₂ >
      cov×-repi : 𝔼.is-regular-epi cov×
      cov×-repi = prduniv-is-repi (ℂ.prd-of⇒wprd-of (ℂ.mk×of is×)) ×F.×of ×F.×tr₁ ×F.×tr₂
      cov×-mono : 𝔼.is-monic cov×
      cov×-mono = 𝔼.jointly-monic-tr ×F.×tr₁ ×F.×tr₂ (pres-jm/-pf (ℂ.πs-are-jointly-monic/ (ℂ.mk× is×)))
                where open preserves-jointly-monic/ (lcov-prd+eql→pres-jm/ Cwprd Cweql lcprd lceql)
      cov×-iso : 𝔼.is-iso cov×
      cov×-iso = 𝔼.monic-cover-is-iso cov×-mono (𝔼.repi-is-cover cov×-repi)

      Fsp-is× : 𝔼.is-product (F.span sp)
      Fsp-is× = record
              { <_,_> = λ f g → cov×⁻¹ 𝔼.∘ ×F.< f , g >
              ; ×tr₁ = λ {A} {f} {g} → ∘e r (×F.×tr₁ˢ {g = F.ₐ ×sp.π₂}) ⊙ assˢ ⊙ ∘e (ass ⊙ lidgg r idcod) r ⊙ ×F.×tr₁
              ; ×tr₂ = λ {A} {f} {g} → ∘e r (×F.×tr₂ˢ {g = F.ₐ ×sp.π₂}) ⊙ assˢ ⊙ ∘e (ass ⊙ lidgg r idcod) r ⊙ ×F.×tr₂
              ; ×uq = λ pf₁ pf₂ → mono-pf (×F.×uq (ass ⊙ ∘e r ×F.×tr₁ ⊙ pf₁ ⊙ ∘e r (×F.×tr₁ˢ {g = F.ₐ ×sp.π₂}) ⊙ assˢ)
                                                   (ass ⊙ ∘e r ×F.×tr₂ ⊙ pf₂ ⊙ ∘e r (×F.×tr₂ˢ {f = F.ₐ ×sp.π₁}) ⊙ assˢ))
              }
              where open 𝔼.is-iso cov×-iso renaming (invf to cov×⁻¹)
                    open ecategory-aux-only 𝔼
                    open 𝔼.is-monic cov×-mono
    -- end pres-prd

    pres-prd : preserves-bin-products F
    pres-prd = record
             { pres-×-pf = pres-prd.Fsp-is×
             }
  -- end lc-prd-eql-preserves-prd



  lcov-×+eql→pres-× : (Cwprd : has-bin-weak-products ℂ) (Cweql : has-weak-equalisers ℂ) 
                         → is-left-covering-prd F → is-left-covering-eql F
                           → preserves-bin-products F
  lcov-×+eql→pres-× wprdC weqlC lc× lceql = pres-prd
                                                where open lc-prd-eql-preserves-prd wprdC weqlC lc× lceql







  module lc-eql-pb-preserves-pb (Cweql : has-weak-equalisers ℂ) (Cwpb : has-weak-pullbacks ℂ)
                                 (lceql : is-left-covering-eql F) (lcpb : is-left-covering-pb F)
                                where
    open is-left-covering-pb lcpb

    module pres-pb {sq : ℂ.comm-square} (is×/ : ℂ.is-pb-square sq) where
      open ℂ.comm-square sq
      private
        module Fsq = 𝔼.comm-square (F.sq sq)
        module ×/sq = ℂ.pullback-sq-not (ℂ.mkpb-sq is×/)
        module ×/F = 𝔼.pullback-of-not (r𝔼.pb-of (F.ₐ down) (F.ₐ right))

      covpb-pf = F.∘∘ ×/sq.×/sqpf
      covpb : || 𝔼.Hom (F.ₒ ×/sq.ul) ×/F.ul ||
      covpb = ×/F.⟨ F.ₐ ×/sq.π/₁ , F.ₐ ×/sq.π/₂ ⟩[ covpb-pf ]
      covpb-repi : 𝔼.is-regular-epi covpb
      covpb-repi = pbuniv-is-repi (ℂ.pbof⇒wpbof (ℂ.mkpb-of is×/)) ×/F.×/of (×/F.×/tr₁ covpb-pf) (×/F.×/tr₂ covpb-pf)
      covpb-mono : 𝔼.is-monic covpb
      covpb-mono = 𝔼.jointly-monic-tr (×/F.×/tr₁ covpb-pf) (×/F.×/tr₂ covpb-pf)
                                       (pres-jm/-pf (ℂ.π/s-are-jointly-monic/ (ℂ.mkpb-sq is×/)))
                 where open preserves-jointly-monic/ (lcov-eql+pb→pres-jm/ Cweql Cwpb lceql lcpb)
      covpb-iso : 𝔼.is-iso covpb
      covpb-iso = 𝔼.monic-cover-is-iso covpb-mono (𝔼.repi-is-cover covpb-repi)

      Fsq-is×/ : 𝔼.is-pb-square (F.sq sq)
      Fsq-is×/ = 𝔼.sp≅pb-is-pb ×/F.×/of covpb-iso (×/F.×/tr₁ covpb-pf) (×/F.×/tr₂ covpb-pf)
    -- end pres-pb

    pres-pb : preserves-pullbacks F
    pres-pb = record
            { pres-pbsq-pf = pres-pb.Fsq-is×/
            }
  -- end lc-eql-pb-preserves-pb




  lcov-eql+pb→pres-pb : (Cweql : has-weak-equalisers ℂ) (Cwpb : has-weak-pullbacks ℂ) 
                           → is-left-covering-eql F → is-left-covering-pb F
                             → preserves-pullbacks F
  lcov-eql+pb→pres-pb weqlC wpbC lceql lcpb = pres-pb
                                            where open lc-eql-pb-preserves-pb weqlC wpbC lceql lcpb

-- end left-cov-relations-into-regular-cat





-- All the properties proved in the module above


×→[lcov-×+eql→lcov-×/] : {ℂ 𝔼 : ecategory} {F : efunctor ℂ 𝔼}  (regE : is-regular 𝔼)
                           (prdC : has-bin-products ℂ)
                               → is-left-covering-prd F → is-left-covering-eql F
                                 → is-left-covering-pb F
×→[lcov-×+eql→lcov-×/] {F = F} regE = lp.×→[lcov-×+eql→lcov-×/]
                                      where module lp = left-cov-relations-into-regular-cat F regE




lcov-×+eql→lcov-×/ : {ℂ 𝔼 : ecategory} {F : efunctor ℂ 𝔼} (regE : is-regular 𝔼)
                      (wprdC : has-bin-weak-products ℂ) (weqlC : has-weak-equalisers ℂ)
                        → is-left-covering-prd F → is-left-covering-eql F
                          → is-left-covering-pb F
lcov-×+eql→lcov-×/ {F = F} regE = lp.lcov-×+eql→lcov-×/
                                 where module lp = left-cov-relations-into-regular-cat F regE



lcov-eql+pb→lcov-bw : {ℂ 𝔼 : ecategory} {F : efunctor ℂ 𝔼} (regE : is-regular 𝔼)
                       (Cweql : has-weak-equalisers ℂ) (Cwpb : has-weak-pullbacks ℂ)
                         → is-left-covering-eql F → is-left-covering-pb F
                           →  is-left-covering-bw F
lcov-eql+pb→lcov-bw {F = F} regE = lp.lcov-eql+pb→lcov-bw
                                  where module lp = left-cov-relations-into-regular-cat F regE



lcov-bw→pres-jm/ : {ℂ 𝔼 : ecategory} {F : efunctor ℂ 𝔼} (regE : is-regular 𝔼)
                    (Cwbw : has-weak-bows ℂ)
                         → is-left-covering-bw F → preserves-jointly-monic/ F
lcov-bw→pres-jm/ {F = F} regE = lp.lcov-bw→pres-jm/
                               where module lp = left-cov-relations-into-regular-cat F regE


lcov-eql+pb→pres-jm/ : {ℂ 𝔼 : ecategory} {F : efunctor ℂ 𝔼} (regE : is-regular 𝔼)
                        (Cweql : has-weak-equalisers ℂ) (Cwpb : has-weak-pullbacks ℂ)
                          → is-left-covering-eql F → is-left-covering-pb F
                            → preserves-jointly-monic/ F
lcov-eql+pb→pres-jm/ {F = F} regE = lp.lcov-eql+pb→pres-jm/
                                   where module lp = left-cov-relations-into-regular-cat F regE


lcov-prd+eql→pres-jm/ : {ℂ 𝔼 : ecategory} {F : efunctor ℂ 𝔼} (regE : is-regular 𝔼)
                         (Cwprd : has-bin-weak-products ℂ) (Cweql : has-weak-equalisers ℂ)
                          → is-left-covering-prd F → is-left-covering-eql F
                            → preserves-jointly-monic/ F
lcov-prd+eql→pres-jm/ {F = F} regE = lp.lcov-prd+eql→pres-jm/
                                    where module lp = left-cov-relations-into-regular-cat F regE


lcov!×→pres-trm : {ℂ 𝔼 : ecategory} {F : efunctor ℂ 𝔼} (regE : is-regular 𝔼)
                            → is-left-covering-trm F → is-left-covering-prd F
                              → preserves-terminal F
lcov!×→pres-trm {F = F} regE = lp.lcov!×→pres-trm
                              where module lp = left-cov-relations-into-regular-cat F regE



lcov-×+eql→pres-× : {ℂ 𝔼 : ecategory} {F : efunctor ℂ 𝔼} (regE : is-regular 𝔼)
                     (Cwprd : has-bin-weak-products ℂ) (Cweql : has-weak-equalisers ℂ)
                       → is-left-covering-prd F → is-left-covering-eql F
                         → preserves-bin-products F
lcov-×+eql→pres-× {F = F} regE = lp.lcov-×+eql→pres-×
                                where module lp = left-cov-relations-into-regular-cat F regE




lcov-eql+pb→pres-pb : {ℂ 𝔼 : ecategory} {F : efunctor ℂ 𝔼} (regE : is-regular 𝔼)
                       (Cweql : has-weak-equalisers ℂ) (Cwpb : has-weak-pullbacks ℂ)
                         → is-left-covering-eql F → is-left-covering-pb F
                           → preserves-pullbacks F
lcov-eql+pb→pres-pb {F = F} regE = lp.lcov-eql+pb→pres-pb
                                  where module lp = left-cov-relations-into-regular-cat F regE


lcov→pres-flim : {ℂ 𝔼 : ecategory} {F : efunctor ℂ 𝔼}
                  (regE : is-regular 𝔼) (fwlC : has-fin-weak-limits ℂ)
                    → is-left-covering F → preserves-fin-limits F
lcov→pres-flim {F = F} regE fwlC lcovF = record
  { prestrm = lcov!×→pres-trm regE lc! lc×
  ; presprd = lcov-×+eql→pres-× regE haswprd hasweql lc× lceql
  ; prespb = lcov-eql+pb→pres-pb regE hasweql haswpb lceql lc×/
  }
  where open has-fin-weak-limits fwlC
        open is-left-covering lcovF
