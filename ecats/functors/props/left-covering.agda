
-- disable the K axiom:

{-# OPTIONS --without-K #-}

-- Agda version 2.5.4.1

module ecats.functors.props.left-covering where

open import ecats.basic-defs.ecat-def&not
open import ecats.basic-defs.all-arrows
open import ecats.basic-defs.eqv-rel
open import ecats.basic-defs.regular-ecat
open import ecats.basic-defs.exact-ecat
open import ecats.basic-props.all
open import ecats.finite-limits.all
open import ecats.functors.defs.efunctor-d&n
open import ecats.functors.defs.natural-transformation
open import ecats.functors.defs.basic-defs
open import ecats.functors.defs.preserving-functor
open import ecats.functors.defs.left-covering



-- when the target category is regular

module left-covering-into-regular-props (ℂ 𝔼 : ecategory) (regE : is-regular 𝔼) where
  private
    module ℂ where
      open ecategory ℂ public
      open comm-shapes ℂ public
      open epis&monos-defs ℂ public
      open epis&monos-props ℂ public
      open finite-limits-d&p ℂ public
      open finite-weak-limits-d&p ℂ public
      open limits→weak-limits ℂ public
      --open relations-among-limit-diagrams ℂ public
    module 𝔼 where
      open ecategory 𝔼 public
      open comm-shapes 𝔼 public
      open iso-defs 𝔼 public
      open epis&monos-defs 𝔼 public
      open epis&monos-props 𝔼 public
      open finite-limits-d&p 𝔼 public
      open finite-weak-limits-d&p 𝔼 public
      open limits→weak-limits 𝔼 public
      open relations-among-limit-diagrams 𝔼 public
    module reg𝔼 where
      open is-regular regE public
      open pullbacks-aux haspb public
      open regular-cat-props regE public



  -- Proofs that a left covering in some limits is left covering in some other.


  -- This module proves lc-×+eql→lc-pb when ℂ has binary products.
  -- Next module proves it when ℂ has weak products and weak equalisers.
  
  module w/prd-lc-prd-eql2lc-pb (prdC : has-bin-products ℂ)
                                {F : efunctor ℂ 𝔼} (lcprd : is-left-covering-prd F) (lceql : is-left-covering-eql F)
                                where
    private
      module F = efunctor-aux F
    open is-left-covering-prd lcprd
    open is-left-covering-eql lceql
    private
      module ×ℂ = bin-products-aux prdC
      module ×𝔼 = bin-products-aux reg𝔼.hasprd
      module eql𝔼 = has-equalisers reg𝔼.haseql
      module wpbof = ℂ.wpullback-of
      module wpbsq = ℂ.wpullback-sq
      module pbof = 𝔼.pullback-of
      module pbsq = 𝔼.pb-square
      module weqlof = ℂ.wequaliser-of
      module eqlof = 𝔼.equaliser-of

    module pbuniv-is-repi {X Y Z : ℂ.Obj} {f : || ℂ.Hom X Z ||} {g : || ℂ.Hom Y Z ||}
                          (wpbC : ℂ.wpullback-of f g) (pbof : 𝔼.pullback-of (F.ₐ f) (F.ₐ g))
                          {covpb : || 𝔼.Hom (F.ₒ (wpbof.ul wpbC)) (pbof.ul pbof) ||}
                          (tr₁ : pbof.π/₁ pbof 𝔼.∘ covpb 𝔼.~ F.ₐ (wpbof.wπ/₁ wpbC))
                          (tr₂ : pbof.π/₂ pbof 𝔼.∘ covpb 𝔼.~ F.ₐ (wpbof.wπ/₂ wpbC))
                          where

      open ℂ.wpullback-of-not wpbC renaming (ul to wul)
      open 𝔼.pullback-of-not pbof
      
      
      weql : ℂ.wequaliser-of (f ℂ.∘ ×ℂ.π₁) (g ℂ.∘ ×ℂ.π₂)
      weql = ℂ.wpbof2weqlof (×ℂ.×of {A = X} {B = Y}) wpbC

      eqlF : 𝔼.equaliser-of (F.ₐ (f ℂ.∘ ×ℂ.π₁)) (F.ₐ (g ℂ.∘ ×ℂ.π₂))
      eqlF = eql𝔼.eql-of (F.ₐ (f ℂ.∘ ×ℂ.π₁)) (F.ₐ (g ℂ.∘ ×ℂ.π₂))

      coveqlF-pf = F.∘∘ (~proof (f ℂ.∘ ×ℂ.π₁) ℂ.∘ ×ℂ.< wπ/₁ , wπ/₂ >   ~[ assˢ ⊙ ∘e ×ℂ.×tr₁ r ] /
                               f ℂ.∘ wπ/₁                             ~[ w×/sqpf ] /
                               g ℂ.∘ wπ/₂                             ~[ ∘e (×ℂ.×tr₂ˢ {f = wπ/₁}) r ⊙ ass ]∎
                               (g ℂ.∘ ×ℂ.π₂) ℂ.∘ ×ℂ.< wπ/₁ , wπ/₂ > ∎)
                 where open ecategory-aux-only ℂ

      coveqlF : || 𝔼.Hom (F.ₒ wul) (eqlof.Eql eqlF) ||
      coveqlF = F.ₐ (×ℂ.< wπ/₁ , wπ/₂ >) |eql[ coveqlF-pf ]
              where open 𝔼.equaliser-of eqlF

      coveqlF-repi : 𝔼.is-regular-epi coveqlF
      coveqlF-repi = eqluniv-is-repi weql eqlF (eqltr coveqlF-pf)
                   where open 𝔼.equaliser-of eqlF


      eqlD : 𝔼.equaliser-of (F.ₐ f 𝔼.∘ ×𝔼.π₁) (F.ₐ g 𝔼.∘ ×𝔼.π₂)
      eqlD = 𝔼.pbof→eqlof ×𝔼.×of pbof

      covprd : || 𝔼.Hom (F.ₒ (X ×ℂ.× Y)) (F.ₒ X ×𝔼.× F.ₒ Y) ||
      covprd = ×𝔼.< F.ₐ ×ℂ.π₁ , F.ₐ ×ℂ.π₂ >

      covprd-repi : 𝔼.is-regular-epi covprd
      covprd-repi = prduniv-is-repi (ℂ.prd-of⇒wprd-of ×ℂ.×of) ×𝔼.×of ×𝔼.×tr₁ ×𝔼.×tr₂


      coveqlD-pf : (F.ₐ f 𝔼.∘ ×𝔼.π₁) 𝔼.∘ covprd 𝔼.∘ eqlof.eqlar eqlF
                        𝔼.~ (F.ₐ g 𝔼.∘ ×𝔼.π₂) 𝔼.∘ covprd 𝔼.∘ eqlof.eqlar eqlF
      coveqlD-pf = epi-pf (~proof ((F.ₐ f 𝔼.∘ ×𝔼.π₁) 𝔼.∘ covprd 𝔼.∘ eqlof.eqlar eqlF) 𝔼.∘ coveqlF  ~[ ∘e r ass ⊙ assˢ ⊙ ∘e (eqlF.eqltr coveqlF-pf) (assˢ ⊙ ∘e ×𝔼.×tr₁ r) ] /
                                  (F.ₐ f 𝔼.∘ F.ₐ ×ℂ.π₁) 𝔼.∘ F.ₐ (×ℂ.< wπ/₁ , wπ/₂ >)              ~[ ∘e r F.∘ax-rf ⊙ coveqlF-pf ⊙ ∘e r F.∘ax-rfˢ ] /
                                  (F.ₐ g 𝔼.∘ F.ₐ ×ℂ.π₂) 𝔼.∘ F.ₐ (×ℂ.< wπ/₁ , wπ/₂ >)          ~[ ∘e (eqlF.eqltr coveqlF-pf ˢ) (∘e (×𝔼.×tr₂ˢ {f = F.ₐ ×ℂ.π₁}) r ⊙ ass)
                                                                                             ⊙ ass ⊙ ∘e r assˢ ]∎
                                  ((F.ₐ g 𝔼.∘ ×𝔼.π₂) 𝔼.∘ covprd 𝔼.∘ eqlof.eqlar eqlF) 𝔼.∘ coveqlF ∎)
                 where open 𝔼.is-epic (𝔼.repi-is-epic coveqlF-repi)
                       open ecategory-aux-only 𝔼
                       module eqlF = 𝔼.equaliser-of eqlF

      coveqlD : || 𝔼.Hom (eqlof.Eql eqlF) (eqlof.Eql eqlD) ||
      coveqlD = (covprd 𝔼.∘ eqlof.eqlar eqlF) |eql[ coveqlD-pf ]
              where open 𝔼.equaliser-of eqlD

      coveqlD-pb : 𝔼.pb-square
      coveqlD-pb = record
        { ×/sq = 𝔼.mksq (𝔼.mksq/ (eqlD.eqltr coveqlD-pf))
        ; ×/ispbsq = record
                   { ⟨_,_⟩[_] = λ h k pf → eqlF._|eql[_] k (⟨⟩pf pf)
                   ; ×/tr₁ = λ pf → eqlD.eqluq (ass ⊙ ∘e r (eqlD.eqltr coveqlD-pf) ⊙ assˢ ⊙ ∘e (eqlF.eqltr (⟨⟩pf pf)) r ⊙ pf ˢ)
                   ; ×/tr₂ = λ pf → eqlF.eqltr (⟨⟩pf pf)
                   ; ×/uq = λ pf1 pf2 → eqlF.eqluq pf2
                   }
        }
        where module eqlD = 𝔼.equaliser-of eqlD
              module eqlF = 𝔼.equaliser-of eqlF
              open ecategory-aux-only 𝔼
              ⟨⟩pf : {C : 𝔼.Obj} {h : || 𝔼.Hom C eqlD.Eql ||} {k : || 𝔼.Hom C (F.ₒ (X ×ℂ.× Y)) ||} (pf : eqlD.eqlar 𝔼.∘ h 𝔼.~ covprd 𝔼.∘ k)
                       → F.ₐ (f ℂ.∘ ×ℂ.π₁) 𝔼.∘ k 𝔼.~ F.ₐ (g ℂ.∘ ×ℂ.π₂) 𝔼.∘ k
              ⟨⟩pf {C} {h} {k} pf = ~proof
                   F.ₐ (f ℂ.∘ ×ℂ.π₁) 𝔼.∘ k                  ~[ ∘e r (F.∘ax-rfˢ ⊙ ∘e (×𝔼.×tr₁ˢ {g = F.ₐ ×ℂ.π₂}) r) ⊙ assˢ ⊙ ∘e assˢ r ] /
                   F.ₐ f 𝔼.∘ ×𝔼.π₁ 𝔼.∘ covprd 𝔼.∘ k          ~[ ass ⊙ ∘e (pf ˢ) r ] /
                   (F.ₐ f 𝔼.∘ ×𝔼.π₁) 𝔼.∘ eqlD.eqlar 𝔼.∘ h    ~[ ass ⊙ ∘e r eqlD.eqleq ⊙ assˢ ] /
                   (F.ₐ g 𝔼.∘ ×𝔼.π₂) 𝔼.∘ eqlD.eqlar 𝔼.∘ h    ~[ ∘e pf r ⊙ assˢ ] /
                   F.ₐ g 𝔼.∘ ×𝔼.π₂ 𝔼.∘ covprd 𝔼.∘ k          ~[ ∘e (ass ⊙ ∘e r ×𝔼.×tr₂) r ⊙ ass ⊙ ∘e r F.∘ax-rf ]∎
                   F.ₐ (g ℂ.∘ ×ℂ.π₂) 𝔼.∘ k ∎

      coveqlD-repi : 𝔼.is-regular-epi coveqlD
      coveqlD-repi = pres-rl coveqlD-pb covprd-repi
                   where module eqlD = 𝔼.equaliser-of eqlD
                         open 𝔼.is-pbsq-stable reg𝔼.repi-pbsq-stb


      covtr : coveqlD 𝔼.∘ coveqlF 𝔼.~ covpb
      covtr = eqlD.eqluq (~proof eqlD.eqlar 𝔼.∘ coveqlD 𝔼.∘ coveqlF      ~[ ass ⊙ ∘e r (eqlD.eqltr coveqlD-pf) ⊙ assˢ ] /
                                 covprd 𝔼.∘ eqlof.eqlar eqlF 𝔼.∘ coveqlF   ~[ ∘e (eqlF.eqltr coveqlF-pf) r ] /
                                 covprd 𝔼.∘ F.ₐ (×ℂ.< wπ/₁ , wπ/₂ >)    ~[ ×𝔼.<>ar~<>ar (F.∘ax ×ℂ.×tr₁ ⊙ tr₁ ˢ) (F.∘ax ×ℂ.×tr₂ ⊙ tr₂ ˢ) ]∎
                                 eqlD.eqlar 𝔼.∘ covpb ∎ )
            where module eqlD = 𝔼.equaliser-of eqlD
                  module eqlF = 𝔼.equaliser-of eqlF
                  open ecategory-aux-only 𝔼


      covpb-repi : 𝔼.is-regular-epi covpb
      covpb-repi =  ∘ce covtr coveqlD-repi coveqlF-repi --reg𝔼.repi-cmp
                 where open is-ecat-congr reg𝔼.regular-epi-is-congr
      
    -- end pbuniv-is-repi
    
    lcpb : is-left-covering-pb F
    lcpb = record
      { pbuniv-is-repi = covpb-repi
      }
      where open pbuniv-is-repi

  -- end w/prd-lc-prd-eql2lc-pb




  ×→[lcov-×+eql→lcov-×/] : (prdC : has-bin-products ℂ) {F : efunctor ℂ 𝔼}
                                 → is-left-covering-prd F → is-left-covering-eql F
                                   → is-left-covering-pb F
  ×→[lcov-×+eql→lcov-×/] prdC lc× lceql = lcpb
                                          where open w/prd-lc-prd-eql2lc-pb prdC lc× lceql









  module lc-prd-eql2lc-pb (C-has-wprd : has-bin-weak-products ℂ) (C-has-weql : has-weak-equalisers ℂ)
                          {F : efunctor ℂ 𝔼} (lcprd : is-left-covering-prd F) (lceql : is-left-covering-eql F)
                          where
    private
      module F = efunctor-aux F
    open is-left-covering-prd lcprd
    open is-left-covering-eql lceql
    private
      module w×ℂ = bin-wproducts-aux C-has-wprd
      module weqlℂ = has-weak-equalisers C-has-weql
      module ×𝔼 = bin-products-aux reg𝔼.hasprd
      module eql𝔼 = has-equalisers reg𝔼.haseql
      module wpbof = ℂ.wpullback-of
      module wpbsq = ℂ.wpullback-sq
      module pbof = 𝔼.pullback-of
      module pbsq = 𝔼.pb-square
      module weqlof = ℂ.wequaliser-of
      module eqlof = 𝔼.equaliser-of
      

    module pbuniv-is-repi {X Y Z : ℂ.Obj} {f : || ℂ.Hom X Z ||} {g : || ℂ.Hom Y Z ||}
                          (wpbof : ℂ.wpullback-of f g) (pbof : 𝔼.pullback-of (F.ₐ f) (F.ₐ g))
                          {covpb : || 𝔼.Hom (F.ₒ (wpbof.ul wpbof)) (pbof.ul pbof) ||}
                          (tr₁ : pbof.π/₁ pbof 𝔼.∘ covpb 𝔼.~ F.ₐ (wpbof.wπ/₁ wpbof))
                          (tr₂ : pbof.π/₂ pbof 𝔼.∘ covpb 𝔼.~ F.ₐ (wpbof.wπ/₂ wpbof))
                          where

      Xw×Y : ℂ.wproduct-of X Y
      Xw×Y = w×ℂ.wprd-of X Y
      FX×FY : 𝔼.product-of (F.ₒ X) (F.ₒ Y)
      FX×FY = ×𝔼.prd-of (F.ₒ X) (F.ₒ Y)

      private
        module Xw×Y = ℂ.wproduct-of-not Xw×Y
        module FX×FY = 𝔼.product-of-not FX×FY
        module fw×g = ℂ.wpullback-of-not wpbof
        module eql = 𝔼.equaliser-of (𝔼.pbof→eqlof FX×FY pbof) -- this is Ff×Fg turned into an equaliser
      
      fwπ gwπ : || ℂ.Hom Xw×Y.O12 Z ||
      fwπ = f ℂ.∘ Xw×Y.wπ₁
      gwπ = g ℂ.∘ Xw×Y.wπ₂

      Ffπ Fgπ : || 𝔼.Hom FX×FY.O12 (F.ₒ Z) ||
      Ffπ = F.ₐ f 𝔼.∘ FX×FY.π₁
      Fgπ = F.ₐ g 𝔼.∘ FX×FY.π₂

      weql : ℂ.wequaliser-of fwπ gwπ
      weql = (weqlℂ.weql-of fwπ gwπ)
      eqlF : 𝔼.equaliser-of(F.ₐ fwπ) (F.ₐ gwπ)
      eqlF = eql𝔼.eql-of (F.ₐ fwπ) (F.ₐ gwπ)
      
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

      covEql-pb : 𝔼.is-pb-square covEql-sq
      covEql-pb = record
        { ⟨_,_⟩[_] = λ h k pf → un {_} {h} {k} pf
        ; ×/tr₁ = λ {_} {h} {k} pf → eql.eqluq (~proof
                eql.eqlar 𝔼.∘ covEql 𝔼.∘ un pf            ~[ ass ⊙ ∘e r (eql.eqltr covEql-pf) ⊙ assˢ ] /
                covprd 𝔼.∘ eqlF.eqlar 𝔼.∘ un pf           ~[ ∘e (eqlF.eqltr (un-pf pf)) r ] /
                covprd 𝔼.∘ k                             ~[ pf ˢ ]∎
                eql.eqlar 𝔼.∘ h ∎)
        ; ×/tr₂ = λ pf → eqlF.eqltr (un-pf pf)
        ; ×/uq = λ _ pf₂ → eqlF.eqluq pf₂
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
      covEql-repi = pres-rl (𝔼.mkpb-sq covEql-pb) covprd-repi
                  where open 𝔼.is-pbsq-stable reg𝔼.repi-pbsq-stb

      covcovE-repi : 𝔼.is-regular-epi (covEql 𝔼.∘ coveqlF)
      covcovE-repi = ∘c covEql-repi coveqlF-repi
                   where open is-ecat-congr reg𝔼.regular-epi-is-congr


      covpb-pf : covpb 𝔼.∘ F.ₐ med-ar 𝔼.~ covEql 𝔼.∘ coveqlF
      covpb-pf = eql.eqluq (~proof
        eql.eqlar 𝔼.∘ covpb 𝔼.∘ F.ₐ med-ar                        ~[ ass ⊙ ∘e r (FX×FY.<>ar~<> tr₁ tr₂) ] /
        FX×FY.< F.ₐ fw×g.wπ/₁ , F.ₐ fw×g.wπ/₂ > 𝔼.∘  F.ₐ med-ar    ~[ FX×FY.<>ar~<>ar (F.∘∘ (fw×g.w×/tr₁ med-ar-pf)) (F.∘∘ (fw×g.w×/tr₂ med-ar-pf)) ] /
        covprd 𝔼.∘ F.ₐ weql.weqlar                               ~[ ∘e (eqlF.eqltr (F.∘∘ weql.weqleq) ˢ) r ] /
        covprd 𝔼.∘ eqlF.eqlar 𝔼.∘ coveqlF                        ~[ ass ⊙ ∘e r (eql.eqltr covEql-pf ˢ) ⊙ assˢ ]∎
        eql.eqlar 𝔼.∘ covEql 𝔼.∘ coveqlF ∎)
                where open ecategory-aux-only 𝔼


      covpb-repi : 𝔼.is-regular-epi covpb
      covpb-repi = reg𝔼.cover-is-regular (𝔼.cover-triang (𝔼.mktriang covpb-pf) (𝔼.repi-is-cover covcovE-repi))
      
    -- end pbuniv-is-repi

    
    lc-pb : is-left-covering-pb F
    lc-pb = record
      { pbuniv-is-repi = covpb-repi
      }
      where open pbuniv-is-repi


  -- end lc-prd-eql2lc-pb




  lcov-×+eql→lcov-×/ : (wprdC : has-bin-weak-products ℂ) (weqlC : has-weak-equalisers ℂ) {F : efunctor ℂ 𝔼}
                          → is-left-covering-prd F → is-left-covering-eql F
                            → is-left-covering-pb F
  lcov-×+eql→lcov-×/ wprdC weqlC lc× lceql = lc-pb
                                              where open lc-prd-eql2lc-pb wprdC weqlC lc× lceql










  module lc-eql-pb2lc-bw (Cweql : has-weak-equalisers ℂ) (Cwpb : has-weak-pullbacks ℂ)
                         {F : efunctor ℂ 𝔼} (lceql : is-left-covering-eql F) (lcpb : is-left-covering-pb F) where
    private
      module F = efunctor-aux F
    open is-left-covering-pb lcpb
    open is-left-covering-eql lceql
    private
      module eql𝔼 = has-equalisers reg𝔼.haseql
      module weqlℂ = has-weak-equalisers Cweql
      module wbwof = ℂ.wbow-of
      module bwof = 𝔼.bow-of


    module bwuniv-is-repi {DL DR : ℂ.Obj} {sp₁ sp₂ : ℂ.span/ DL DR} (wbw : ℂ.wbow-of sp₁ sp₂)
                          (bw : 𝔼.bow-of (F.span/ sp₁) (F.span/ sp₂))
                          {covbw : || 𝔼.Hom (F.ₒ (wbwof.wBow wbw)) (bwof.Bow bw) ||}
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
        module pbFa1 = 𝔼.pullback-of-not (reg𝔼.pb-of Fsp₁.a1 Fsp₂.a1)
        module eqlFa2 = 𝔼.equaliser-of (eql𝔼.eql-of (F.ₐ (sp₁.a2 ℂ.∘ wpba1.wπ/₁)) (F.ₐ (sp₂.a2 ℂ.∘ wpba1.wπ/₂)))

      med-wbw-pf₁ : sp₁.a1 ℂ.∘ wpba1.wπ/₁ ℂ.∘ weqla2.weqlar ℂ.~ sp₂.a1 ℂ.∘ wpba1.wπ/₂ ℂ.∘ weqla2.weqlar
      med-wbw-pf₁ = ass ⊙ ∘e r wpba1.w×/sqpf ⊙ assˢ
                  where open ecategory-aux-only ℂ
      med-wbw-pf₂ : sp₁.a2 ℂ.∘ wpba1.wπ/₁ ℂ.∘ weqla2.weqlar ℂ.~ sp₂.a2 ℂ.∘ wpba1.wπ/₂ ℂ.∘ weqla2.weqlar
      med-wbw-pf₂ = ass ⊙ weqla2.weqleq ⊙ assˢ
                  where open ecategory-aux-only ℂ
      
      med-wbw : || ℂ.Hom weqla2.wEql wbw.wBow ||
      med-wbw = wbw.⟨ wpba1.wπ/₁ ℂ.∘ weqla2.weqlar , wpba1.wπ/₂ ℂ.∘ weqla2.weqlar ⟩[ med-wbw-pf₁ , med-wbw-pf₂ ]

      med-bw : || 𝔼.Hom bw.Bow pbFa1.ul ||
      med-bw = pbFa1.⟨ bw.π//₁ , bw.π//₂ ⟩[ bw.sqpf₁ ]

      covEql : || 𝔼.Hom (F.ₒ weqla2.wEql) eqlFa2.Eql ||
      covEql = F.ₐ weqla2.weqlar eqlFa2.|eql[ F.∘∘ weqla2.weqleq ]

      covEql-repi : 𝔼.is-regular-epi covEql
      covEql-repi = eqluniv-is-repi (wbw-aux.weql-a2 sp₁ sp₂)
                                    (eql𝔼.eql-of (F.ₐ (sp₁.a2 ℂ.∘ wpba1.wπ/₁)) (F.ₐ (sp₂.a2 ℂ.∘ wpba1.wπ/₂)))
                                    (eqlFa2.eqltr (F.∘∘ weqla2.weqleq))


      covPb : || 𝔼.Hom (F.ₒ wpba1.ul) pbFa1.ul ||
      covPb = pbFa1.⟨ F.ₐ wpba1.wπ/₁ , F.ₐ wpba1.wπ/₂ ⟩[ F.∘∘ wpba1.w×/sqpf ]

      covPb-repi : 𝔼.is-regular-epi covPb
      covPb-repi = pbuniv-is-repi (wbw-aux.wpb-a1 sp₁ sp₂)
                                  (reg𝔼.pb-of Fsp₁.a1 Fsp₂.a1)
                                  (pbFa1.×/tr₁ (F.∘∘ wpba1.w×/sqpf))
                                  (pbFa1.×/tr₂ (F.∘∘ wpba1.w×/sqpf))

      covBw-pf₁ : F.ₐ sp₁.a1 𝔼.∘ F.ₐ wpba1.wπ/₁ 𝔼.∘ eqlFa2.eqlar 𝔼.~ F.ₐ sp₂.a1 𝔼.∘ F.ₐ wpba1.wπ/₂ 𝔼.∘ eqlFa2.eqlar
      covBw-pf₁ = ass ⊙ ∘e r (F.∘∘ wpba1.w×/sqpf) ⊙ assˢ
                where open ecategory-aux-only 𝔼
      covBw-pf₂ : F.ₐ sp₁.a2 𝔼.∘ F.ₐ wpba1.wπ/₁ 𝔼.∘ eqlFa2.eqlar 𝔼.~ F.ₐ sp₂.a2 𝔼.∘ F.ₐ wpba1.wπ/₂ 𝔼.∘ eqlFa2.eqlar
      covBw-pf₂ = ass ⊙ ∘e r F.∘ax-rf ⊙ eqlFa2.eqleq ⊙ ∘e r F.∘ax-rfˢ ⊙ assˢ 
                where open ecategory-aux-only 𝔼
      covBw : || 𝔼.Hom eqlFa2.Eql bw.Bow ||
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
              un-pf : {C : 𝔼.Obj} {h : || 𝔼.Hom C bw.Bow ||} {k : || 𝔼.Hom C (F.ₒ wpba1.ul) ||} (pf : med-bw 𝔼.∘ h 𝔼.~ covPb 𝔼.∘ k)
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

              tr₁-pf : {C : 𝔼.Obj} {h : || 𝔼.Hom C bw.Bow ||} {k : || 𝔼.Hom C (F.ₒ wpba1.ul) ||} (pf : med-bw 𝔼.∘ h 𝔼.~ covPb 𝔼.∘ k)
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
                 where open 𝔼.is-pbsq-stable reg𝔼.repi-pbsq-stb

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
      covbw-repi = reg𝔼.cover-is-regular (𝔼.cover-triang (𝔼.mktriang cov-eq) (𝔼.repi-is-cover (∘c covBw-repi covEql-repi)))
                 where open is-ecat-congr reg𝔼.regular-epi-is-congr
      
    -- end bwuniv-is-repi


    is-lcbw : is-left-covering-bw F
    is-lcbw = record
      { bwuniv-is-repi = covbw-repi
      }
      where open bwuniv-is-repi

  -- end lc-eql-pb2lc-bw



  lcov-eql+pb→lcov-bw : (Cweql : has-weak-equalisers ℂ) (Cwpb : has-weak-pullbacks ℂ) {F : efunctor ℂ 𝔼}
                           → is-left-covering-eql F → is-left-covering-pb F
                             →  is-left-covering-bw F
  lcov-eql+pb→lcov-bw weqlC wpbC lceql lcpb = is-lcbw
                                                  where open lc-eql-pb2lc-bw weqlC wpbC lceql lcpb








  -- Proofs that a left covering preserves stuff


  module lc-bw2pres-jm (Cwbw : has-weak-bows ℂ) {F : efunctor ℂ 𝔼} (lcbw : is-left-covering-bw F)
                       where
    private
      module F where
        open efunctor-aux F public
        open is-left-covering-bw lcbw public
      module wbwℂ = has-weak-bows Cwbw
      module bw𝔼 = has-bows reg𝔼.hasbw

    module pres-jointly-monic {X Y : ℂ.Obj} {sp/ : ℂ.span/ X Y} (isjm/ : ℂ.is-jointly-monic/ sp/) where
      Fsp : 𝔼.span/ (F.ₒ X) (F.ₒ Y)
      Fsp = F.span/ sp/
      trkp : ℂ.bow-of sp/ sp/
      trkp = record { is-bw = ℂ.jm/→idiskpsp/ isjm/ }
      kpsp : 𝔼.bow-of Fsp Fsp
      kpsp = bw𝔼.bw-of Fsp Fsp
      private
        module sp where
          open ℂ.span/ sp/ public
          open ℂ.is-jointly-monic/ isjm/ public
        module Fsp = 𝔼.span/ Fsp
        module trkp = ℂ.bow-of trkp
        module kpsp = 𝔼.bow-of kpsp

      covbw : || 𝔼.Hom (F.ₒ sp.O12) kpsp.Bow ||
      covbw = kpsp.⟨ F.ₐ trkp.π//₁ , F.ₐ trkp.π//₂ ⟩[ F.∘∘ trkp.sqpf₁ , F.∘∘ trkp.sqpf₂ ]

      covbw-repi : 𝔼.is-regular-epi covbw
      covbw-repi = F.bwuniv-is-repi (ℂ.bw-of→wbw-of trkp)
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

                                                                                                           

  lcov-bw→pres-jm/ : (Cwbw : has-weak-bows ℂ) {F : efunctor ℂ 𝔼}
                           → is-left-covering-bw F → preserves-jointly-monic/ F
  lcov-bw→pres-jm/ wbwC lcbw = pres-jm/
                              where open lc-bw2pres-jm wbwC lcbw






  module lc-eql-pb2pres-jm (Cweql : has-weak-equalisers ℂ) (Cwpb : has-weak-pullbacks ℂ)
                           {F : efunctor ℂ 𝔼} (lceql : is-left-covering-eql F) (lcpb : is-left-covering-pb F)
                           = lc-bw2pres-jm (has-weql+wpb⇒has-wbw Cweql Cwpb)
                                           (lcov-eql+pb→lcov-bw Cweql Cwpb lceql lcpb)
                                                                                                           

  lcov-eql+pb→pres-jm/ : (Cweql : has-weak-equalisers ℂ) (Cwpb : has-weak-pullbacks ℂ) {F : efunctor ℂ 𝔼}
                            → is-left-covering-eql F → is-left-covering-pb F
                              → preserves-jointly-monic/ F
  lcov-eql+pb→pres-jm/ weqlC wpbC lceql lcpb = pres-jm/
                                              where open lc-eql-pb2pres-jm weqlC wpbC lceql lcpb





  
  module lc-prd-eql2pres-jm (wprdC : has-bin-weak-products ℂ) (weqlC : has-weak-equalisers ℂ)
                            {F : efunctor ℂ 𝔼} (lcprd : is-left-covering-prd F) (lceql : is-left-covering-eql F) =
                            lc-eql-pb2pres-jm weqlC
                                              (has-wprd+weql⇒has-wpb wprdC weqlC)
                                              lceql
                                              (lcov-×+eql→lcov-×/ wprdC weqlC lcprd lceql)


  lcov-prd+eql→pres-jm/ : (Cwprd : has-bin-weak-products ℂ) (Cweql : has-weak-equalisers ℂ) {F : efunctor ℂ 𝔼}
                            → is-left-covering-prd F → is-left-covering-eql F
                              → preserves-jointly-monic/ F
  lcov-prd+eql→pres-jm/ wprdC weqlC lcprd lceql = pres-jm/
                                                      where open lc-prd-eql2pres-jm wprdC weqlC lcprd lceql






  



  module lc-trm-prd-preserves-trm (Ehastrm : has-terminal 𝔼) {F : efunctor ℂ 𝔼}
                                  (lctrm : is-left-covering-trm F) (lcprd : is-left-covering-prd F)
                                  where
    private
      module F = efunctor-aux F
    open is-left-covering-prd lcprd
    open is-left-covering-trm lctrm
    open has-terminal Ehastrm renaming (trmOb to TE; istrm to TEistrm)
    private
      module TE = 𝔼.is-terminal TEistrm
      module ×𝔼 = bin-products-aux (𝔼.pb-trm-so-prd TEistrm reg𝔼.haspb)

    module trmuniv-is-iso {TC : ℂ.Obj} (TCistrm : ℂ.is-terminal TC) where
      private
        module TC = ℂ.is-terminal TCistrm

      covtrm : || 𝔼.Hom (F.ₒ TC) TE ||
      covtrm = TE.! (F.ₒ TC)

      covtrm-repi : 𝔼.is-regular-epi covtrm
      covtrm-repi = trmuniv-is-repi (ℂ.is-trm⇒is-wtrm TCistrm) TEistrm covtrm

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

      covprd : || 𝔼.Hom (F.ₒ TC) (F.ₒ TC ×𝔼.× F.ₒ TC) ||
      covprd = ×𝔼.< F.ₐ (ℂ.idar TC) , F.ₐ (ℂ.idar TC) >

      covprd-repi : 𝔼.is-regular-epi covprd
      covprd-repi = prduniv-is-repi (ℂ.prd-of⇒wprd-of trm-prd) ×𝔼.×of ×𝔼.×tr₁ ×𝔼.×tr₂
                  where open ecategory-aux-only 𝔼

      covprd-mono : 𝔼.is-monic covprd
      covprd-mono = record
        { mono-pf = λ {_} {h} {h'} pf → 
                  ~proof h                       ~[ lidggˢ r (×𝔼.×tr₁ ⊙ F.id) ⊙ assˢ ] /
                         ×𝔼.π₁ 𝔼.∘ covprd 𝔼.∘ h    ~[ ∘e pf r ] /
                         ×𝔼.π₁ 𝔼.∘ covprd 𝔼.∘ h'   ~[ ass ⊙ lidgg r (×𝔼.×tr₁ ⊙ F.id) ]∎
                         h' ∎
        }
        where open ecategory-aux-only 𝔼

      covprd-iso : 𝔼.is-iso covprd
      covprd-iso = cov-pf (𝔼.ridax covprd) covprd-mono
                 where open epis&monos-props 𝔼
                       open 𝔼.is-cover (repi-is-cover covprd-repi)


      covtrm-kp : 𝔼.pullback-of covtrm covtrm
      covtrm-kp = 𝔼.mkpb-of (𝔼.×is-pb-on! TEistrm ×𝔼.×isprd )
      private
        module kp = 𝔼.pullback-of covtrm-kp

      kp₁~kp₂ : kp.π/₁ 𝔼.~ kp.π/₂
      kp₁~kp₂ = ~proof
        kp.π/₁                             ~[ ridggˢ  r idcod ] /
        kp.π/₁ 𝔼.∘ covprd 𝔼.∘ covprd⁻¹    ~[ ass ⊙ ∘e r (×𝔼.×tr₁ ⊙ ×𝔼.×tr₂ˢ {f = F.ₐ (ℂ.idar TC)}) ⊙ assˢ ] /
        kp.π/₂ 𝔼.∘ covprd 𝔼.∘ covprd⁻¹    ~[ ridgg r idcod ]∎
        kp.π/₂ ∎
              where open 𝔼.is-iso covprd-iso renaming (invf to covprd⁻¹)
                    open ecategory-aux-only 𝔼

      covtrm-mono : 𝔼.is-monic covtrm
      covtrm-mono = 𝔼.π/₁~π/₂→mono covtrm-kp kp₁~kp₂
                  --where open epis&monos-props 𝔼

      covtrm-iso : 𝔼.is-iso covtrm
      covtrm-iso = cov-pf (𝔼.ridax covtrm) covtrm-mono
                 where open 𝔼.is-cover (𝔼.repi-is-cover covtrm-repi)


      Ftrm-is-trm : 𝔼.is-terminal (F.ₒ TC)
      Ftrm-is-trm = 𝔼.iso!-is! (𝔼.mk≅ (𝔼.inv-iso-pair isisopair)) TEistrm
                  where open 𝔼.is-iso covtrm-iso

    -- end trmuniv-is-iso
    
    pres-trm : preserves-terminal F
    pres-trm = record
      { pres-!-pf = Ftrm-is-trm
      }
      where open trmuniv-is-iso

  -- end lc-trm-prd-preserves-trm



  lcov!×→pres-trm :  (hastrm : has-terminal 𝔼) {F : efunctor ℂ 𝔼}
                              → is-left-covering-trm F → is-left-covering-prd F
                                → preserves-terminal F
  lcov!×→pres-trm hastrm lc! lc× = pres-trm
                                  where open lc-trm-prd-preserves-trm hastrm lc! lc×








  module lc-prd-eql-preserves-prd (Cwprd : has-bin-weak-products ℂ) (Cweql : has-weak-equalisers ℂ)
                                  {F : efunctor ℂ 𝔼} (lcprd : is-left-covering-prd F) (lceql : is-left-covering-eql F)
                                  where
    private
      module F = efunctor-aux F
    open is-left-covering-prd lcprd
    private
      module ×𝔼 = bin-products-aux reg𝔼.hasprd


    module pres-prd {sp : ℂ.span} (is× : ℂ.is-product sp) where
      open ℂ.span sp
      private
        module Fsp = 𝔼.span (F.span sp)
        module ×sp = ℂ.bin-product-not (ℂ.mk× is×)
        module ×F = 𝔼.bin-product-not (×𝔼.prdsp {F.ₒ O1} {F.ₒ O2})

      cov× : || 𝔼.Hom (F.ₒ O12) ×F.O12 ||
      cov× = ×F.< F.ₐ ×sp.π₁ , F.ₐ ×sp.π₂ >

      cov×-repi : 𝔼.is-regular-epi cov×
      cov×-repi = prduniv-is-repi (ℂ.prd-of⇒wprd-of (ℂ.mk×of is×)) ×𝔼.×of ×F.×tr₁ ×F.×tr₂

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



  lcov-×+eql→pres-× : (Cwprd : has-bin-weak-products ℂ) (Cweql : has-weak-equalisers ℂ) {F : efunctor ℂ 𝔼}
                         → is-left-covering-prd F → is-left-covering-eql F
                           → preserves-bin-products F
  lcov-×+eql→pres-× wprdC weqlC lc× lceql = pres-prd
                                                where open lc-prd-eql-preserves-prd wprdC weqlC lc× lceql







  module lc-eql-pb-preserves-pb (Cweql : has-weak-equalisers ℂ) (Cwpb : has-weak-pullbacks ℂ)
                                {F : efunctor ℂ 𝔼} (lceql : is-left-covering-eql F) (lcpb : is-left-covering-pb F)
                                where
    private
      module F = efunctor-aux F
    open is-left-covering-pb lcpb



    module pres-pb {sq : ℂ.comm-square} (is×/ : ℂ.is-pb-square sq) where
      open ℂ.comm-square sq
      private
        module Fsq = 𝔼.comm-square (F.sq sq)
        module ×/sq = ℂ.pullback-sq-not (ℂ.mkpb-sq is×/)
        module ×/F = 𝔼.pullback-of-not (reg𝔼.pb-of (F.ₐ down) (F.ₐ right))

      covpb-pf = F.∘∘ ×/sq.×/sqpf
      covpb : || 𝔼.Hom (F.ₒ ×/sq.ul) ×/F.ul ||
      covpb = ×/F.⟨ F.ₐ ×/sq.π/₁ , F.ₐ ×/sq.π/₂ ⟩[ covpb-pf ]

      covpb-repi : 𝔼.is-regular-epi covpb
      covpb-repi = pbuniv-is-repi (ℂ.pbof⇒wpbof (ℂ.mkpb-of is×/)) reg𝔼.×/of (×/F.×/tr₁ covpb-pf) (×/F.×/tr₂ covpb-pf)

      covpb-mono : 𝔼.is-monic covpb
      covpb-mono = 𝔼.jointly-monic-tr (×/F.×/tr₁ covpb-pf) (×/F.×/tr₂ covpb-pf)
                                       (pres-jm/-pf (ℂ.π/s-are-jointly-monic/ (ℂ.mkpb-sq is×/)))
                 where open preserves-jointly-monic/ (lcov-eql+pb→pres-jm/ Cweql Cwpb lceql lcpb)
      covpb-iso : 𝔼.is-iso covpb
      covpb-iso = 𝔼.monic-cover-is-iso covpb-mono (𝔼.repi-is-cover covpb-repi)

      Fsq-is×/ : 𝔼.is-pb-square (F.sq sq)
      Fsq-is×/ = 𝔼.cosp≅pb-is-pb reg𝔼.×/of covpb-iso (×/F.×/tr₁ covpb-pf) (×/F.×/tr₂ covpb-pf)

    -- end pres-pb


    pres-pb : preserves-pullbacks F
    pres-pb = record
            { pres-pbsq-pf = pres-pb.Fsq-is×/
            }

  -- end lc-eql-pb-preserves-pb




  lcov-eql+pb→pres-pb : (Cweql : has-weak-equalisers ℂ) (Cwpb : has-weak-pullbacks ℂ) {F : efunctor ℂ 𝔼}
                           → is-left-covering-eql F → is-left-covering-pb F
                             → preserves-pullbacks F
  lcov-eql+pb→pres-pb weqlC wpbC lceql lcpb = pres-pb
                                            where open lc-eql-pb-preserves-pb weqlC wpbC lceql lcpb

-- end left-covering-into-regular-props





-- All the properties proved in the module above

×→[lcov-×+eql→lcov-×/] : {ℂ 𝔼 : ecategory} (regE : is-regular 𝔼)
                           (prdC : has-bin-products ℂ) {F : efunctor ℂ 𝔼}
                               → is-left-covering-prd F → is-left-covering-eql F
                                 → is-left-covering-pb F
×→[lcov-×+eql→lcov-×/] {ℂ} {𝔼} regE = lp.×→[lcov-×+eql→lcov-×/]
                                       where module lp = left-covering-into-regular-props ℂ 𝔼 regE




lcov-×+eql→lcov-×/ : {ℂ 𝔼 : ecategory} (regE : is-regular 𝔼)
                      (wprdC : has-bin-weak-products ℂ) (weqlC : has-weak-equalisers ℂ) {F : efunctor ℂ 𝔼}
                        → is-left-covering-prd F → is-left-covering-eql F
                          → is-left-covering-pb F
lcov-×+eql→lcov-×/ {ℂ} {𝔼} regE = lp.lcov-×+eql→lcov-×/
                                  where module lp = left-covering-into-regular-props ℂ 𝔼 regE



lcov-eql+pb→lcov-bw : {ℂ 𝔼 : ecategory} (regE : is-regular 𝔼)
                       (Cweql : has-weak-equalisers ℂ) (Cwpb : has-weak-pullbacks ℂ) {F : efunctor ℂ 𝔼}
                         → is-left-covering-eql F → is-left-covering-pb F
                           →  is-left-covering-bw F
lcov-eql+pb→lcov-bw {ℂ} {𝔼} regE = lp.lcov-eql+pb→lcov-bw
                                   where module lp = left-covering-into-regular-props ℂ 𝔼 regE



lcov-bw→pres-jm/ : {ℂ 𝔼 : ecategory} (regE : is-regular 𝔼)
                    (Cwbw : has-weak-bows ℂ) {F : efunctor ℂ 𝔼}
                         → is-left-covering-bw F → preserves-jointly-monic/ F
lcov-bw→pres-jm/ {ℂ} {𝔼} regE = lp.lcov-bw→pres-jm/
                                where module lp = left-covering-into-regular-props ℂ 𝔼 regE


lcov-eql+pb→pres-jm/ : {ℂ 𝔼 : ecategory} (regE : is-regular 𝔼)
                        (Cweql : has-weak-equalisers ℂ) (Cwpb : has-weak-pullbacks ℂ) {F : efunctor ℂ 𝔼}
                          → is-left-covering-eql F → is-left-covering-pb F
                            → preserves-jointly-monic/ F
lcov-eql+pb→pres-jm/ {ℂ} {𝔼} regE = lp.lcov-eql+pb→pres-jm/
                                    where module lp = left-covering-into-regular-props ℂ 𝔼 regE


lcov-prd+eql→pres-jm/ : {ℂ 𝔼 : ecategory} (regE : is-regular 𝔼)
                         (Cwprd : has-bin-weak-products ℂ) (Cweql : has-weak-equalisers ℂ) {F : efunctor ℂ 𝔼}
                          → is-left-covering-prd F → is-left-covering-eql F
                            → preserves-jointly-monic/ F
lcov-prd+eql→pres-jm/ {ℂ} {𝔼} regE = lp.lcov-prd+eql→pres-jm/
                                     where module lp = left-covering-into-regular-props ℂ 𝔼 regE


lcov!×→pres-trm : {ℂ 𝔼 : ecategory} (regE : is-regular 𝔼)
                   (hastrm : has-terminal 𝔼) {F : efunctor ℂ 𝔼}
                            → is-left-covering-trm F → is-left-covering-prd F
                              → preserves-terminal F
lcov!×→pres-trm {ℂ} {𝔼} regE = lp.lcov!×→pres-trm
                               where module lp = left-covering-into-regular-props ℂ 𝔼 regE



lcov-×+eql→pres-× : {ℂ 𝔼 : ecategory} (regE : is-regular 𝔼)
                     (Cwprd : has-bin-weak-products ℂ) (Cweql : has-weak-equalisers ℂ) {F : efunctor ℂ 𝔼}
                       → is-left-covering-prd F → is-left-covering-eql F
                         → preserves-bin-products F
lcov-×+eql→pres-× {ℂ} {𝔼} regE = lp.lcov-×+eql→pres-×
                                 where module lp = left-covering-into-regular-props ℂ 𝔼 regE




lcov-eql+pb→pres-pb : {ℂ 𝔼 : ecategory} (regE : is-regular 𝔼)
                       (Cweql : has-weak-equalisers ℂ) (Cwpb : has-weak-pullbacks ℂ) {F : efunctor ℂ 𝔼}
                         → is-left-covering-eql F → is-left-covering-pb F
                           → preserves-pullbacks F
lcov-eql+pb→pres-pb {ℂ} {𝔼} regE = lp.lcov-eql+pb→pres-pb
                                   where module lp = left-covering-into-regular-props ℂ 𝔼 regE










-- left covering functor from cat with weak fin limits to exact cat 


module left-covering-into-exact-props {ℂ : ecategory} (hasfwl : has-fin-weak-limits ℂ)
                                      {𝔼 : ecategory} (exE : is-exact 𝔼)
                                      {F : efunctor ℂ 𝔼} (lcovF : is-left-covering F)
                                      where
  private
    module ℂ where
      open ecategory ℂ public
      open comm-shapes ℂ public
      open pseudo-eq-rel-defs ℂ public
      open finite-limits-d&p ℂ public
      open finite-weak-limits-d&p ℂ public
      open limits→weak-limits ℂ public
    module wlℂ where
      open has-fin-weak-limits hasfwl public
      open has-weak-terminal haswtrm public
      open has-weak-equalisers hasweql using (weql-of) public
      open has-weak-pullbacks haswpb using (wpb-of) public
      open has-weak-bows haswbw using (wbw-of) public
    module 𝔼 where
      open ecategory 𝔼 public
      open comm-shapes 𝔼 public
      open epis&monos-defs 𝔼 public
      open epis&monos-props 𝔼 public
      open eq-rel-defs 𝔼 public
      open image-fact-defs 𝔼 public
      open finite-limits-d&p 𝔼 public
    module ex𝔼 where
      open is-exact exE public
      open has-bin-products hasprd using (prd-of) public
      open has-equalisers haseql using (eql-of) public
      open has-pullbacks haspb using (pb-of) public
      open exact-cat-props exE public
      open is-regular//has-finlim exact-is-regular//has-fl public
      open has-terminal hastrm public
    module F = efunctor-aux F
    module lcF where
      open is-left-covering lcovF public
      open left-covering-into-regular-props ℂ 𝔼 ex𝔼.exact-is-regular public
    --module lcpF = left-covering-props-on-regular-cat ℂ 𝔼 ex𝔼.exact-is-regular


  -- image fact of the image of a peq under a left covering functor is an equivalence relation

  module eqrel-from-peq-via-left-covering (A : ℂ.Peq) where
    private
      module presF where
        open preserves-pullbacks (lcF.lcov-eql+pb→pres-pb wlℂ.hasweql wlℂ.haswpb lcF.lceql lcF.lc×/) public
      module A = ℂ.Peq A
      module FAL² = 𝔼.product-of-not (ex𝔼.prd-of (F.ₒ A.Lo) (F.ₒ A.Lo))

    -- main definitions
    F% : || 𝔼.Hom (F.ₒ A.Hi) FAL².O12 ||
    F% = FAL².< F.ₐ A.%0 , F.ₐ A.%1 >
    imgF% : 𝔼.img-fact-of F%
    imgF% = ex𝔼.img-of F%
    private
      module imgF% = 𝔼.img-fact-of imgF%
    r₁ r₂ : || 𝔼.Hom imgF%.Ob (F.ₒ A.Lo) ||    
    r₁ = FAL².π₁ 𝔼.∘ imgF%.M
    r₂ = FAL².π₂ 𝔼.∘ imgF%.M
    imgF%tr₁ = ~proof r₁ 𝔼.∘ imgF%.C            ~[ assˢ ⊙ ∘e imgF%.tr r  ] /
                      FAL².π₁ 𝔼.∘ F%            ~[ FAL².×tr₁ ]∎
                      F.ₐ A.%0 ∎
             where open ecategory-aux-only 𝔼                     
    imgF%tr₂ = ~proof r₂ 𝔼.∘ imgF%.C           ~[ assˢ ⊙ ∘e imgF%.tr r  ] /
                      FAL².π₂ 𝔼.∘ F%           ~[ FAL².×tr₂ ]∎
                      F.ₐ A.%1 ∎
             where open ecategory-aux-only 𝔼            

    -- auxiliary definitions
    private
    -- jointly monic
      rjm : 𝔼.is-jointly-monic/ (𝔼.mkspan/ r₁ r₂)
      rjm = 𝔼.<>monic→isjm/-ar FAL².×of imgF%.M-is-monic
    -- reflexive
      imgF%ρ : || 𝔼.Hom (F.ₒ A.Lo) imgF%.Ob ||
      imgF%ρ  = imgF%.C 𝔼.∘ F.ₐ A.ρ    
    -- symmetric
      imgF%σ-monic : 𝔼.is-monic FAL².< r₂ , r₁ >
      imgF%σ-monic = 𝔼.isjm/→<>monic (𝔼.jointly-monic-sym rjm) FAL².×of
      imgF%σ-comm : FAL².< r₂ , r₁ > 𝔼.∘ imgF%.C 𝔼.∘ F.ₐ A.σ 𝔼.~ F%
      imgF%σ-comm = ~proof
        FAL².< r₂ , r₁ > 𝔼.∘ imgF%.C 𝔼.∘ F.ₐ A.σ   ~[ ass ⊙ ∘e r (FAL².<>ar~<> imgF%tr₂ imgF%tr₁) ] /
        FAL².< F.ₐ A.%1 , F.ₐ A.%0 > 𝔼.∘ F.ₐ A.σ    ~[ FAL².<>ar~<> (F.∘ax A.σ-ax₁) (F.∘ax A.σ-ax₀) ]∎
        F% ∎
                  where open ecategory-aux-only 𝔼
      imgF%σ : || 𝔼.Hom imgF%.Ob imgF%.Ob ||
      imgF%σ = imgF%.univ imgF%σ-monic imgF%σ-comm
    -- transitive
      τF%pb : 𝔼.pullback-of (F.ₐ A.%1) (F.ₐ A.%0)
      τF%pb = ex𝔼.pb-of (F.ₐ A.%1) (F.ₐ A.%0)
      τrpb : 𝔼.pullback-of r₂ r₁
      τrpb = ex𝔼.pb-of r₂ r₁
      module τrpb = 𝔼.pullback-of-not τrpb
      module τAwpb = ℂ.wpullback-of-not A.τwpb
      module τF%pb = 𝔼.pullback-of-not τF%pb
      F%τeq : F% 𝔼.∘ F.ₐ A.τ   𝔼.~   FAL².< F.ₐ (A.%0 ℂ.∘ τAwpb.wπ/₁) , F.ₐ (A.%1 ℂ.∘ τAwpb.wπ/₂) >
      F%τeq = FAL².<>ar~<> (F.∘ax A.τ-ax₀) (F.∘ax A.τ-ax₁)          
      outcov-pf = F.ₐ A.%1 𝔼.∘ F.ₐ τAwpb.wπ/₁  ~[ F.∘ax-rf ⊙ F.ext τAwpb.w×/sqpf ⊙ F.∘ax-rfˢ ]
                  F.ₐ A.%0 𝔼.∘ F.ₐ τAwpb.wπ/₂
                where open ecategory-aux-only 𝔼
      outcov : || 𝔼.Hom (F.ₒ τAwpb.ul) τF%pb.ul ||
      outcov = τF%pb.⟨ F.ₐ τAwpb.wπ/₁ , F.ₐ τAwpb.wπ/₂ ⟩[ outcov-pf ]
      outcov-repi : 𝔼.is-regular-epi outcov
      outcov-repi = lcF.pbuniv-is-repi A.τwpb τF%pb (τF%pb.×/tr₁ outcov-pf) (τF%pb.×/tr₂ outcov-pf)
        module c×c where
          open 𝔼.×/ₐdef τrpb τF%pb public
          open ex𝔼.×/ₐ-of-repis-is-repi τrpb τF%pb imgF%tr₂ imgF%tr₁
                                         (ex𝔼.any-imgC-is-repi imgF%) (ex𝔼.any-imgC-is-repi imgF%)
                                         public
      τcov : || 𝔼.Hom (F.ₒ τAwpb.ul) τrpb.ul ||
      τcov = c×c.×/arcan 𝔼.∘ outcov
      τcov-repi : 𝔼.is-regular-epi τcov
      τcov-repi = ∘c c×c.×/arcanProp outcov-repi
                where open is-ecat-congr ex𝔼.regular-epi-is-congr
      private
        module τc = 𝔼.is-regular-epi τcov-repi

      imgF%τ-pf-aux1 = ~proof
        r₁ 𝔼.∘ τrpb.π/₁ 𝔼.∘ τcov                     ~[ ∘e (ass ⊙ ∘e r (τrpb.×/tr₁ (c×c.×/ₐcanpf imgF%tr₂ imgF%tr₁))) r ] /
        r₁ 𝔼.∘ (imgF%.C 𝔼.∘ τF%pb.π/₁) 𝔼.∘ outcov   ~[ ass ⊙ ∘e r (ass ⊙ ∘e r imgF%tr₁) ⊙ assˢ ] /
        F.ₐ A.%0 𝔼.∘ τF%pb.π/₁ 𝔼.∘ outcov            ~[  ∘e (τF%pb.×/tr₁ outcov-pf) r ⊙ F.∘ax-rf ]∎
        F.ₐ (A.%0 ℂ.∘ τAwpb.wπ/₁) ∎
                   where open ecategory-aux-only 𝔼
      imgF%τ-pf-aux2 = ~proof
        r₂ 𝔼.∘ τrpb.π/₂ 𝔼.∘ τcov                     ~[ ∘e (ass ⊙ ∘e r (τrpb.×/tr₂ (c×c.×/ₐcanpf imgF%tr₂ imgF%tr₁))) r ] /
        r₂ 𝔼.∘ (imgF%.C 𝔼.∘ τF%pb.π/₂) 𝔼.∘ outcov   ~[ ass ⊙ ∘e r (ass ⊙ ∘e r imgF%tr₂) ⊙ assˢ ] /
        F.ₐ A.%1 𝔼.∘ τF%pb.π/₂ 𝔼.∘ outcov            ~[  ∘e (τF%pb.×/tr₂ outcov-pf) r ⊙ F.∘ax-rf ]∎
        F.ₐ (A.%1 ℂ.∘ τAwpb.wπ/₂) ∎
                   where open ecategory-aux-only 𝔼
      imgF%τ-pf-aux : FAL².< F.ₐ (A.%0 ℂ.∘ τAwpb.wπ/₁) , F.ₐ (A.%1 ℂ.∘ τAwpb.wπ/₂) >
                             𝔼.~ FAL².< r₁ 𝔼.∘ τrpb.π/₁ , r₂ 𝔼.∘ τrpb.π/₂ > 𝔼.∘ τcov
      imgF%τ-pf-aux = FAL².<>ar~<>ˢ (assˢ ⊙ imgF%τ-pf-aux1) (assˢ ⊙ imgF%τ-pf-aux2)
                    where open ecategory-aux-only 𝔼
      imgF%τ-pf : (imgF%.C 𝔼.∘ F.ₐ A.τ) 𝔼.∘ τc.rel₁ 𝔼.~ (imgF%.C 𝔼.∘ F.ₐ A.τ) 𝔼.∘ τc.rel₂
      imgF%τ-pf = mono-pf (~proof
        imgF%.M 𝔼.∘ (imgF%.C 𝔼.∘ F.ₐ A.τ) 𝔼.∘ τc.rel₁                             ~[ ass ⊙ ∘e r (ass ⊙ ∘e r imgF%.tr) ] /
        (F% 𝔼.∘ F.ₐ A.τ) 𝔼.∘ τc.rel₁                                                ~[ ∘e r F%τeq ] /
        FAL².< F.ₐ (A.%0 ℂ.∘ τAwpb.wπ/₁) , F.ₐ (A.%1 ℂ.∘ τAwpb.wπ/₂) > 𝔼.∘ τc.rel₁   ~[ ∘e r imgF%τ-pf-aux ⊙ assˢ  ] /
        FAL².< r₁ 𝔼.∘ τrpb.π/₁ , r₂ 𝔼.∘ τrpb.π/₂ > 𝔼.∘ τcov 𝔼.∘ τc.rel₁            ~[ ∘e τc.eq r  ] /
        FAL².< r₁ 𝔼.∘ τrpb.π/₁ , r₂ 𝔼.∘ τrpb.π/₂ > 𝔼.∘ τcov 𝔼.∘ τc.rel₂            ~[  ass ⊙ ∘e r (imgF%τ-pf-aux ˢ) ] /
        FAL².< F.ₐ (A.%0 ℂ.∘ τAwpb.wπ/₁) , F.ₐ (A.%1 ℂ.∘ τAwpb.wπ/₂) > 𝔼.∘ τc.rel₂   ~[ ∘e r (F%τeq ˢ) ] /
        (F% 𝔼.∘ F.ₐ A.τ) 𝔼.∘ τc.rel₂                                           ~[ ∘e r (∘e r (imgF%.tr ˢ) ⊙ assˢ) ⊙ assˢ ]∎
        imgF%.M 𝔼.∘ (imgF%.C 𝔼.∘ F.ₐ A.τ) 𝔼.∘ τc.rel₂ ∎)
              where open ecategory-aux-only 𝔼
                    open 𝔼.is-monic (ex𝔼.img-of.M-is-monic F%)

      imgF%τ : || 𝔼.Hom τrpb.ul imgF%.Ob ||
      imgF%τ = τc.univ {imgF%.Ob} (imgF%.C 𝔼.∘ F.ₐ A.τ) imgF%τ-pf
      imgF%τ-tr : imgF%τ 𝔼.∘ τcov 𝔼.~ imgF%.C 𝔼.∘ F.ₐ A.τ
      imgF%τ-tr = τc.univ-eq {imgF%.Ob} {imgF%.C 𝔼.∘ F.ₐ A.τ} imgF%τ-pf
      imgF%τ-ax₀ : r₁ 𝔼.∘ imgF%τ 𝔼.~ r₁ 𝔼.∘ τrpb.π/₁
      imgF%τ-ax₀ = τc.epi-pf (~proof
        (r₁ 𝔼.∘ imgF%τ) 𝔼.∘ τcov            ~[ assˢ ⊙ ∘e imgF%τ-tr r ⊙ ass ⊙ ∘e r imgF%tr₁ ] /
        F.ₐ A.%0 𝔼.∘ F.ₐ A.τ                 ~[ F.∘ax A.τ-ax₀ ⊙ imgF%τ-pf-aux1 ˢ ⊙ ass ]∎
        (r₁ 𝔼.∘ τrpb.π/₁) 𝔼.∘ τcov ∎)
                 where open ecategory-aux-only 𝔼
      imgF%τ-ax₁ = τc.epi-pf (~proof
        (r₂ 𝔼.∘ imgF%τ) 𝔼.∘ τcov            ~[ assˢ ⊙ ∘e imgF%τ-tr r ⊙ ass ⊙ ∘e r imgF%tr₂ ] / 
        F.ₐ A.%1 𝔼.∘ F.ₐ A.τ                 ~[ F.∘ax A.τ-ax₁ ⊙ (imgF%τ-pf-aux2 ˢ) ⊙ ass ]∎
        (r₂ 𝔼.∘ τrpb.π/₂) 𝔼.∘ τcov ∎)
                 where open ecategory-aux-only 𝔼
    -- equivalece relation
      iseqr : 𝔼.is-eq-rel {imgF%.Ob} {F.ₒ A.Lo} r₁ r₂
      iseqr = record
        { isjm/ = rjm
        ; isρ = record
              { ρ = imgF%ρ
              ; ρ-ax₀ = ass ⊙ ∘e r imgF%tr₁ ⊙ F.∘ax-rf ⊙ F.idax A.ρ-ax₀
              ; ρ-ax₁ = ass ⊙ ∘e r imgF%tr₂ ⊙ F.∘ax-rf ⊙ F.idax A.ρ-ax₁
              }
        ; isσ = record
              { σ = imgF%σ
              ; σ-ax₀ = ∘e r (FAL².×tr₂ˢ {f = r₂}) ⊙ assˢ ⊙ ∘e (imgF%.univ-tr imgF%σ-monic imgF%σ-comm) r
              ; σ-ax₁ = ∘e r (FAL².×tr₁ˢ {g = r₁}) ⊙ assˢ ⊙ ∘e (imgF%.univ-tr imgF%σ-monic imgF%σ-comm) r
              }
        ; τpb = τrpb
        ; isτ = record
              { τ = imgF%τ
              ; τ-ax₀ = imgF%τ-ax₀
              ; τ-ax₁ = imgF%τ-ax₁
              }
        }
        where open ecategory-aux-only 𝔼
    -- end private
      
    eqrel/ : 𝔼.eqrel-over (F.ₒ A.Lo)
    eqrel/ = record
      { relOb = imgF%.Ob
      ; r₁ = r₁
      ; r₂ = r₂
      ; iseqrel = iseqr
      }
  -- end eqrel-from-peq-via-left-covering

{-
  private
    module peq = ℂ.PeqOver
    module ×ᶜ (A B : 𝔼.Obj) = 𝔼.product-of-not (ex𝔼.prd-of A B)
  peq2Fimg-ar : {X : ℂ.Obj} (R : ℂ.PeqOver X)
                   → || 𝔼.Hom (F.ₒ (peq.Hi R)) (×ᶜ.O12 (F.ₒ X) (F.ₒ X)) ||
  peq2Fimg-ar A = F%
              where open eqrel-from-peq-via-left-covering (ℂ.mkpeq-c A)
  peq2Fimg : {X : ℂ.Obj} (A : ℂ.PeqOver X) → 𝔼.img-fact-of (peq2Fimg-ar A)
  peq2Fimg A = imgF%
             where open eqrel-from-peq-via-left-covering (ℂ.mkpeq-c A)

  peq2Feqrel : {X : ℂ.Obj} (A : ℂ.PeqOver X) → 𝔼.eqrel-over (F.ₒ X)
  peq2Feqrel A = eqrel/
               where open eqrel-from-peq-via-left-covering (ℂ.mkpeq-c A)-}

-- end left-covering-into-exact-props















{-                      The following module is to keep for historical reasons,
                        to learn from the comparison with module lc-bw2pres-jm... 






  module lc-eql-pb2pres-jm (Cweql : has-weak-equalisers ℂ) (Cwpb : has-weak-pullbacks ℂ) (Eeql : has-equalisers 𝔼)
                           {F : efunctor ℂ 𝔼} (lceql : is-left-covering-eql F) (lcpb : is-left-covering-pb F)
                           where
    private
      module F = efunctor-aux F
    open is-left-covering-pb lcpb
    open is-left-covering-eql lceql
    private
      module wpbℂ = weak-pullbacks-aux (wpb-aux Cwpb)
      module weqlℂ = has-weak-equalisers Cweql
      module eql𝔼 = has-equalisers Eeql

    -- these definitions should go in a more appropriate place... now can be reformulated with bows
    record wkernel-pair-span-of {X Y : ℂ.Obj} (sp/ : ℂ.span/ X Y) : Set₁ where
      open ℂ.span/ sp/
      field
        wkpOb : ℂ.Obj
        wkp₁ wkp₂ : || ℂ.Hom wkpOb O12 ||
        wkp-eq1 : a1 ℂ.∘ wkp₁ ℂ.~ a1 ℂ.∘ wkp₂
        wkp-eq2 : a2 ℂ.∘ wkp₁ ℂ.~ a2 ℂ.∘ wkp₂
        wsp⟨_,_⟩[_,_] : {Z : ℂ.Obj} (f g : || ℂ.Hom Z O12 ||)
                           → a1 ℂ.∘ f ℂ.~ a1 ℂ.∘ g → a1 ℂ.∘ f ℂ.~ a1 ℂ.∘ g → || ℂ.Hom Z wkpOb ||
        wkp-tr₁ : {Z : ℂ.Obj} {f g : || ℂ.Hom Z O12 ||} (pf1 : a1 ℂ.∘ f ℂ.~ a1 ℂ.∘ g) (pf2 : a1 ℂ.∘ f ℂ.~ a1 ℂ.∘ g)
                      → wkp₁ ℂ.∘ wsp⟨ f , g ⟩[ pf1 , pf2 ] ℂ.~ f
        wkp-tr₂ : {Z : ℂ.Obj} {f g : || ℂ.Hom Z O12 ||} (pf1 : a1 ℂ.∘ f ℂ.~ a1 ℂ.∘ g) (pf2 : a1 ℂ.∘ f ℂ.~ a1 ℂ.∘ g)
                      → wkp₂ ℂ.∘ wsp⟨ f , g ⟩[ pf1 , pf2 ] ℂ.~ g


    record kernel-pair-span-of {A B : 𝔼.Obj} (sp/ : 𝔼.span/ A B) : Set₁ where
      open 𝔼.span/ sp/
      field
        kpOb : 𝔼.Obj
        kp₁ kp₂ : || 𝔼.Hom kpOb O12 ||
        kp-eq1 : a1 𝔼.∘ kp₁ 𝔼.~ a1 𝔼.∘ kp₂
        kp-eq2 : a2 𝔼.∘ kp₁ 𝔼.~ a2 𝔼.∘ kp₂
        sp⟨_,_⟩[_,_] : {Z : 𝔼.Obj} (f g : || 𝔼.Hom Z O12 ||)
                           → a1 𝔼.∘ f 𝔼.~ a1 𝔼.∘ g → a1 𝔼.∘ f 𝔼.~ a1 𝔼.∘ g → || 𝔼.Hom Z kpOb ||
        kp-tr₁ : {Z : 𝔼.Obj} {f g : || 𝔼.Hom Z O12 ||} (pf1 : a1 𝔼.∘ f 𝔼.~ a1 𝔼.∘ g) (pf2 : a1 𝔼.∘ f 𝔼.~ a1 𝔼.∘ g)
                      → kp₁ 𝔼.∘ sp⟨ f , g ⟩[ pf1 , pf2 ] 𝔼.~ f
        kp-tr₂ : {Z : 𝔼.Obj} {f g : || 𝔼.Hom Z O12 ||} (pf1 : a1 𝔼.∘ f 𝔼.~ a1 𝔼.∘ g) (pf2 : a1 𝔼.∘ f 𝔼.~ a1 𝔼.∘ g)
                      → kp₂ 𝔼.∘ sp⟨ f , g ⟩[ pf1 , pf2 ] 𝔼.~ g
        kp-uq : {Z : 𝔼.Obj} {h h' : || 𝔼.Hom Z kpOb ||}
                     → kp₁ 𝔼.∘ h 𝔼.~ kp₁ 𝔼.∘ h' → kp₂ 𝔼.∘ h 𝔼.~ kp₂ 𝔼.∘ h' → h 𝔼.~ h'

    private
      module wkp-sp = wkernel-pair-span-of
      module kp-sp = kernel-pair-span-of
      
{-
    lc-kerp-spans : {X Y : ℂ.Obj} {sp/ : ℂ.span/ X Y} (wkp : wkernel-pair-span-of sp/) (kp : kernel-pair-span-of (Fsp sp/))
                    {kp-cov : || 𝔼.Hom (F.ₒ (wkp-sp.wkpOb wkp)) (kp-sp.kpOb kp) ||}
                      → kp-sp.kp₁ kp 𝔼.∘ kp-cov 𝔼.~ F.ₐ (wkp-sp.wkp₁ wkp) → kp-sp.kp₂ kp 𝔼.∘ kp-cov 𝔼.~ F.ₐ (wkp-sp.wkp₂ wkp)
                        → 𝔼.is-regular-epi kp-cov
    lc-kerp-spans wkp kp {kp-cov} tr₁ tr₂ = {!!}
                                          where open wkp-sp wkp
                                                open kp-sp kp
-}

    module pres-jointly-monic {X Y : ℂ.Obj} {sp/ : ℂ.span/ X Y} (isjm/ : ℂ.is-jointly-monic/ sp/) where
      private
        module sp where
          open ℂ.span/ sp/ public
          open ℂ.is-jointly-monic/ isjm/ public
        module wkpO1 = ℂ.wpullback-of-not (wpbℂ.wpb-of sp.a1 sp.a1)
        module weqlO2 = ℂ.wequaliser-of (weqlℂ.weql-of (sp.a2 ℂ.∘ wkpO1.wπ/₁) (sp.a2 ℂ.∘ wkpO1.wπ/₂))
        module kpFO1 = 𝔼.pullback-sq-not (reg𝔼.pbsq {a = F.ₐ sp.a1} {F.ₐ sp.a1})
        module eqlFO2 = 𝔼.equaliser-of (eql𝔼.eql-of (F.ₐ sp.a2 𝔼.∘ kpFO1.π/₁) (F.ₐ sp.a2 𝔼.∘ kpFO1.π/₂))
        module eqlO2 = 𝔼.equaliser-of (eql𝔼.eql-of (F.ₐ (sp.a2 ℂ.∘ wkpO1.wπ/₁)) (F.ₐ (sp.a2 ℂ.∘ wkpO1.wπ/₂)))

      wbow-π₁ wbow-π₂ : || ℂ.Hom weqlO2.wEql sp.O12 ||
      wbow-π₁ = wkpO1.wπ/₁ ℂ.∘ weqlO2.weqlar
      wbow-π₂ = wkpO1.wπ/₂ ℂ.∘ weqlO2.weqlar

      wbw-sqpf₁ : sp.a1 ℂ.∘ wbow-π₁ ℂ.~ sp.a1 ℂ.∘ wbow-π₂
      wbw-sqpf₁ = ass ⊙ ∘e r wkpO1.w×/sqpf ⊙ assˢ
                where open ecategory-aux-only ℂ
      wbw-sqpf₂ : sp.a2 ℂ.∘ wbow-π₁ ℂ.~ sp.a2 ℂ.∘ wbow-π₂
      wbw-sqpf₂ = ass ⊙ weqlO2.weqleq ⊙ assˢ
                where open ecategory-aux-only ℂ
      wbow-πs-are-eq : wbow-π₁ ℂ.~ wbow-π₂
      wbow-πs-are-eq = sp.jm-pf wbw-sqpf₁ wbw-sqpf₂

      cov-eql-pf = F.∘∘ weqlO2.weqleq
      cov-eql : || 𝔼.Hom (F.ₒ weqlO2.wEql) eqlO2.Eql ||
      cov-eql = (F.ₐ weqlO2.weqlar) eqlO2.|eql[ cov-eql-pf ]

      cov-eql-repi : 𝔼.is-regular-epi cov-eql
      cov-eql-repi = eqluniv-is-repi (weqlℂ.weql-of (sp.a2 ℂ.∘ wkpO1.wπ/₁) (sp.a2 ℂ.∘ wkpO1.wπ/₂))
                                     (eql𝔼.eql-of (F.ₐ (sp.a2 ℂ.∘ wkpO1.wπ/₁)) (F.ₐ (sp.a2 ℂ.∘ wkpO1.wπ/₂)))
                                     (eqlO2.eqltr (F.∘∘ weqlO2.weqleq))

      cov-pb-pf = F.∘∘ wkpO1.w×/sqpf
      cov-pb : || 𝔼.Hom (F.ₒ wkpO1.ul) kpFO1.ul ||
      cov-pb = kpFO1.⟨ F.ₐ wkpO1.wπ/₁ , F.ₐ  wkpO1.wπ/₂ ⟩[ cov-pb-pf ]

      cov-pb-repi : 𝔼.is-regular-epi cov-pb
      cov-pb-repi = pbuniv-is-repi wkpO1.w×/of kpFO1.×/of (kpFO1.×/tr₁ (F.∘∘ wkpO1.w×/sqpf)) (kpFO1.×/tr₂ (F.∘∘ wkpO1.w×/sqpf))


      med-ar-pf : (F.ₐ sp.a2 𝔼.∘ kpFO1.π/₁) 𝔼.∘ (cov-pb 𝔼.∘ eqlO2.eqlar) 𝔼.~ (F.ₐ sp.a2 𝔼.∘ kpFO1.π/₂) 𝔼.∘ (cov-pb 𝔼.∘ eqlO2.eqlar)
      med-ar-pf = ~proof (F.ₐ sp.a2 𝔼.∘ kpFO1.π/₁) 𝔼.∘ (cov-pb 𝔼.∘ eqlO2.eqlar)      ~[ ass ⊙ ∘e r (assˢ ⊙ ∘e (kpFO1.×/tr₁ cov-pb-pf) r) ] /
                          (F.ₐ sp.a2 𝔼.∘ F.ₐ wkpO1.wπ/₁) 𝔼.∘ eqlO2.eqlar             ~[ ∘e r F.∘ax-rf ⊙ eqlO2.eqleq ⊙ ∘e r F.∘ax-rfˢ ] /
                          (F.ₐ sp.a2 𝔼.∘ F.ₐ wkpO1.wπ/₂) 𝔼.∘ eqlO2.eqlar             ~[ ∘e r (∘e (kpFO1.×/tr₂ cov-pb-pf ˢ) r ⊙ ass) ⊙ assˢ ]∎
                          (F.ₐ sp.a2 𝔼.∘ kpFO1.π/₂) 𝔼.∘ (cov-pb 𝔼.∘ eqlO2.eqlar) ∎
                where open ecategory-aux-only 𝔼

      med-ar : || 𝔼.Hom eqlO2.Eql eqlFO2.Eql ||
      med-ar = eqlFO2._|eql[_] (cov-pb 𝔼.∘ eqlO2.eqlar) med-ar-pf

      med-ar-sqpf : eqlFO2.eqlar 𝔼.∘ med-ar 𝔼.~ cov-pb 𝔼.∘ eqlO2.eqlar
      med-ar-sqpf = eqlFO2.eqltr med-ar-pf

      med-ar-pbsq : 𝔼.pb-square
      med-ar-pbsq = 𝔼.mkpb-sq {×/sq = 𝔼.mksq (𝔼.mksq/ med-ar-sqpf)}
                            (record
                  { ⟨_,_⟩[_] = λ h k pf → k eqlO2.|eql[ univ-pf pf ]
                  ; ×/tr₁ = λ pf → eqlFO2.eqluq (ass ⊙ ∘e r med-ar-sqpf ⊙ assˢ ⊙ ∘e (eqlO2.eqltr (univ-pf pf)) r ⊙ pf ˢ)
                  ; ×/tr₂ = λ pf → eqlO2.eqltr (univ-pf pf)
                  ; ×/uq = λ _ → eqlO2.eqluq
                  })
                  where open ecategory-aux-only 𝔼
                        univ-pf : {C : 𝔼.Obj} {h : || 𝔼.Hom C eqlFO2.Eql ||} {k : || 𝔼.Hom C (F.ₒ wkpO1.ul) ||}
                                  (pf : eqlFO2.eqlar 𝔼.∘ h 𝔼.~ cov-pb 𝔼.∘ k) → F.ₐ (sp.a2 ℂ.∘ wkpO1.wπ/₁) 𝔼.∘ k 𝔼.~ F.ₐ (sp.a2 ℂ.∘ wkpO1.wπ/₂) 𝔼.∘ k
                        univ-pf {C} {h} {k} pf = ~proof
                                F.ₐ (sp.a2 ℂ.∘ wkpO1.wπ/₁) 𝔼.∘ k             ~[ ∘e r (F.∘ax-rfˢ ⊙ ∘e (kpFO1.×/tr₁ cov-pb-pf ˢ) r ⊙ ass) ⊙ assˢ ] /
                                (F.ₐ sp.a2 𝔼.∘ kpFO1.π/₁) 𝔼.∘ cov-pb 𝔼.∘ k    ~[ ∘e (pf ˢ) r ⊙ ass ⊙ ∘e r eqlFO2.eqleq ⊙ assˢ ⊙ ∘e pf r ] /
                                (F.ₐ sp.a2 𝔼.∘ kpFO1.π/₂) 𝔼.∘ cov-pb 𝔼.∘ k    ~[ ass ⊙ ∘e r (assˢ ⊙ ∘e (kpFO1.×/tr₂ cov-pb-pf) r ⊙ F.∘ax-rf) ]∎
                                F.ₐ (sp.a2 ℂ.∘ wkpO1.wπ/₂) 𝔼.∘ k ∎


      med-ar-repi : 𝔼.is-regular-epi med-ar
      med-ar-repi = pres-rl med-ar-pbsq cov-pb-repi
                  where open 𝔼.is-pbsq-stable reg𝔼.repi-are-pb-stb


      cov-bow : || 𝔼.Hom (F.ₒ weqlO2.wEql) eqlFO2.Eql ||
      cov-bow = med-ar 𝔼.∘ cov-eql

      cov-bow-repi : 𝔼.is-regular-epi cov-bow
      cov-bow-repi = reg𝔼.repi-cmp-r cov-eql-repi med-ar-repi

      bow-π₁ bow-π₂ : || 𝔼.Hom eqlFO2.Eql (F.ₒ sp.O12) ||
      bow-π₁ = kpFO1.π/₁ 𝔼.∘ eqlFO2.eqlar
      bow-π₂ = kpFO1.π/₂ 𝔼.∘ eqlFO2.eqlar

      bow-πs-are-eq : bow-π₁ 𝔼.~ bow-π₂
      bow-πs-are-eq = cbw.epi-pf (~proof
                    (kpFO1.π/₁ 𝔼.∘ eqlFO2.eqlar) 𝔼.∘ med-ar 𝔼.∘ cov-eql    ~[ ass ⊙ ∘e r (assˢ ⊙ ∘e med-ar-sqpf r ⊙ ass) ⊙ assˢ ] /
                    (kpFO1.π/₁ 𝔼.∘ cov-pb) 𝔼.∘ eqlO2.eqlar 𝔼.∘ cov-eql     ~[ ∘e (eqlO2.eqltr cov-eql-pf) (kpFO1.×/tr₁ cov-pb-pf) ] /
                    F.ₐ wkpO1.wπ/₁ 𝔼.∘ F.ₐ weqlO2.weqlar                   ~[ F.∘∘ wbow-πs-are-eq ] /
                    F.ₐ wkpO1.wπ/₂ 𝔼.∘ F.ₐ weqlO2.weqlar                   ~[ ∘e (eqlO2.eqltr cov-eql-pf ˢ) (kpFO1.×/tr₂ cov-pb-pf ˢ) ] /
                    (kpFO1.π/₂ 𝔼.∘ cov-pb) 𝔼.∘ eqlO2.eqlar 𝔼.∘ cov-eql     ~[ ass ⊙ ∘e r (assˢ ⊙ ∘e (med-ar-sqpf ˢ) r ⊙ ass) ⊙ assˢ ]∎
                    bow-π₂ 𝔼.∘ cov-bow ∎)
                    where module cbw = 𝔼.is-regular-epi cov-bow-repi
                          --open 𝔼.is-epic coeq-uniq
                          open ecategory-aux-only 𝔼


      private
        module Fsp = 𝔼.span/ (F.span/ sp/)

      Fsp-is-jm/ : 𝔼.is-jointly-monic/ (F.span/ sp/)
      Fsp-is-jm/ = 𝔼.jm/-via-pb+eq reg𝔼.×/of (eql𝔼.eql-of (Fsp.a2 𝔼.∘ reg𝔼.π/₁) (Fsp.a2 𝔼.∘ reg𝔼.π/₂)) bow-πs-are-eq
      
    -- end pres-jointly-monic


    pres-jm/ : preserves-jointly-monic/ F
    pres-jm/ = record
             { pres-jm/-pf = Fsp-is-jm/
             }
             where open pres-jointly-monic

  -- end lc-eql-pb2pres-jm
-}
