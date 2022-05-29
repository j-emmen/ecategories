
{-# OPTIONS --without-K #-}

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
open import ecats.functors.props.left-covering.left-covering-regular public
open import ecats.functors.props.left-covering.left-covering-basic public




-- Postcomposing a left covering functor with an exact functor yields a left covering functor

module exact+lcov-is-lcov {ℂ 𝔻 𝔼 : ecategory}(fl𝔻 : has-fin-limits 𝔻)
                          {F : efunctor ℂ 𝔻}{G : efunctor 𝔻 𝔼}
                          (lcovF : is-left-covering F)(exG : is-exact-functor G)
                          where
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
    module 𝔻 where
      open ecategory 𝔻 public
      open comm-shapes 𝔻 public
      open iso-defs 𝔻 public
      open epis&monos-defs 𝔻 public
      open epis&monos-props 𝔻 public
      open finite-limits-d&p 𝔻 public
      open finite-weak-limits-d&p 𝔻 public
      open limits→weak-limits 𝔻 public
      open relations-among-limit-diagrams 𝔻 public
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
    module fl𝔻 where
      open has-fin-limits fl𝔻 public
      open has-terminal hastrm public
      open has-bin-products hasprd using (prd-of) public
      open has-equalisers haseql using (eql-of) public
      open has-pullbacks haspb using (pb-of) public
      open has-bows hasbw using (bw-of) public
    module F where
      open efunctor-aux F public
      module lcov = is-left-covering lcovF
    module G where
      open efunctor-aux G public
      module ex = is-exact-functor exG
    module G○F = efunctor-aux (G ○ F)

  module cmp-lcov-trm {X : ℂ.Obj}(wtrmX : ℂ.is-wterminal X){TE : 𝔼.Obj}(trmTE : 𝔼.is-terminal TE)
                      (cov! : || 𝔼.Hom (G○F.ₒ X) TE ||)
                      where
    private
      module wT = ℂ.is-wterminal wtrmX
      TD : 𝔻.Obj
      TD = fl𝔻.trmOb
      module TD = 𝔻.is-terminal fl𝔻.istrm
      module TE = 𝔼.is-terminal trmTE
      module GTD = 𝔼.is-terminal (G.ex.pres-!-pf fl𝔻.istrm)
      covD-ar : || 𝔻.Hom (F.ₒ X) TD ||
      covD-ar = TD.! (F.ₒ X)
      covD : 𝔻.is-regular-epi covD-ar
      covD = F.lcov.trmuniv-is-repi wtrmX fl𝔻.istrm covD-ar
      GcovD : 𝔼.is-regular-epi (G.ₐ covD-ar)
      GcovD = G.ex.pres-repi-pf covD
      TE≅GTD : 𝔼.is-iso (TE.! (G.ₒ TD))
      TE≅GTD = 𝔼.mkis-iso (𝔼.!uq-isop (G.ex.pres-!-pf fl𝔻.istrm) trmTE)
      eq : TE.! (G.ₒ TD) 𝔼.∘ G.ₐ covD-ar 𝔼.~ cov!
      eq = TE.!uqg
    cov!-repi : 𝔼.is-regular-epi cov!
    cov!-repi = 𝔼.iso-to-repi-is-repi-cod TE≅GTD eq GcovD
  -- end cmp-lcov-trm

  module cmp-lcov-prd {X Y : ℂ.Obj}(wprdC : ℂ.wproduct-of X Y)
                      (prdE : 𝔼.product-of (G○F.ₒ X) (G○F.ₒ Y))
                      {covprd : || 𝔼.Hom (G○F.ₒ (ℂ.wproduct-of.O12 wprdC))
                                          (𝔼.product-of.O12 prdE) ||}
                      (tr₁ : 𝔼.product-of.π₁ prdE 𝔼.∘ covprd 𝔼.~ G○F.ₐ (ℂ.wproduct-of.wπ₁ wprdC))
                      (tr₂ : 𝔼.product-of.π₂ prdE 𝔼.∘ covprd 𝔼.~ G○F.ₐ (ℂ.wproduct-of.wπ₂ wprdC))
                      where
    private
      module wprdC = ℂ.wproduct-of wprdC
      prdD : 𝔻.product-of (F.ₒ X) (F.ₒ Y)
      prdD = fl𝔻.prd-of (F.ₒ X) (F.ₒ Y)
      module prdD = 𝔻.product-of prdD
      module prdE = 𝔼.product-of prdE
      GprdD : 𝔼.product-of (G○F.ₒ X) (G○F.ₒ Y)
      GprdD = 𝔼.mk×of (G.ex.pres-×-pf prdD.×isprd)
      module GprdD = 𝔼.product-of GprdD
      covD-ar : || 𝔻.Hom (F.ₒ wprdC.O12) prdD.O12 ||
      covD-ar = prdD.< F.ₐ wprdC.wπ₁ , F.ₐ wprdC.wπ₂ >
      covD : 𝔻.is-regular-epi covD-ar
      covD = F.lcov.prduniv-is-repi wprdC prdD prdD.×tr₁ prdD.×tr₂
      GcovD : 𝔼.is-regular-epi (G.ₐ covD-ar)
      GcovD = G.ex.pres-repi-pf covD
      med : || 𝔼.Hom (G.ₒ prdD.O12) prdE.O12 ||
      med = prdE.< G.ₐ prdD.π₁ , G.ₐ prdD.π₂ >
      E≅GD : 𝔼.is-iso med
      E≅GD = 𝔼.mkis-iso ×uq-iso-pair
           where open 𝔼.product-is-unique-uptoiso GprdD prdE
      isotr : med 𝔼.∘ G.ₐ covD-ar 𝔼.~ covprd
      isotr = prdE.×uq
        (~proof prdE.π₁ 𝔼.∘ med 𝔼.∘ G.ₐ covD-ar   ~[ ass ⊙ ∘e r prdE.×tr₁ ] /
                G.ₐ prdD.π₁ 𝔼.∘ G.ₐ covD-ar        ~[ G.∘ax prdD.×tr₁ ] /
                G○F.ₐ wprdC.wπ₁                    ~[ tr₁ ˢ ]∎
                prdE.π₁ 𝔼.∘ covprd ∎)
        (~proof prdE.π₂ 𝔼.∘ med 𝔼.∘ G.ₐ covD-ar   ~[ ass ⊙ ∘e r prdE.×tr₂ ] /
                G.ₐ prdD.π₂ 𝔼.∘ G.ₐ covD-ar        ~[ G.∘ax prdD.×tr₂ ] /
                G○F.ₐ wprdC.wπ₂                    ~[ tr₂ ˢ ]∎
                prdE.π₂ 𝔼.∘ covprd ∎)
        where open ecategory-aux-only 𝔼
    covprd-repi : 𝔼.is-regular-epi covprd
    covprd-repi = 𝔼.iso-to-repi-is-repi-cod E≅GD isotr GcovD    
  -- end cmp-lcov-prd

  module cmp-lcov-eql {X Y : ℂ.Obj}{f f' : || ℂ.Hom X Y ||}(weqlC : ℂ.wequaliser-of f f')
                      (eqlE : 𝔼.equaliser-of (G○F.ₐ f) (G○F.ₐ f'))
                      {coveql : || 𝔼.Hom (G○F.ₒ (ℂ.wequaliser-of.wEql weqlC))
                                          (𝔼.equaliser-of.Eql eqlE) ||}
                      (tr : 𝔼.equaliser-of.eqlar eqlE 𝔼.∘ coveql
                                     𝔼.~ G○F.ₐ (ℂ.wequaliser-of.weqlar weqlC))
                      where
    private
      module weqlC = ℂ.wequaliser-of weqlC
      eqlD : 𝔻.equaliser-of (F.ₐ f) (F.ₐ f')
      eqlD = fl𝔻.eql-of (F.ₐ f) (F.ₐ f')
      module eqlD = 𝔻.equaliser-of eqlD
      module eqlE = 𝔼.equaliser-of eqlE
      GeqlD : 𝔼.equaliser-of (G○F.ₐ f) (G○F.ₐ f')
      GeqlD = 𝔼.mkeql-of (G.ex.pres-eql-pf eqlD.iseql)
      module GeqlD = 𝔼.equaliser-of GeqlD
      covD-ar : || 𝔻.Hom (F.ₒ weqlC.wEql) eqlD.Eql ||
      covD-ar = F.ₐ weqlC.weqlar eqlD.|eql[ F.∘∘ weqlC.weqleq  ]
      covD : 𝔻.is-regular-epi covD-ar
      covD = F.lcov.eqluniv-is-repi weqlC eqlD (eqlD.eqltr (F.∘∘ weqlC.weqleq) )
      GcovD : 𝔼.is-regular-epi (G.ₐ covD-ar)
      GcovD = G.ex.pres-repi-pf covD
      med : || 𝔼.Hom (G.ₒ eqlD.Eql) eqlE.Eql ||
      med = G.ₐ eqlD.eqlar eqlE.|eql[ G.∘∘ eqlD.eqleq ]
      E≅GD : 𝔼.is-iso med
      E≅GD = 𝔼.eqls-unv-is-iso eqlE.iseql GeqlD.iseql {med} (eqlE.eqltr (G.∘∘ eqlD.eqleq))
      isotr : med 𝔼.∘ G.ₐ covD-ar 𝔼.~ coveql
      isotr = eqlE.eqluq (~proof
        eqlE.eqlar 𝔼.∘ med 𝔼.∘ G.ₐ covD-ar    ~[ ass ⊙ ∘e r (eqlE.eqltr (G.∘∘ eqlD.eqleq)) ] /
        G.ₐ eqlD.eqlar 𝔼.∘ G.ₐ covD-ar         ~[ G.∘ax (eqlD.eqltr (F.∘∘ weqlC.weqleq)) ] /
        G○F.ₐ weqlC.weqlar                      ~[ tr ˢ ]∎
        eqlE.eqlar 𝔼.∘ coveql ∎)
            where open ecategory-aux-only 𝔼
    coveql-repi : 𝔼.is-regular-epi coveql
    coveql-repi = 𝔼.iso-to-repi-is-repi-cod E≅GD isotr GcovD    
  -- end cmp-lcov-eql

  module cmp-lcov-pb {X Y Z : ℂ.Obj}{f : || ℂ.Hom X Z ||}{g : || ℂ.Hom Y Z ||}
                     (wpbC : ℂ.wpullback-of f g)(pbE : 𝔼.pullback-of (G○F.ₐ f) (G○F.ₐ g))
                     {covpb : || 𝔼.Hom (G○F.ₒ (ℂ.wpullback-of.ul wpbC)) (𝔼.pullback-of.ul pbE) ||}
                     (tr₁ : 𝔼.pullback-of.π/₁ pbE 𝔼.∘ covpb 𝔼.~ G○F.ₐ (ℂ.wpullback-of.wπ/₁ wpbC))
                     (tr₂ : 𝔼.pullback-of.π/₂ pbE 𝔼.∘ covpb 𝔼.~ G○F.ₐ (ℂ.wpullback-of.wπ/₂ wpbC))
                      where
    private
      module wpbC = ℂ.wpullback-of-not wpbC
      pbD : 𝔻.pullback-of (F.ₐ f) (F.ₐ g)
      pbD = fl𝔻.pb-of (F.ₐ f) (F.ₐ g)
      module pbD = 𝔻.pullback-of-not pbD
      module pbE = 𝔼.pullback-of-not pbE
      GpbD : 𝔼.pullback-of (G○F.ₐ f) (G○F.ₐ g)
      GpbD = 𝔼.pbof-is2sq (G.ex.pres-ispbof-pf (𝔻.pbof-sq2is pbD))
      module GpbD = 𝔼.pullback-of-not GpbD
      covD-ar : || 𝔻.Hom (F.ₒ wpbC.ul) pbD.ul ||
      covD-ar = pbD.⟨ F.ₐ wpbC.wπ/₁ , F.ₐ wpbC.wπ/₂ ⟩[ F.∘∘ wpbC.w×/sqpf ]
      covD : 𝔻.is-regular-epi covD-ar
      covD = F.lcov.pbuniv-is-repi wpbC pbD (pbD.×/tr₁ (F.∘∘ wpbC.w×/sqpf)) (pbD.×/tr₂ (F.∘∘ wpbC.w×/sqpf))
      GcovD : 𝔼.is-regular-epi (G.ₐ covD-ar)
      GcovD = G.ex.pres-repi-pf covD
      med : || 𝔼.Hom (G.ₒ pbD.ul) pbE.ul ||
      med = pbE.⟨ G.ₐ pbD.π/₁ , G.ₐ pbD.π/₂ ⟩[ G.∘∘ pbD.×/sqpf ]
      E≅GD : 𝔼.is-iso med
      E≅GD = 𝔼.pbs-unvar-is-iso GpbD pbE (pbE.×/tr₁ (G.∘∘ pbD.×/sqpf)) (pbE.×/tr₂ (G.∘∘ pbD.×/sqpf))
      isotr : med 𝔼.∘ G.ₐ covD-ar 𝔼.~ covpb
      isotr = pbE.×/uq
        (~proof pbE.π/₁ 𝔼.∘ med 𝔼.∘ G.ₐ covD-ar   ~[ ass ⊙ ∘e r (pbE.×/tr₁ (G.∘∘ pbD.×/sqpf)) ] /
                G.ₐ pbD.π/₁ 𝔼.∘ G.ₐ covD-ar        ~[ G.∘ax (pbD.×/tr₁ (F.∘∘ wpbC.w×/sqpf)) ] /
                G○F.ₐ wpbC.wπ/₁                    ~[ tr₁ ˢ ]∎
                pbE.π/₁ 𝔼.∘ covpb ∎)
        (~proof pbE.π/₂ 𝔼.∘ med 𝔼.∘ G.ₐ covD-ar   ~[ ass ⊙ ∘e r (pbE.×/tr₂ (G.∘∘ pbD.×/sqpf)) ] /
                G.ₐ pbD.π/₂ 𝔼.∘ G.ₐ covD-ar        ~[ G.∘ax (pbD.×/tr₂ (F.∘∘ wpbC.w×/sqpf)) ] /
                G○F.ₐ wpbC.wπ/₂                    ~[ tr₂ ˢ ]∎
                pbE.π/₂ 𝔼.∘ covpb ∎)
        where open ecategory-aux-only 𝔼
    covpb-repi : 𝔼.is-regular-epi covpb
    covpb-repi = 𝔼.iso-to-repi-is-repi-cod E≅GD isotr GcovD    
  -- end cmp-lcov-pb

  private
    cmplceql : is-left-covering-eql (G ○ F)
    cmplceql = record { eqluniv-is-repi = coveql-repi }
             where open cmp-lcov-eql
    cmplcpb : is-left-covering-pb (G ○ F)
    cmplcpb = record { pbuniv-is-repi = covpb-repi }
            where open cmp-lcov-pb  
  cmp-lcov :  has-weak-equalisers ℂ → has-weak-pullbacks ℂ → is-regular 𝔼
                                  → is-left-covering (G ○ F)
  cmp-lcov Cweql Cwpb reg𝔼 = record
    { lc! = record { trmuniv-is-repi = cov!-repi }
    ; lc× = record { prduniv-is-repi = covprd-repi }
    ; lceql = cmplceql
    ; lc×/ = cmplcpb
    ; lcbw = lcov-eql+pb→lcov-bw reg𝔼 Cweql Cwpb cmplceql cmplcpb
    }
    where open cmp-lcov-trm
          open cmp-lcov-prd
-- end exact+lcov-is-lcov

ex○lcov-is-lcov : {ℂ 𝔻 𝔼 : ecategory}(weqlℂ : has-weak-equalisers ℂ)(wpbℂ : has-weak-pullbacks ℂ)
                  (fl𝔻 : has-fin-limits 𝔻)(reg𝔼 : is-regular 𝔼){F : efunctor ℂ 𝔻}{G : efunctor 𝔻 𝔼}
                     → is-left-covering F → is-exact-functor G
                       → is-left-covering (G ○ F)
ex○lcov-is-lcov weqlℂ wpbℂ fl𝔻 reg𝔼 lcovF exG = cmp-lcov weqlℂ wpbℂ reg𝔼
                                                where open exact+lcov-is-lcov fl𝔻 lcovF exG
