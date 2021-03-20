
-- disable the K axiom:

{-# OPTIONS --without-K  #-}

-- Agda version 2.5.4.1

module ecats.exact-completion.CVconstr-is-excompl.embedding.universal-property.is-left-covering where

open import ecats.basic-defs.ecat-def&not
open import ecats.basic-defs.commut-shapes
open import ecats.basic-defs.all-arrows
open import ecats.basic-props.epi&mono
open import ecats.basic-defs.regular-ecat
open import ecats.basic-defs.exact-ecat
open import ecats.basic-props.exact-ecat
open import ecats.finite-limits.all
open import ecats.functors.defs.efunctor-d&n
open import ecats.functors.defs.basic-defs
open import ecats.functors.defs.left-covering
open import ecats.functors.props.left-covering
open import ecats.constructions.ecat-eqrel
open import ecats.exact-completion.CVconstruction
open import ecats.exact-completion.CVconstr-is-excompl.finite-limits.fin-limits
open import ecats.exact-completion.CVconstr-is-excompl.embedding.universal-property.def



module exact-compl-universal-is-left-cov {ℂ : ecategory} (hasfwl : has-fin-weak-limits ℂ) where
  private
    module ℂ where
      open ecategory ℂ public
      open comm-shapes ℂ public
      open pseudo-eq-rel-defs ℂ public
      open finite-weak-limits ℂ public
    module fwlℂ where
      open has-fin-weak-limits hasfwl public
      open has-weak-pullbacks haswpb using (wpb-of) public
      open has-weak-Wlimits (has-wpb⇒has-wWlim haswpb) using (wW-of) public
    module Exℂ where
      open ecategory Ex ℂ [ hasfwl ] public
      open comm-shapes Ex ℂ [ hasfwl ] public
      open iso-defs Ex ℂ [ hasfwl ] public
      open epis&monos-defs Ex ℂ [ hasfwl ] public
      open epis&monos-props Ex ℂ [ hasfwl ] public
      open finite-weak-limits Ex ℂ [ hasfwl ] public
      open finite-limits Ex ℂ [ hasfwl ] public
      open limits→weak-limits Ex ℂ [ hasfwl ] public
    module flExℂ where
      open has-fin-limits (exact-compl-has-fin-limits hasfwl) public
      open has-terminal hastrm public
      open has-bin-products hasprd public
    module CVex = efunctor-aux CVex ℂ [ hasfwl ]
  open exact-compl-universal-def hasfwl

  module extension-is-left-cov {𝔼 : ecategory} (ex𝔼 : is-exact 𝔼)
                               {F : efunctor ℂ 𝔼} (lcovF : is-left-covering F)
                               where
    private
      module 𝔼 where
        open ecategory 𝔼 public
        open comm-shapes 𝔼 public
        open iso-defs 𝔼 public
        open epis&monos-defs 𝔼 public
        open epis&monos-props 𝔼 public
        open eq-rel-defs 𝔼 public
        open kernel-pairs-defs 𝔼 public
        open finite-limits-d&p 𝔼 public
        open relations-among-limit-diagrams 𝔼 public
      module ex𝔼 where
        open exact-cat-d&p ex𝔼 public
        open has-terminal hastrm public
        open has-bin-products hasprd using (prd-of) public
        open has-equalisers haseql using (eql-of) public
        open has-pullbacks haspb using (pb-of) public
        --open has-bows hasbw using (bw-of) public
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
      Q/F↑ex : (A : Exℂ.Obj) → 𝔼.coeq-of {FRel.relOb A} {FRel.baseOb A} (FRel.r₁ A) (FRel.r₂ A)
      Q/F↑ex A = ex𝔼.eqr-has-coeq (FRel.eqrelover A)
      module Q/F↑ex (A : Exℂ.Obj) where
        open 𝔼.coeq-of (Q/F↑ex A) public
        repi : 𝔼.is-regular-epi {FRel.baseOb A} {Ob} ar
        repi = record { coeq = iscoeq }
        open 𝔼.is-exact-seq (ex𝔼.ex-seq (FRel.eqrelover A))
        module kp = 𝔼.pullback-of-not (𝔼.mkpb-of iskerpair)



    module F↑ex-lcov-terminal {wT : Exℂ.Obj} (wTpf : Exℂ.is-wterminal wT)
                              {T : 𝔼.Obj} (Tpf : 𝔼.is-terminal T)
                              (cov! : || 𝔼.Hom (F↑ex.ₒ wT) T ||)
                              where
      T' : Exℂ.Obj
      T' = flExℂ.trmOb
      T'pf : Exℂ.is-terminal T'
      T'pf = flExℂ.istrm
      private
        module wT where
          open ℂ.peq wT public
          open Exℂ.is-wterminal wTpf public
        module T' where
          open ℂ.peq T' public
          open Exℂ.is-terminal T'pf public
        module T =  𝔼.is-terminal Tpf
      -- Lo of the chosen terminal in Exℂ is weakly terminal in ℂ
      T'Lopf : ℂ.is-wterminal T'.Lo
      T'Lopf = iswtrm
             where open has-fin-weak-limits hasfwl
                   open has-weak-terminal haswtrm
      covT : || 𝔼.Hom (F.ₒ T'.Lo) T ||
      covT = T.! (F.ₒ T'.Lo)
      covT-repi : 𝔼.is-regular-epi covT
      covT-repi = lcF.trmuniv-is-repi T'Lopf Tpf covT

      medEx : || Exℂ.Hom T' wT ||
      medEx = wT.w! T'
      med : || 𝔼.Hom (F.ₒ T'.Lo) (F↑ex.ₒ wT) ||
      med = F↑ex.ₐ {T'} {wT} medEx 𝔼.∘ Q/F↑ex.ar T'

      cov-tr : cov! 𝔼.∘ med 𝔼.~ covT
      cov-tr = T.!uniq (cov! 𝔼.∘ med)      
      cov!-repi : 𝔼.is-regular-epi cov!
      cov!-repi = ex𝔼.repi-triang cov-tr covT-repi
    -- end F↑ex-lcov-terminal

    F↑ex-is-left-covering-trm : is-left-covering-trm F↑ex
    F↑ex-is-left-covering-trm = record
      { trmuniv-is-repi = cov!-repi
      }
      where open F↑ex-lcov-terminal



    module F↑ex-lcov-bin-products {A B wP : Exℂ.Obj} {wp₁ : || Exℂ.Hom wP A ||} {wp₂ : || Exℂ.Hom wP B ||}
                                  (wPpf : Exℂ.is-wproduct (Exℂ.mkspan wp₁ wp₂))
                                  {P : 𝔼.Obj} {p₁ : || 𝔼.Hom P (F↑ex.ₒ A) ||} {p₂ : || 𝔼.Hom P (F↑ex.ₒ B) ||}
                                  (Ppf : 𝔼.is-product (𝔼.mkspan p₁ p₂))
                                  {cov× : || 𝔼.Hom (F↑ex.ₒ wP) P ||}
                                  (pf₁ : p₁ 𝔼.∘ cov× 𝔼.~ F↑ex.ₐ {wP} {A} wp₁)
                                  (pf₂ : p₂ 𝔼.∘ cov× 𝔼.~ F↑ex.ₐ {wP} {B} wp₂)
                                  where
      A×B : Exℂ.product-of A B
      A×B = flExℂ.prd-of A B
      private
        module A = ℂ.peq A
        module B = ℂ.peq B
        module wP where
          open ℂ.peq wP public
          open Exℂ.wproduct-of-not (Exℂ.mkw×of wPpf) public
        module A×B where
          open Exℂ.product-of-not A×B public
          module Ob = ℂ.peq O12
          module π₁ = ℂ.peq-mor π₁
          module π₂ = ℂ.peq-mor π₂
        module P = 𝔼.product-of-not (𝔼.mk×of Ppf)

      Lo[A×B] : ℂ.is-wproduct (ℂ.mkspan A×B.π₁.lo A×B.π₂.lo)
      Lo[A×B] = iswprd
              where open has-fin-weak-limits hasfwl
                    open has-bin-weak-products haswprd using (wprd-of)
                    open ℂ.wproduct-of (wprd-of A.Lo B.Lo)
      FLoA×FLoB : 𝔼.product-of (F.ₒ A.Lo) (F.ₒ B.Lo)
      FLoA×FLoB = ex𝔼.prd-of (F.ₒ A.Lo) (F.ₒ B.Lo)
      private
        module Lo[A×B] = ℂ.wproduct-of-not (ℂ.mkw×of Lo[A×B])
        module FLoA×FLoB = 𝔼.product-of-not FLoA×FLoB
        module QA×QB = ex𝔼.sides-cover-so-pb-covers (𝔼.mkpb-of (𝔼.×is-pb-on! ex𝔼.istrm Ppf))
                                                     (𝔼.mkpb-of (𝔼.×is-pb-on! ex𝔼.istrm FLoA×FLoB.×isprd))
                                                     (ex𝔼.!uniq (ex𝔼.! (F↑ex.ₒ A) 𝔼.∘ Q/F↑ex.ar A))
                                                     (ex𝔼.!uniq (ex𝔼.! (F↑ex.ₒ B) 𝔼.∘ Q/F↑ex.ar B))
                                                     (Q/F↑ex.repi A)
                                                     (Q/F↑ex.repi B)
      covFLo : || 𝔼.Hom (F.ₒ Lo[A×B].O12) FLoA×FLoB.O12 ||
      covFLo = FLoA×FLoB.< F.ₐ A×B.π₁.lo , F.ₐ A×B.π₂.lo >
      covFLo-repi : 𝔼.is-regular-epi covFLo
      covFLo-repi = lcF.prduniv-is-repi (ℂ.mkw×of Lo[A×B]) FLoA×FLoB FLoA×FLoB.×tr₁ FLoA×FLoB.×tr₂
      covP : || 𝔼.Hom (F.ₒ Lo[A×B].O12) P ||
      covP = QA×QB.diag 𝔼.∘ covFLo
      covP-repi : 𝔼.is-regular-epi covP
      covP-repi = ∘c QA×QB.covpb.is-repi covFLo-repi
                where open is-ecat-congr ex𝔼.regular-epi-is-congr

      medEx : || Exℂ.Hom A×B.O12 wP ||
      medEx = wP.w< A×B.π₁ , A×B.π₂ >
      F[A×B] : 𝔼.Obj
      F[A×B] = F↑ex.ₒ A×B.O12
      F↑medEx : || 𝔼.Hom F[A×B] (F↑ex.ₒ wP) ||
      F↑medEx = F↑ex.ₐ {A×B.O12} {wP} medEx
      med : || 𝔼.Hom (F.ₒ Lo[A×B].O12) (F↑ex.ₒ wP) ||
      med = F↑medEx 𝔼.∘ Q/F↑ex.ar A×B.O12

      cov-tr : cov× 𝔼.∘ med 𝔼.~ covP
      cov-tr = P.×uq
        (~proof p₁ 𝔼.∘ cov× 𝔼.∘ med                       ~[ ass ⊙ ∘e r pf₁ ] /
                F↑ex.ₐ {wP} {A} wp₁ 𝔼.∘ med                ~[ ass ⊙ ∘e r (F↑ex.∘ax {A×B.O12} {wP} {A}
                                                              {f = medEx} {wp₁} {A×B.π₁} wP.w×tr₁) ] /
                F↑ex.ₐ {A×B.O12} {A} A×B.π₁ 𝔼.∘ Q/F↑ex.ar A×B.O12       ~[ q-sq (FRel.ₐ A×B.π₁) ] /
                Q/F↑ex.ar A 𝔼.∘ F.ₐ A×B.π₁.lo              ~[ ∘e (FLoA×FLoB.×tr₁ˢ {g = F.ₐ A×B.π₂.lo}) r ] /
                Q/F↑ex.ar A 𝔼.∘ FLoA×FLoB.π₁ 𝔼.∘ covFLo   ~[ ass ⊙ ∘e r (P.×tr₁ˢ {g = Q/F↑ex.ar B 𝔼.∘ FLoA×FLoB.π₂}) ⊙ assˢ ]∎
                p₁ 𝔼.∘ QA×QB.diag 𝔼.∘ covFLo ∎)
        (~proof p₂ 𝔼.∘ cov× 𝔼.∘ med                       ~[ ass ⊙ ∘e r pf₂ ] /
                F↑ex.ₐ {wP} {B} wp₂ 𝔼.∘ med                ~[ ass ⊙ ∘e r (F↑ex.∘ax {A×B.O12} {wP} {B}
                                                              {f = medEx} {wp₂} {A×B.π₂} wP.w×tr₂) ] /
                F↑ex.ₐ {A×B.O12} {B} A×B.π₂ 𝔼.∘ Q/F↑ex.ar A×B.O12        ~[ q-sq (FRel.ₐ A×B.π₂) ] /
                Q/F↑ex.ar B 𝔼.∘ F.ₐ A×B.π₂.lo              ~[ ∘e (FLoA×FLoB.×tr₂ˢ {g = F.ₐ A×B.π₂.lo}) r ] /
                Q/F↑ex.ar B 𝔼.∘ FLoA×FLoB.π₂ 𝔼.∘ covFLo   ~[ ass ⊙ ∘e r (P.×tr₂ˢ {g = Q/F↑ex.ar B 𝔼.∘ FLoA×FLoB.π₂}) ⊙ assˢ ]∎
                p₂ 𝔼.∘ QA×QB.diag 𝔼.∘ covFLo ∎)
        where open ecategory-aux-only 𝔼
              open quot-of-eqrel-funct ex𝔼 using (q-sq)
      cov×-repi : 𝔼.is-regular-epi cov×
      cov×-repi = ex𝔼.repi-triang cov-tr covP-repi
    -- end F↑ex-lcov-bin-products


    F↑ex-is-left-covering-isprd : is-left-covering-isprd F↑ex
    F↑ex-is-left-covering-isprd = record
      { prduniv-is-repi = λ iswprd prdof pf₁ pf₂ → cov×-repi iswprd (×isprd prdof) pf₁ pf₂
      }
      where open F↑ex-lcov-bin-products
            open 𝔼.product-of

    F↑ex-is-left-covering-prd : is-left-covering-prd F↑ex
    F↑ex-is-left-covering-prd = lc-isprd2lc-prd F↑ex-is-left-covering-isprd



    module F↑ex-lcov-equalisers  {A B : Exℂ.Obj} {f g : || Exℂ.Hom A B ||}
                                 {wE : Exℂ.Obj} {we : || Exℂ.Hom wE A ||} {wEsqpf : f Exℂ.∘ we Exℂ.~ g Exℂ.∘ we}
                                 (wEpf : Exℂ.is-wequaliser {e = we} wEsqpf)
                                 {E : 𝔼.Obj} {e : || 𝔼.Hom E (F↑ex.ₒ A) ||} {Esqpf : F↑ex.ₐ f 𝔼.∘ e 𝔼.~ F↑ex.ₐ g 𝔼.∘ e}
                                 (Epf : 𝔼.is-equaliser {e = e} Esqpf)
                                 {coveql : || 𝔼.Hom (F↑ex.ₒ wE) E ||} (trpf : e 𝔼.∘ coveql 𝔼.~ F↑ex.ₐ {wE} {A} we)
                                 where
      private
        module A = ℂ.peq A
        module B = ℂ.peq B
        module f = ℂ.peq-mor f
        module g = ℂ.peq-mor g
        module wE where
          open Exℂ.is-wequaliser wEpf public
          module Ob = ℂ.peq wE
          module we = ℂ.peq-mor we
        module Efg where
          open exact-compl-has-equalisers hasfwl
          open ExC-eql-of f g using (eqlLo; eql-of) renaming (sp-lof to sp-lofg) public
          module eql = Exℂ.equaliser-of eql-of
          module wbw = ℂ.wbow-of eqlLo
        module E = 𝔼.is-equaliser Epf
        module CRFB where
          open eqrel-from-peq-via-left-covering reg𝔼 lcovF
          open eqrel-as-repi-mono-fact B public
          open rmfF% using (C; C-is-repi) public
      RFB₁ RFB₂ : || 𝔼.Hom (FRel.relOb B) (FRel.baseOb B) ||
      RFB₁ = FRel.r₁ B
      RFB₂ = FRel.r₂ B
      CFB : || 𝔼.Hom (F.ₒ B.Hi) (FRel.relOb B) ||
      CFB = CRFB.C
      -- the following two take long to typecheck
      CFB-tr₁ : RFB₁ 𝔼.∘ CFB 𝔼.~ F.ₐ B.%0
      CFB-tr₁ = CRFB.rmfF%tr₁
      CFB-tr₂ : RFB₂ 𝔼.∘ CFB 𝔼.~ F.ₐ B.%1
      CFB-tr₂ = CRFB.rmfF%tr₂
      private
        module Q/F↑B where
          open Q/F↑ex B public
          FQ/ : 𝔼.is-coeq (F.ₐ B.%0) (F.ₐ B.%1) ar
          FQ/ = 𝔼.epi/coeq-so-coeq (𝔼.repi-is-epic CRFB.C-is-repi)
                                    CFB-tr₁
                                    CFB-tr₂
                                    iscoeq
          module FQ/ = 𝔼.is-coeq FQ/
      -- Take pb P,p1,p2 of Q/F↑A along e,
      -- so p1 is repi and there is a1 : P --> FRel.ₒ B;
      -- take pb P',p'1,p'2 of CFB along a1, so p'1 is repi;
      -- then P',p2∘p'1,p'2 is bow limit of Fsp-lofg and FspB.
      
      covE1-pb : 𝔼.pullback-of e (Q/F↑ex.ar A)
      covE1-pb = ex𝔼.pb-of e (Q/F↑ex.ar A)
      private
        module covE1 where
          open 𝔼.pullback-of-not covE1-pb public
          mono : 𝔼.is-monic π/₂
          mono = pres-du covE1-pb (record { mono-pf = E.eqluq })
               where open 𝔼.is-pbof-stable 𝔼.mono-pbof-stb
          repi : 𝔼.is-regular-epi π/₁
          repi = pres-rl covE1-pb (Q/F↑ex.repi A)
               where open 𝔼.is-pbof-stable ex𝔼.repi-pbof-stable
      bwπ-pf : Q/F↑B.ar 𝔼.∘ F.ₐ f.lo 𝔼.∘ covE1.π/₂ 𝔼.~ Q/F↑B.ar 𝔼.∘ F.ₐ g.lo 𝔼.∘ covE1.π/₂
      bwπ-pf = ~proof Q/F↑B.ar 𝔼.∘ F.ₐ f.lo 𝔼.∘ covE1.π/₂       ~[ ass ⊙ ∘e r (q-sq (FRel.ₐ f) ˢ) ⊙ assˢ ] /
                      F↑ex.ₐ {A} {B} f 𝔼.∘ Q/F↑ex.ar A 𝔼.∘ covE1.π/₂    ~[ ∘e (covE1.×/sqpf ˢ) r ] /
                      F↑ex.ₐ {A} {B} f 𝔼.∘ e 𝔼.∘ covE1.π/₁              ~[ ass ⊙ ∘e r Esqpf ⊙ assˢ ] / 
                      F↑ex.ₐ {A} {B} g 𝔼.∘ e 𝔼.∘ covE1.π/₁              ~[ ∘e covE1.×/sqpf r ] /
                      F↑ex.ₐ {A} {B} g 𝔼.∘ Q/F↑ex.ar A 𝔼.∘ covE1.π/₂    ~[ ass ⊙ ∘e r (q-sq (FRel.ₐ g)) ⊙ assˢ ]∎
                      Q/F↑B.ar 𝔼.∘ F.ₐ g.lo 𝔼.∘ covE1.π/₂ ∎
             where open ecategory-aux-only 𝔼
                   open quot-of-eqrel-funct ex𝔼 using (q-sq)
      bwπ : || 𝔼.Hom covE1.ul (FRel.relOb B) ||
      bwπ = Q/F↑B.kp.⟨ F.ₐ f.lo 𝔼.∘ covE1.π/₂ , F.ₐ g.lo 𝔼.∘ covE1.π/₂ ⟩[ bwπ-pf ]
      bwπ-tr₁ : RFB₁ 𝔼.∘ bwπ 𝔼.~ F.ₐ f.lo 𝔼.∘ covE1.π/₂
      bwπ-tr₁ = Q/F↑B.kp.×/tr₁ {covE1.ul} {F.ₐ f.lo 𝔼.∘ covE1.π/₂} {F.ₐ g.lo 𝔼.∘ covE1.π/₂} bwπ-pf
      bwπ-tr₂ : RFB₂ 𝔼.∘ bwπ 𝔼.~ F.ₐ g.lo 𝔼.∘ covE1.π/₂
      bwπ-tr₂ = Q/F↑B.kp.×/tr₂ {covE1.ul} {F.ₐ f.lo 𝔼.∘ covE1.π/₂} {F.ₐ g.lo 𝔼.∘ covE1.π/₂} bwπ-pf
      
      covE2-pb : 𝔼.pullback-of bwπ CFB
      covE2-pb = ex𝔼.pb-of bwπ CFB
      private
        module covE2 where
          open 𝔼.pullback-of-not covE2-pb public
          repi : 𝔼.is-regular-epi π/₁
          repi = pres-rl covE2-pb CRFB.C-is-repi
               where open 𝔼.is-pbof-stable ex𝔼.repi-pbof-stable

      private
        module proving-is-bow where
          open ecategory-aux-only 𝔼
          sqpf₁ : F.ₐ f.lo 𝔼.∘ covE1.π/₂ 𝔼.∘ covE2.π/₁ 𝔼.~ F.ₐ B.%0 𝔼.∘ covE2.π/₂
          sqpf₁ = ~proof F.ₐ f.lo 𝔼.∘ covE1.π/₂ 𝔼.∘ covE2.π/₁
                     ~[ ass ⊙ ∘e r (bwπ-tr₁ ˢ) ⊙ assˢ  ] /
                         RFB₁ 𝔼.∘ bwπ 𝔼.∘ covE2.π/₁
                     ~[ ∘e covE2.×/sqpf r ] / -- 
                         RFB₁ 𝔼.∘ CFB 𝔼.∘ covE2.π/₂
                     ~[ ass ⊙ ∘e r CFB-tr₁ ]∎
                         F.ₐ B.%0 𝔼.∘ covE2.π/₂ ∎
          sqpf₂ : F.ₐ g.lo 𝔼.∘ covE1.π/₂ 𝔼.∘ covE2.π/₁ 𝔼.~ F.ₐ B.%1 𝔼.∘ covE2.π/₂
          sqpf₂ = ~proof F.ₐ g.lo 𝔼.∘ covE1.π/₂ 𝔼.∘ covE2.π/₁
                      ~[ ass ⊙ ∘e r (bwπ-tr₂ ˢ) ⊙ assˢ ] /
                         RFB₂ 𝔼.∘ bwπ 𝔼.∘ covE2.π/₁
                      ~[ ∘e covE2.×/sqpf r ] /
                         RFB₂ 𝔼.∘ CFB 𝔼.∘ covE2.π/₂
                      ~[ ass ⊙ ∘e r CFB-tr₂ ]∎
                         F.ₐ B.%1 𝔼.∘ covE2.π/₂ ∎
          module bwuniv {D : 𝔼.Obj} {k : || 𝔼.Hom D (F.ₒ A.Lo) ||} {h : || 𝔼.Hom D (F.ₒ B.Hi) ||}
                        (pf₁ : F.ₐ f.lo 𝔼.∘ k 𝔼.~ F.ₐ B.%0 𝔼.∘ h) (pf₂ : F.ₐ g.lo 𝔼.∘ k 𝔼.~ F.ₐ B.%1 𝔼.∘ h)
                        where
            open quot-of-eqrel-funct ex𝔼 using (q-sq)
            unE-pf : F↑ex.ₐ f 𝔼.∘ Q/F↑ex.ar A 𝔼.∘ k 𝔼.~ F↑ex.ₐ g 𝔼.∘ Q/F↑ex.ar A 𝔼.∘ k
            unE-pf = ~proof
              F↑ex.ₐ f 𝔼.∘ Q/F↑ex.ar A 𝔼.∘ k   ~[ ass ⊙ ∘e r (q-sq (FRel.ₐ f)) ⊙ assˢ  ] /
              Q/F↑B.ar 𝔼.∘ F.ₐ f.lo 𝔼.∘ k      ~[ ∘e pf₁ r ] /
              Q/F↑B.ar 𝔼.∘ F.ₐ B.%0 𝔼.∘ h      ~[ ass ⊙ ∘e r Q/F↑B.FQ/.eq ⊙ assˢ ] /
              Q/F↑B.ar 𝔼.∘ F.ₐ B.%1 𝔼.∘ h      ~[ ∘e (pf₂ ˢ) r ] /
              Q/F↑B.ar 𝔼.∘ F.ₐ g.lo 𝔼.∘ k      ~[ ass ⊙ ∘e r (q-sq (FRel.ₐ g) ˢ) ⊙ assˢ ]∎
              F↑ex.ₐ g 𝔼.∘ Q/F↑ex.ar A 𝔼.∘ k ∎
            unE : || 𝔼.Hom D E ||
            unE = (Q/F↑ex.ar A 𝔼.∘ k) E.|eql[ unE-pf ]
            un-pfl :  e 𝔼.∘ unE 𝔼.~ Q/F↑ex.ar A 𝔼.∘ k
            un-pfl = E.eqltr unE-pf
            unl : || 𝔼.Hom D covE1.ul ||
            unl = covE1.⟨ unE , k ⟩[ un-pfl ]
            un-pfr : bwπ 𝔼.∘ unl 𝔼.~ CFB 𝔼.∘ h
            un-pfr = FRel.jm-pf B {D} {bwπ 𝔼.∘ unl} {CFB 𝔼.∘ h}
            -- takes a while
              (~proof RFB₁ 𝔼.∘ bwπ 𝔼.∘ unl
                  ~[ ass ⊙ ∘e r bwπ-tr₁ ⊙ assˢ ] /
                      F.ₐ f.lo 𝔼.∘ covE1.π/₂ 𝔼.∘ unl
                  ~[ ∘e (covE1.×/tr₂ un-pfl) r ] /
                      F.ₐ f.lo 𝔼.∘ k
                  ~[ pf₁ ⊙ ∘e r (CFB-tr₁ ˢ) ⊙ assˢ ]∎
                      RFB₁ 𝔼.∘ CFB 𝔼.∘ h ∎)
              (~proof RFB₂ 𝔼.∘ bwπ 𝔼.∘ covE1.⟨ unE , k ⟩[ un-pfl ]
                  ~[ ass ⊙ ∘e r bwπ-tr₂ ⊙ assˢ ] / --
                      F.ₐ g.lo 𝔼.∘ covE1.π/₂ 𝔼.∘ covE1.⟨ unE , k ⟩[ un-pfl ]
                  ~[ ∘e (covE1.×/tr₂ un-pfl) r ] /
                      F.ₐ g.lo 𝔼.∘ k
                  ~[ pf₂ ⊙ ∘e r (CFB-tr₂ ˢ) ⊙ assˢ ]∎
                      RFB₂ 𝔼.∘ CFB 𝔼.∘ h ∎)
            untr₁ : (covE1.π/₂ 𝔼.∘ covE2.π/₁) 𝔼.∘ covE2.⟨ unl , h ⟩[ un-pfr ]
                               𝔼.~ k
            untr₁ = assˢ ⊙ ∘e (covE2.×/tr₁ un-pfr) r ⊙ covE1.×/tr₂ un-pfl
            untr₂ : covE2.π/₂ 𝔼.∘ covE2.⟨ unl , h ⟩[ un-pfr ] 𝔼.~ h
            untr₂ = covE2.×/tr₂ un-pfr
          -- end bwuniv
        -- end proving-is-bow
      -- end private
      
      Flofg FB : 𝔼.span/ (F.ₒ B.Lo) (F.ₒ B.Lo)
      Flofg = F.span/ Efg.sp-lofg
      FB = F.span/ B.sp/
      Bw : 𝔼.bow-of Flofg FB
      Bw = record
        { sp = 𝔼.mkspan/ (covE1.π/₂ 𝔼.∘ covE2.π/₁) covE2.π/₂
        ; sqpf₁ = sqpf₁
        ; sqpf₂ = sqpf₂
        ; is-bw = record
          { ⟨_,_⟩[_,_] = λ k h pf₁ pf₂ →
                       covE2.⟨ unl pf₁ pf₂ , h ⟩[ un-pfr pf₁ pf₂ ]
          ; tr₁ = untr₁
          ; tr₂ = untr₂
          ; uq = unuq
          }
        }
        where open ecategory-aux-only 𝔼
              open quot-of-eqrel-funct ex𝔼 using (q-sq)
              open proving-is-bow
              open bwuniv
              unuq : {D : 𝔼.Obj} {h h' : || 𝔼.Hom D covE2.ul ||}
                     (pf₁ : (covE1.π/₂ 𝔼.∘ covE2.π/₁) 𝔼.∘ h 𝔼.~ (covE1.π/₂ 𝔼.∘ covE2.π/₁) 𝔼.∘ h')
                     (pf₂ : covE2.π/₂ 𝔼.∘ h 𝔼.~ covE2.π/₂ 𝔼.∘ h')
                       → h 𝔼.~ h'
              unuq {_} {h} {h'} pf₁ pf₂ = covE2.×/uq (mono-pf (ass ⊙ pf₁ ⊙ assˢ)) pf₂
                                        where open 𝔼.is-monic covE1.mono

      private module Bw = 𝔼.bow-of Bw
      covBw : || 𝔼.Hom (F.ₒ Efg.wbw.Ob) Bw.Ob ||
      covBw = Bw.⟨ F.ₐ Efg.wbw.wπ//₁ , F.ₐ Efg.wbw.wπ//₂ ⟩[ F.∘∘ Efg.wbw.sqpf₁ , F.∘∘ Efg.wbw.sqpf₂ ]
      covBw-pf₁ : Bw.π//₁ 𝔼.∘ covBw 𝔼.~ F.ₐ Efg.wbw.wπ//₁
      covBw-pf₁ = Bw.tr₁ {_} {F.ₐ Efg.wbw.wπ//₁} {F.ₐ Efg.wbw.wπ//₂} (F.∘∘ Efg.wbw.sqpf₁) (F.∘∘ Efg.wbw.sqpf₂)
      covBw-pf₂ : Bw.π//₂ 𝔼.∘ covBw 𝔼.~ F.ₐ Efg.wbw.wπ//₂
      covBw-pf₂ = Bw.tr₂ {_} {F.ₐ Efg.wbw.wπ//₁} {F.ₐ Efg.wbw.wπ//₂} (F.∘∘ Efg.wbw.sqpf₁) (F.∘∘ Efg.wbw.sqpf₂)
      covBw-repi : 𝔼.is-regular-epi covBw
      covBw-repi = lcF.bwuniv-is-repi Efg.eqlLo Bw covBw-pf₁ covBw-pf₂

      covE : || 𝔼.Hom (F.ₒ Efg.wbw.Ob) E ||
      covE = covE1.π/₁ 𝔼.∘ covE2.π/₁ 𝔼.∘ covBw
      covE-repi : 𝔼.is-regular-epi covE
      covE-repi = ∘c covE1.repi (∘c covE2.repi covBw-repi)
                where open is-ecat-congr ex𝔼.regular-epi-is-congr

      medEx : || Exℂ.Hom Efg.eql.Eql wE ||
      medEx = Efg.eql.eqlar wE.|weql[ Efg.eql.eqleq ]
      F↑Efg-ob : 𝔼.Obj
      F↑Efg-ob = F↑ex.ₒ Efg.eql.Eql
      F↑medEx : || 𝔼.Hom F↑Efg-ob (F↑ex.ₒ wE) ||
      F↑medEx = F↑ex.ₐ {Efg.eql.Eql} {wE} medEx
      med : || 𝔼.Hom (F.ₒ Efg.wbw.Ob) (F↑ex.ₒ wE) ||
      med = F↑medEx 𝔼.∘ Q/F↑ex.ar Efg.eql.Eql

      F↑we : || 𝔼.Hom (F↑ex.ₒ wE) (F↑ex.ₒ A) ||
      F↑we = F↑ex.ₐ {wE} {A} we
      F↑Efg-ar : || 𝔼.Hom F↑Efg-ob (F↑ex.ₒ A) ||
      F↑Efg-ar = F↑ex.ₐ {Efg.eql.Eql} {A} Efg.eql.eqlar
      cov-tr-aux : F↑we 𝔼.∘  F↑medEx 𝔼.~ F↑Efg-ar
      cov-tr-aux = F↑ex.∘ax {Efg.eql.Eql} {wE} {A} {medEx} {we} {Efg.eql.eqlar} (wE.weqltr Efg.eql.eqleq)
      cov-tr : coveql 𝔼.∘ med 𝔼.~ covE
      cov-tr = E.eqluq {F.ₒ Efg.wbw.Ob} {𝔼._∘_ coveql med} {covE} (~proof
        e 𝔼.∘ coveql 𝔼.∘ med                                ~[ ass ⊙ ∘e r trpf ] /
        F↑we 𝔼.∘ med                                         ~[ ass ⊙ ∘e r cov-tr-aux ] /
        F↑Efg-ar 𝔼.∘ Q/F↑ex.ar Efg.eql.Eql                   ~[ q-sq (FRel.ₐ Efg.eql.eqlar) ] /
        Q/F↑ex.ar A 𝔼.∘ F.ₐ Efg.wbw.wπ//₁                    ~[ ∘e (covBw-pf₁ ˢ ⊙ assˢ) r ] /
        Q/F↑ex.ar A 𝔼.∘ covE1.π/₂ 𝔼.∘ covE2.π/₁ 𝔼.∘ covBw   ~[ ass ⊙ ∘e r (covE1.×/sqpf ˢ) ⊙ assˢ ]∎
        e 𝔼.∘ covE ∎)
             where open ecategory-aux-only 𝔼
                   open quot-of-eqrel-funct ex𝔼 using (q-sq)
      coveql-repi : 𝔼.is-regular-epi coveql
      coveql-repi = ex𝔼.repi-triang cov-tr covE-repi
  -- end F↑ex-lcov-equalisers

    F↑ex-is-left-covering-iseql : is-left-covering-iseql F↑ex
    F↑ex-is-left-covering-iseql = record
      { eqluniv-is-repi = coveql-repi
      }
      where open F↑ex-lcov-equalisers
            open 𝔼.equaliser-of

    F↑ex-is-left-covering-eql : is-left-covering-eql F↑ex
    F↑ex-is-left-covering-eql = lc-iseql2lc-eql F↑ex-is-left-covering-iseql

    F↑ex-is-left-covering-pb : is-left-covering-pb F↑ex
    F↑ex-is-left-covering-pb = lcov-×+eql→lcov-×/ reg𝔼
                                                  (has-prd⇒has-wprd flExℂ.hasprd)
                                                  (has-eql⇒has-weql flExℂ.haseql)
                                                  F↑ex-is-left-covering-prd
                                                  F↑ex-is-left-covering-eql

    F↑ex-is-left-covering : is-left-covering F↑ex
    F↑ex-is-left-covering = record
      { lc! = F↑ex-is-left-covering-trm
      ; lc× = F↑ex-is-left-covering-prd
      ; lceql = F↑ex-is-left-covering-eql
      ; lc×/ = F↑ex-is-left-covering-pb
      ; lcbw = lcov-eql+pb→lcov-bw reg𝔼 (has-eql⇒has-weql flExℂ.haseql) (has-pb⇒has-wpb flExℂ.haspb)
                                    F↑ex-is-left-covering-eql F↑ex-is-left-covering-pb
      }
  -- end extension-is-left-cov



  ↑ex-is-left-covering : {𝔼 : ecategory} (ex𝔼 : is-exact 𝔼)
                         {F : efunctor ℂ 𝔼} (lcovF : is-left-covering F)
                           → is-left-covering (↑ex ex𝔼 lcovF)
  ↑ex-is-left-covering ex𝔼 lcovF = F↑ex-is-left-covering
                                  where open extension-is-left-cov ex𝔼 lcovF using (F↑ex-is-left-covering)
-- end exact-compl-universal-is-left-cov





{-
    module F↑ex-lcov-pullbacks {I A B wP : Exℂ.Obj} {a : || Exℂ.Hom A I ||} {b : || Exℂ.Hom B I ||}
                               {wp₁ : || Exℂ.Hom wP A ||} {wp₂ : || Exℂ.Hom wP B ||}
                               {wPsq : a Exℂ.∘ wp₁ Exℂ.~ b Exℂ.∘ wp₂}
                               (wPpf : Exℂ.is-wpb-square (Exℂ.mksq (Exℂ.mksq/ {A} {I} {B} wPsq)))
                               {P : 𝔼.Obj} {p₁ : || 𝔼.Hom P (F↑ex.ₒ A) ||} {p₂ : || 𝔼.Hom P (F↑ex.ₒ B) ||}
                               {Psq : (F↑ex.ₐ a) 𝔼.∘ p₁ 𝔼.~ (F↑ex.ₐ b) 𝔼.∘ p₂}
                               (Ppf : 𝔼.is-pb-square (𝔼.mksq (𝔼.mksq/ Psq)))
                               {cov×/ : || 𝔼.Hom (F↑ex.ₒ wP) P ||}
                               (pf₁ : p₁ 𝔼.∘ cov×/ 𝔼.~ F↑ex.ₐ wp₁) (pf₂ : p₂ 𝔼.∘ cov×/ 𝔼.~ F↑ex.ₐ wp₂)
                               where
      a×/b : Exℂ.pullback-of a b
      a×/b = flExℂ.pb-of {I} {A} {B} a b
      private
        module I = ℂ.peq I
        module A = ℂ.peq A
        module B = ℂ.peq B
        module a = ℂ.peq-mor a
        module b = ℂ.peq-mor b
        module wP where
          open Exℂ.wpullback-of-not (Exℂ.mkwpb-of wPpf) public
          module Ob = ℂ.peq wP
          module wπ/₁ = ℂ.peq-mor wπ/₁
          module wπ/₂ = ℂ.peq-mor wπ/₂
        module a×/b where
          open Exℂ.pullback-of-not a×/b public
          module Ob = ℂ.peq ul
          module π/₁ = ℂ.peq-mor π/₁
          module π/₂ = ℂ.peq-mor π/₂
        module P = 𝔼.pullback-of-not (𝔼.mkpb-of Ppf)

      Lo[a×/b] : ℂ.wWlim-of a.lo I.sp/ b.lo
      Lo[a×/b] = fwlℂ.wW-of a.lo I.sp/ b.lo
              --where open has-fin-weak-limits hasfwl
                --    open has-bin-weak-products haswprd using (wprd-of)
                  --  open ℂ.wproduct-of (wprd-of A.Lo B.Lo)
      Fa×/Fb : 𝔼.pullback-of (F.ₐ a.lo) (F.ₐ b.lo)
      Fa×/Fb = ex𝔼.pb-of (F.ₐ a.lo) (F.ₐ b.lo)
      private
        module Lo[a×/b] = ℂ.wWlim-of Lo[a×/b]
        module Fa×/Fb = 𝔼.pullback-of-not Fa×/Fb
      covFLo : || 𝔼.Hom (F.ₒ a×/b.Ob.Lo) Fa×/Fb.ul ||
      covFLo = Fa×/Fb.⟨ F.ₐ a×/b.π₁.lo , F.ₐ a×/b.π₂.lo ⟩[ ? ]
      covFLo-repi : 𝔼.is-regular-epi covFLo
      covFLo-repi = lcF.prduniv-is-repi (ℂ.mkw×of Lo[a×/b]) Fa×/Fb Fa×/Fb.×tr₁ Fa×/Fb.×tr₂
      QA×QB : || 𝔼.Hom Fa×/Fb.O12 P ||
      QA×QB = {!!}
            where open ex𝔼.pb-of-reg-covers-is-reg-cover-of-pb (𝔼.mkpb-of (𝔼.×is-pb-on! ex𝔼.istrm Ppf))
                                                                (𝔼.repi-is-reg-cov {!!})
                                                                {!!}

      medEx : || Exℂ.Hom a×/b.O12 wP ||
      medEx = wP.w< a×/b.π₁ , a×/b.π₂ >
      med : || 𝔼.Hom (F.ₒ Lo[a×/b].O12) (F↑ex.ₒ wP) ||
      med = F↑ex.ₐ {a×/b.O12} {wP} medEx 𝔼.∘ Q/F↑ex.ar a×/b.O12

      --covP-tr
    -- end F↑ex-lcov-pullbacks

    F↑ex-is-left-covering-pb : is-left-covering-pb F↑ex
    F↑ex-is-left-covering-pb = record
      { pbuniv-is-repi = {!!}
      }
      where open F↑ex-lcov-pullbacks
-}
