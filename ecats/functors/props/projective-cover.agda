
-- disable the K axiom:

{-# OPTIONS --without-K #-}

-- Agda version 2.5.4.1

module ecats.functors.props.projective-cover where

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
open import ecats.functors.defs.projective-cover
open import ecats.functors.defs.left-covering
open import ecats.functors.props.left-covering


-- Properties of projective covers into finitely complete categories

module projective-cover-props {ℂ : ecategory} (hasfl : has-fin-limits ℂ)
                              {ℙ : ecategory} {PC : efunctor ℙ ℂ} (ispjcov : is-projective-cover PC)
                              where
  private
    module ℙ where
      open ecategory ℙ public
      open comm-shapes ℙ public
      open epis&monos-defs ℙ public
      open epis&monos-props ℙ public
      open kernel-pairs-defs ℙ public
      open finite-limits-d&p ℙ public
      open finite-weak-limits-d&p ℙ public
      open limits→weak-limits ℙ public
      --open relations-among-limit-diagrams ℙ public
    module ℂ where
      open ecategory ℂ public
      open comm-shapes ℂ public
      open iso-defs ℂ public
      open epis&monos-defs ℂ public
      open epis&monos-props ℂ public
      open kernel-pairs-defs ℂ public
      open eq-rel-defs ℂ public
      open finite-limits-d&p ℂ public
      open projective-defs ℂ public
    module flℂ where
      open has-fin-limits hasfl public
      open has-terminal hastrm public
      open has-bin-products hasprd using (prd-of) public
      open has-equalisers haseql using (eql-of) public
      open has-pullbacks haspb using (pb-of) public
      open has-bows hasbw using (bw-of) public
    module PC where
      open efunctor-aux PC public
      open is-projective-cover ispjcov public


  -- Covers of limits in ℂ are weak limits in ℙ

  module cover-of-terminal-is-weak-terminal {T : ℂ.Obj} (istrm : ℂ.is-terminal T) where
    private
      module T = ℂ.is-terminal istrm
    wT : ℙ.Obj
    wT = PC.rc.Ob T
    iswtrm : ℙ.is-wterminal wT
    iswtrm = record
             { w! = λ X → PC.full-ar (PC.rp.lift X (PC.rc.is-repi T) (T.! (PC.ₒ X)))
             }
  -- end cover-of-terminal-is-weak-terminal


  dom-has-weak-terminal : has-weak-terminal ℙ
  dom-has-weak-terminal = record
    { wtrmOb = wT
    ; iswtrm = iswtrm
    }
    where open cover-of-terminal-is-weak-terminal flℂ.istrm



  module cover-of-product-is-weak-product {X Y : ℙ.Obj} (prd : ℂ.product-of (PC.ₒ X) (PC.ₒ Y)) where
    private
      module PCX×PCY = ℂ.product-of-not prd
      module ×rc = PC.rc PCX×PCY.O12
      w×Ob : ℙ.Obj
      w×Ob = PC.rc.Ob PCX×PCY.O12
      wπ₁ : || ℙ.Hom w×Ob X ||
      wπ₁ = PC.full-ar (PCX×PCY.π₁ ℂ.∘ ×rc.ar)
      wπ₂ : || ℙ.Hom w×Ob Y ||
      wπ₂ = PC.full-ar (PCX×PCY.π₂ ℂ.∘ ×rc.ar)
      wun-aux : {Z : ℙ.Obj} (h : || ℙ.Hom Z X ||) (k : || ℙ.Hom Z Y ||) → || ℂ.Hom (PC.ₒ Z) (PC.ₒ w×Ob) ||
      wun-aux {Z} h k = PC.rp.lift Z ×rc.is-repi PCX×PCY.< PC.ₐ h , PC.ₐ k >
      wun-aux-tr : {Z : ℙ.Obj} (h : || ℙ.Hom Z X ||) (k : || ℙ.Hom Z Y ||)
                      → ×rc.ar ℂ.∘ wun-aux h k ℂ.~ PCX×PCY.< PC.ₐ h , PC.ₐ k >
      wun-aux-tr {Z} h k = PC.rp.lift-tr Z {repi = ×rc.is-repi} {PCX×PCY.< PC.ₐ h , PC.ₐ k >}
      wun : {Z : ℙ.Obj} (h : || ℙ.Hom Z X ||) (k : || ℙ.Hom Z Y ||) → || ℙ.Hom Z w×Ob ||
      wun h k = PC.full-ar (wun-aux h k)
      tr₁PC : {Z : ℙ.Obj} (h : || ℙ.Hom Z X ||) (k : || ℙ.Hom Z Y ||)
                 → PC.ₐ wπ₁ ℂ.∘ PC.ₐ (wun h k) ℂ.~ PC.ₐ h
      tr₁PC {Z} h k = ~proof
        PC.ₐ wπ₁ ℂ.∘ PC.ₐ (wun h k)                           ~[ ∘e PC.full-pf PC.full-pf ⊙ assˢ ] /
        PCX×PCY.π₁ ℂ.∘ ×rc.ar ℂ.∘ wun-aux h k                 ~[ ∘e (wun-aux-tr h k) r ] /
        PCX×PCY.π₁ ℂ.∘ PCX×PCY.< PC.ₐ h , PC.ₐ k >            ~[ PCX×PCY.×tr₁ ]∎
        PC.ₐ h ∎
                where open ecategory-aux-only ℂ
      tr₂PC : {Z : ℙ.Obj} (h : || ℙ.Hom Z X ||) (k : || ℙ.Hom Z Y ||)
                 → PC.ₐ wπ₂ ℂ.∘ PC.ₐ (wun h k) ℂ.~ PC.ₐ k
      tr₂PC {Z} h k = ~proof
        PC.ₐ wπ₂ ℂ.∘ PC.ₐ (wun h k)                           ~[ ∘e PC.full-pf PC.full-pf ⊙ assˢ ] /
        PCX×PCY.π₂ ℂ.∘ ×rc.ar ℂ.∘ wun-aux h k                 ~[ ∘e (wun-aux-tr h k) r ] /
        PCX×PCY.π₂ ℂ.∘ PCX×PCY.< PC.ₐ h , PC.ₐ k >            ~[ PCX×PCY.×tr₂ ]∎
        PC.ₐ k ∎
               where open ecategory-aux-only ℂ
    -- end private
    Xw×Y : ℙ.wproduct-of X Y
    Xw×Y = record
      { w×sp/ = ℙ.mkspan/ wπ₁ wπ₂
      ; w×isprd = record
                { w<_,_> = wun
                ; w×tr₁ = λ {_} {h} {k} → PC.faith-pf (PC.∘ax-rfˢ ⊙ tr₁PC h k)
                ; w×tr₂ = λ {_} {h} {k} → PC.faith-pf (PC.∘ax-rfˢ ⊙ tr₂PC h k)
                }
      }
      where open ecategory-aux-only ℂ
  -- end cover-of-product-is-weak-product


  dom-has-bin-weak-products : has-bin-weak-products ℙ
  dom-has-bin-weak-products = record
    { wprd-of = Xw×Y
    }
    where module tmp (X Y : ℙ.Obj) = cover-of-product-is-weak-product (flℂ.prd-of (PC.ₒ X) (PC.ₒ Y))
          open tmp



  module cover-of-equaliser-is-weak-equaliser {X Y : ℙ.Obj} {f f' : || ℙ.Hom X Y ||}
                                           (eql : ℂ.equaliser-of (PC.ₐ f) (PC.ₐ f'))
                                           where
    private
      module PCf~PCf' = ℂ.equaliser-of eql
      module ~rc = PC.rc PCf~PCf'.Eql
      wE : ℙ.Obj
      wE = PC.rc.Ob PCf~PCf'.Eql
      we : || ℙ.Hom wE X ||
      we = PC.full-ar (PCf~PCf'.eqlar ℂ.∘ ~rc.ar)
      weq : f ℙ.∘ we ℙ.~ f' ℙ.∘ we
      weq = PC.faith-pf (PC.∘ax-rfˢ ⊙ ∘e (PC.full-pf {_}) r ⊙ ass
                        ⊙ ∘e r PCf~PCf'.eqleq ⊙ assˢ ⊙ ∘e (PC.full-pf {_} ˢ) r ⊙ PC.∘ax-rf)
          where open ecategory-aux-only ℂ

      wun-aux : {Z : ℙ.Obj} {h : || ℙ.Hom Z X ||} (pf : f ℙ.∘ h ℙ.~ f' ℙ.∘ h)
                   → || ℂ.Hom (PC.ₒ Z) (PC.ₒ wE) ||
      wun-aux {Z} {h} pf = PC.rp.lift Z ~rc.is-repi (PC.ₐ h PCf~PCf'.|eql[ PC.∘∘ pf ])
      wun-aux-tr : {Z : ℙ.Obj} {h : || ℙ.Hom Z X ||} (pf : f ℙ.∘ h ℙ.~ f' ℙ.∘ h)
                   → ~rc.ar ℂ.∘ wun-aux pf ℂ.~ PC.ₐ h PCf~PCf'.|eql[ PC.∘∘ pf ]
      wun-aux-tr {Z} {h} pf = PC.rp.lift-tr Z {repi = ~rc.is-repi} {PC.ₐ h PCf~PCf'.|eql[ PC.∘∘ pf ]}
      wun : {Z : ℙ.Obj} (h : || ℙ.Hom Z X ||) (pf : f ℙ.∘ h ℙ.~ f' ℙ.∘ h) → || ℙ.Hom Z wE ||
      wun _ pf = PC.full-ar (wun-aux pf)
      trPC : {Z : ℙ.Obj} {h : || ℙ.Hom Z X ||} (pf : f ℙ.∘ h ℙ.~ f' ℙ.∘ h)
                → PC.ₐ we ℂ.∘ PC.ₐ (wun h pf) ℂ.~ PC.ₐ h
      trPC {_} {h} pf = ~proof
        PC.ₐ we ℂ.∘ PC.ₐ (wun h pf)                             ~[ ∘e PC.full-pf PC.full-pf ⊙ assˢ ] /
        PCf~PCf'.eqlar  ℂ.∘ ~rc.ar ℂ.∘ wun-aux pf              ~[ ∘e (wun-aux-tr pf) r ] /
        PCf~PCf'.eqlar ℂ.∘ PC.ₐ h PCf~PCf'.|eql[ PC.∘∘ pf ]     ~[ PCf~PCf'.eqltr (PC.∘∘ pf) ]∎
        PC.ₐ h ∎
              where open ecategory-aux-only ℂ
    -- end private
    fw~f' : ℙ.wequaliser-of f f'
    fw~f' = record
      { wEql = wE
      ; weqlar = we
      ; weqleq = weq
      ; isweql = record
               { _|weql[_] = wun
               ; weqltr = λ pf → PC.faith-pf (PC.∘ax-rfˢ ⊙ trPC pf)
               }
      }
      where open ecategory-aux-only ℂ
  -- end cover-of-equaliser-is-weak-equaliser


  dom-has-weak-equalisers : has-weak-equalisers ℙ
  dom-has-weak-equalisers = record
    { weql-of = fw~f'
    }
    where module tmp {X Y : ℙ.Obj} (f f' : || ℙ.Hom X Y ||)
                     = cover-of-equaliser-is-weak-equaliser (flℂ.eql-of (PC.ₐ f) (PC.ₐ f'))
          open tmp



  module cover-of-pullback-is-weak-pullback {X Y Z : ℙ.Obj} {f : || ℙ.Hom X Z ||} {g : || ℙ.Hom Y Z ||}
                                         (pb : ℂ.pullback-of (PC.ₐ f) (PC.ₐ g))
                                         where
    private
      module PCf×/PCg = ℂ.pullback-of-not pb
      module ×/rc = PC.rc PCf×/PCg.ul
      w×/Ob : ℙ.Obj
      w×/Ob = PC.rc.Ob PCf×/PCg.ul
      wπ/₁ : || ℙ.Hom w×/Ob X ||
      wπ/₁ = PC.full-ar (PCf×/PCg.π/₁ ℂ.∘ ×/rc.ar)
      wπ/₂ : || ℙ.Hom w×/Ob Y ||
      wπ/₂ = PC.full-ar (PCf×/PCg.π/₂ ℂ.∘ ×/rc.ar)
      w×/sqpf : f ℙ.∘ wπ/₁ ℙ.~ g ℙ.∘ wπ/₂
      w×/sqpf = PC.faith-pf (~proof
        PC.ₐ (f ℙ.∘ wπ/₁)                     ~[ PC.∘ax-rfˢ ⊙ ∘e PC.full-pf r ] /
        PC.ₐ f ℂ.∘ PCf×/PCg.π/₁ ℂ.∘ ×/rc.ar   ~[ ass ⊙ ∘e r PCf×/PCg.×/sqpf ⊙ assˢ ] /
        PC.ₐ g ℂ.∘ PCf×/PCg.π/₂ ℂ.∘ ×/rc.ar   ~[ ∘e (PC.full-pf ˢ) r ⊙ PC.∘ax-rf ]∎
        PC.ₐ (g ℙ.∘ wπ/₂) ∎)
              where open ecategory-aux-only ℂ
      wun-aux : {W : ℙ.Obj} {h : || ℙ.Hom W X ||} {k : || ℙ.Hom W Y ||}
                   → f ℙ.∘ h ℙ.~ g ℙ.∘ k → || ℂ.Hom (PC.ₒ W) (PC.ₒ w×/Ob) ||
      wun-aux {W} {h} {k} pf = PC.rp.lift W ×/rc.is-repi PCf×/PCg.⟨ PC.ₐ h , PC.ₐ k ⟩[ PC.∘∘ pf ]
      wun-aux-tr : {W : ℙ.Obj} {h : || ℙ.Hom W X ||} {k : || ℙ.Hom W Y ||} (pf : f ℙ.∘ h ℙ.~ g ℙ.∘ k)
                      → ×/rc.ar ℂ.∘ wun-aux pf ℂ.~ PCf×/PCg.⟨ PC.ₐ h , PC.ₐ k ⟩[ PC.∘∘ pf ]
      wun-aux-tr {W} {h} {k} pf = PC.rp.lift-tr W {repi = ×/rc.is-repi} {PCf×/PCg.⟨ PC.ₐ h , PC.ₐ k ⟩[ PC.∘∘ pf ]}
      wun : {W : ℙ.Obj} (h : || ℙ.Hom W X ||) (k : || ℙ.Hom W Y ||)
               → f ℙ.∘ h ℙ.~ g ℙ.∘ k → || ℙ.Hom W w×/Ob ||
      wun h k pf = PC.full-ar (wun-aux pf)
      tr₁PC : {W : ℙ.Obj} {h : || ℙ.Hom W X ||} {k : || ℙ.Hom W Y ||} (pf : f ℙ.∘ h ℙ.~ g ℙ.∘ k)
                 → PC.ₐ wπ/₁ ℂ.∘ PC.ₐ (wun h k pf) ℂ.~ PC.ₐ h
      tr₁PC {W} {h} {k} pf = ~proof
        PC.ₐ wπ/₁ ℂ.∘ PC.ₐ (wun h k pf)                                ~[ ∘e PC.full-pf PC.full-pf ⊙ assˢ ] /
        PCf×/PCg.π/₁ ℂ.∘ ×/rc.ar ℂ.∘ wun-aux pf                        ~[ ∘e (wun-aux-tr pf) r ] /
        PCf×/PCg.π/₁ ℂ.∘ PCf×/PCg.⟨ PC.ₐ h , PC.ₐ k ⟩[ PC.∘∘ pf ]        ~[ PCf×/PCg.×/tr₁ (PC.∘∘ pf) ]∎
        PC.ₐ h ∎
                where open ecategory-aux-only ℂ
      tr₂PC : {W : ℙ.Obj} {h : || ℙ.Hom W X ||} {k : || ℙ.Hom W Y ||} (pf : f ℙ.∘ h ℙ.~ g ℙ.∘ k)
                 → PC.ₐ wπ/₂ ℂ.∘ PC.ₐ (wun h k pf) ℂ.~ PC.ₐ k
      tr₂PC {W} {h} {k} pf = ~proof
        PC.ₐ wπ/₂ ℂ.∘ PC.ₐ (wun h k pf)                               ~[ ∘e PC.full-pf PC.full-pf ⊙ assˢ ] /
        PCf×/PCg.π/₂ ℂ.∘ ×/rc.ar ℂ.∘ wun-aux pf                       ~[ ∘e (wun-aux-tr pf) r ] /
        PCf×/PCg.π/₂ ℂ.∘ PCf×/PCg.⟨ PC.ₐ h , PC.ₐ k ⟩[ PC.∘∘ pf ]       ~[ PCf×/PCg.×/tr₂ (PC.∘∘ pf) ]∎
        PC.ₐ k ∎
               where open ecategory-aux-only ℂ
    -- end private
    fw×/g : ℙ.wpullback-of f g
    fw×/g = record
      { w×/sq/ = ℙ.mksq/ w×/sqpf
      ; w×/iswpbsq = record
                   { w⟨_,_⟩[_] = wun
                   ; w×/tr₁ = λ pf → PC.faith-pf (PC.∘ax-rfˢ ⊙ tr₁PC pf)
                   ; w×/tr₂ = λ pf → PC.faith-pf (PC.∘ax-rfˢ ⊙ tr₂PC pf)
                   }
      }
      where open ecategory-aux-only ℂ
  -- end cover-of-pullback-is-weak-pullback


  dom-has-weak-pullbacks : has-weak-pullbacks ℙ
  dom-has-weak-pullbacks = record
    { wpb-of = fw×/g
    }
    where module tmp {X Y Z : ℙ.Obj} (f : || ℙ.Hom X Z ||) (g : || ℙ.Hom Y Z ||)
                     = cover-of-pullback-is-weak-pullback (flℂ.pb-of (PC.ₐ f) (PC.ₐ g))
          open tmp



  dom-has-fin-weak-limits : has-fin-weak-limits ℙ
  dom-has-fin-weak-limits = record
    { haswtrm = dom-has-weak-terminal
    ; haswprd = dom-has-bin-weak-products
    ; hasweql = dom-has-weak-equalisers
    ; haswpb = dom-has-weak-pullbacks
    ; haswbw = has-weql+wpb⇒has-wbw dom-has-weak-equalisers dom-has-weak-pullbacks
    }
-- end projective-cover-props



-- Properties of projective covers into regular categories

module projective-cover-on-reg-cat-props {𝔼 : ecategory} (𝔼isreg : is-regular 𝔼)
                                         {ℙ : ecategory} {PC : efunctor ℙ 𝔼} (ispjcov : is-projective-cover PC)
                                         where
  private
    module ℙ where
      open ecategory ℙ public
      open comm-shapes ℙ public
      open epis&monos-defs ℙ public
      open epis&monos-props ℙ public
      open kernel-pairs-defs ℙ public
      open finite-limits-d&p ℙ public
      open finite-weak-limits-d&p ℙ public
      open limits→weak-limits ℙ public
    module 𝔼 where
      open ecategory 𝔼 public
      open comm-shapes 𝔼 public
      open iso-defs 𝔼 public
      open epis&monos-defs 𝔼 public
      open epis&monos-props 𝔼 public
      open kernel-pairs-defs 𝔼 public
      open eq-rel-defs 𝔼 public
      open finite-limits-d&p 𝔼 public
      --open finite-weak-limits-d&p 𝔼 public
      --open limits→weak-limits 𝔼 public
      --open relations-among-limit-diagrams 𝔼 public
      open projective-defs 𝔼 public
    module r𝔼 where
      open regular-cat-d&p 𝔼isreg public
      --open has-fin-limits hasfl public
      open has-terminal hastrm public
      open has-bin-products hasprd using (prd-of) public
      open has-equalisers haseql using (eql-of) public
      open has-pullbacks haspb using (pb-of) public
      open has-bows hasbw using (bw-of) public
    open projective-cover-props r𝔼.hasfl ispjcov
    module fwlℙ where
      open has-fin-weak-limits dom-has-fin-weak-limits public
    module PC where
      open efunctor-aux PC public
      open is-projective-cover ispjcov public


  -- PC is left covering
  
  module PC-is-left-cov-trm  {PT : ℙ.Obj} (PT-pf : ℙ.is-wterminal PT)
                             {CT : 𝔼.Obj} (CT-pf : 𝔼.is-terminal CT)
                             (cov! : || 𝔼.Hom (PC.ₒ PT) CT ||)
                             where
    private
      module PT = ℙ.is-wterminal PT-pf
      module CT = 𝔼.is-terminal CT-pf
      module rcT = PC.rc CT
      module wTrc where
        Ob : ℙ.Obj
        Ob = cover-of-terminal-is-weak-terminal.wT CT-pf
        open ℙ.is-wterminal (cover-of-terminal-is-weak-terminal.iswtrm CT-pf) public
    med-ar : || ℙ.Hom wTrc.Ob PT ||
    med-ar = PT.w! wTrc.Ob
    cov!-pf : cov! 𝔼.∘ PC.ₐ med-ar 𝔼.~ rcT.ar
    cov!-pf = CT.!uqg
    cov!-repi : 𝔼.is-regular-epi cov!
    cov!-repi = r𝔼.repi-triang cov!-pf rcT.is-repi
 -- end PC-is-left-cov-trm

  PC-is-left-cov-trm : is-left-covering-trm PC
  PC-is-left-cov-trm = record
    { trmuniv-is-repi = cov!-repi
    }
    where open PC-is-left-cov-trm



  module PC-is-left-cov-prd  {X Y : ℙ.Obj} {V : ℙ.Obj} {Pp₁ : || ℙ.Hom V X ||} {Pp₂ : || ℙ.Hom V Y ||}
                             (Pw× : ℙ.is-wproduct (ℙ.mkspan Pp₁ Pp₂))
                             {P : 𝔼.Obj} {Ep₁ : || 𝔼.Hom P (PC.ₒ X) ||} {Ep₂ : || 𝔼.Hom P (PC.ₒ Y) ||}
                             (E× : 𝔼.is-product (𝔼.mkspan Ep₁ Ep₂)) {cov× : || 𝔼.Hom (PC.ₒ V) P ||}
                             (cov×-tr₁ : Ep₁ 𝔼.∘ cov× 𝔼.~ PC.ₐ Pp₁) (cov×-tr₂ : Ep₂ 𝔼.∘ cov× 𝔼.~ PC.ₐ Pp₂)
                             where
    private
      module Pw× = ℙ.bin-wproduct-not (ℙ.mkw× Pw×)
      module E× = 𝔼.bin-product-not (𝔼.mk× E×)
      module rc× = PC.rc E×.O12
      module w×rc = ℙ.wproduct-of-not (cover-of-product-is-weak-product.Xw×Y (𝔼.mk×of E×))
    med-ar : || ℙ.Hom w×rc.O12 V ||
    med-ar = Pw×.w< w×rc.wπ₁ , w×rc.wπ₂ >
    cov×-pf : cov× 𝔼.∘ PC.ₐ med-ar 𝔼.~ rc×.ar
    cov×-pf = E×.×uq (~proof E×.π₁ 𝔼.∘ cov× 𝔼.∘ PC.ₐ med-ar      ~[ ass ⊙ ∘e r cov×-tr₁ ] /
                             PC.ₐ Pw×.wπ₁ 𝔼.∘ PC.ₐ med-ar         ~[ PC.∘ax Pw×.w×tr₁ ⊙ PC.full-pf ]∎
                             E×.π₁ 𝔼.∘ rc×.ar ∎)
                     (~proof E×.π₂ 𝔼.∘ cov× 𝔼.∘ PC.ₐ med-ar      ~[ ass ⊙ ∘e r cov×-tr₂ ] /
                             PC.ₐ Pw×.wπ₂ 𝔼.∘ PC.ₐ med-ar         ~[ PC.∘ax Pw×.w×tr₂ ⊙ PC.full-pf ]∎
                             E×.π₂ 𝔼.∘ rc×.ar ∎)
              where open ecategory-aux-only 𝔼
    cov×-repi : 𝔼.is-regular-epi cov×
    cov×-repi = r𝔼.repi-triang cov×-pf rc×.is-repi
  -- end PC-is-left-cov-prd


  PC-is-left-cov-prd : is-left-covering-prd PC
  PC-is-left-cov-prd = record
    { prduniv-is-repi = λ P×of E×of tr₁ tr₂ → cov×-repi (P.w×isprd P×of) (E.×isprd E×of) tr₁ tr₂
    }
    where open PC-is-left-cov-prd
          module P = ℙ.wproduct-of
          module E = 𝔼.product-of



  module PC-is-left-cov-eql {X Y : ℙ.Obj} {f₁ f₂ : || ℙ.Hom X Y ||}
                            {PwE : ℙ.Obj} {Pwe : || ℙ.Hom PwE X ||} {Pweql-eq : f₁ ℙ.∘ Pwe ℙ.~ f₂ ℙ.∘ Pwe}
                            (Pweql-pf : ℙ.is-wequaliser Pweql-eq) {EE : 𝔼.Obj} {Ee : || 𝔼.Hom EE (PC.ₒ X) ||}
                            {Eeql-eq : (PC.ₐ f₁) 𝔼.∘ Ee 𝔼.~ (PC.ₐ f₂) 𝔼.∘ Ee} (Eeql-pf : 𝔼.is-equaliser Eeql-eq)
                            {coveql : || 𝔼.Hom (PC.ₒ PwE) EE ||} (coveql-tr : Ee 𝔼.∘ coveql 𝔼.~ PC.ₐ Pwe)
                            where
    private
      module Pe = ℙ.wequaliser-of (ℙ.mkweql-of Pweql-pf)
      module Ee = 𝔼.equaliser-of (𝔼.mkeql-of Eeql-pf)
      module rce = PC.rc Ee.Eql
      module werc = ℙ.wequaliser-of (cover-of-equaliser-is-weak-equaliser.fw~f' (𝔼.mkeql-of Eeql-pf))
    med-ar : || ℙ.Hom werc.wEql Pe.wEql ||
    med-ar =  werc.weqlar Pe.|weql[ werc.weqleq ]
    coveql-pf : coveql 𝔼.∘ PC.ₐ med-ar 𝔼.~ rce.ar
    coveql-pf = Ee.eqluq (~proof
      Ee.eqlar 𝔼.∘ coveql 𝔼.∘ PC.ₐ med-ar     ~[ ass ⊙ ∘e r coveql-tr ] /
      PC.ₐ Pe.weqlar 𝔼.∘ PC.ₐ med-ar           ~[ PC.∘ax (Pe.weqltr werc.weqleq) ] /
      PC.ₐ werc.weqlar                         ~[ PC.full-pf ]∎
      Ee.eqlar 𝔼.∘ rce.ar ∎)
              where open ecategory-aux-only 𝔼
    coveql-repi : 𝔼.is-regular-epi coveql
    coveql-repi = r𝔼.repi-triang coveql-pf rce.is-repi
-- end PC-is-left-cov-eql


  PC-is-left-cov-eql : is-left-covering-eql PC
  PC-is-left-cov-eql = record
    { eqluniv-is-repi = λ weqlof eqlof tr → coveql-repi (P.isweql weqlof) (E.iseql eqlof) tr
    }
    where open PC-is-left-cov-eql
          module P = ℙ.wequaliser-of
          module E = 𝔼.equaliser-of




  module PC-is-left-cov-pb  {Z X Y : ℙ.Obj} {x : || ℙ.Hom X Z ||} {y : || ℙ.Hom Y Z ||}
                            {V : ℙ.Obj} {Pp₁ : || ℙ.Hom V X ||} {Pp₂ : || ℙ.Hom V Y ||} {Peqpf : x ℙ.∘ Pp₁ ℙ.~ y ℙ.∘ Pp₂}
                            (Pw×/ : ℙ.is-wpb-square (ℙ.mksq (ℙ.mksq/ Peqpf)))
                            {P : 𝔼.Obj} {p₁ : || 𝔼.Hom P (PC.ₒ X) ||} {p₂ : || 𝔼.Hom P (PC.ₒ Y) ||}
                            {Eeqpf : PC.ₐ x 𝔼.∘ p₁ 𝔼.~ PC.ₐ y 𝔼.∘ p₂} (E×/ : 𝔼.is-pb-square (𝔼.mksq (𝔼.mksq/ Eeqpf)))
                            {cov×/ : || 𝔼.Hom (PC.ₒ V) P ||}
                            (cov×/-tr₁ : p₁ 𝔼.∘ cov×/ 𝔼.~ PC.ₐ Pp₁) (cov×/-tr₂ : p₂ 𝔼.∘ cov×/ 𝔼.~ PC.ₐ Pp₂)                           
{-                            {X Y : ℙ.Obj} {V : ℙ.Obj} {Pp₁ : || ℙ.Hom V X ||} {Pp₂ : || ℙ.Hom V Y ||}
                            (Pw× : ℙ.is-wproduct (ℙ.mkspan Pp₁ Pp₂))
                            {P : 𝔼.Obj} {Ep₁ : || 𝔼.Hom P (PC.ₒ X) ||} {Ep₂ : || 𝔼.Hom P (PC.ₒ Y) ||}
                            (E× : 𝔼.is-product (𝔼.mkspan Ep₁ Ep₂)) {cov× : || 𝔼.Hom (PC.ₒ V) P ||}
                            (cov×-tr₁ : Ep₁ 𝔼.∘ cov× 𝔼.~ PC.ₐ Pp₁) (cov×-tr₂ : Ep₂ 𝔼.∘ cov× 𝔼.~ PC.ₐ Pp₂)-}
                            where
    private
      module Pw×/ = ℙ.wpullback-sq-not (ℙ.mkwpb-sq Pw×/)
      module E×/ = 𝔼.pullback-sq-not (𝔼.mkpb-sq E×/)
      module rc×/ = PC.rc E×/.ul
      module w×/rc = ℙ.wpullback-of-not (cover-of-pullback-is-weak-pullback.fw×/g (𝔼.mkpb-of E×/))
    med-ar : || ℙ.Hom w×/rc.ul V ||
    med-ar = Pw×/.w⟨ w×/rc.wπ/₁ , w×/rc.wπ/₂ ⟩[ w×/rc.w×/sqpf ]
    cov×/-pf : cov×/ 𝔼.∘ PC.ₐ med-ar 𝔼.~ rc×/.ar
    cov×/-pf = E×/.×/uq (~proof E×/.π/₁ 𝔼.∘ cov×/ 𝔼.∘ PC.ₐ med-ar      ~[ ass ⊙ ∘e r cov×/-tr₁ ] /
                                PC.ₐ Pw×/.wπ/₁ 𝔼.∘ PC.ₐ med-ar         ~[ PC.∘ax (Pw×/.w×/tr₁ w×/rc.w×/sqpf) ⊙ PC.full-pf ]∎
                                E×/.π/₁ 𝔼.∘ rc×/.ar ∎)
                        (~proof E×/.π/₂ 𝔼.∘ cov×/ 𝔼.∘ PC.ₐ med-ar      ~[ ass ⊙ ∘e r cov×/-tr₂ ] /
                                PC.ₐ Pw×/.wπ/₂ 𝔼.∘ PC.ₐ med-ar         ~[ PC.∘ax (Pw×/.w×/tr₂ w×/rc.w×/sqpf) ⊙ PC.full-pf ]∎
                                E×/.π/₂ 𝔼.∘ rc×/.ar ∎)
              where open ecategory-aux-only 𝔼
    cov×/-repi : 𝔼.is-regular-epi cov×/
    cov×/-repi = r𝔼.repi-triang cov×/-pf rc×/.is-repi
  -- end PC-is-left-cov-pb


  PC-is-left-cov-pb : is-left-covering-pb PC
  PC-is-left-cov-pb = record
    { pbuniv-is-repi = λ P×/of E×/of tr₁ tr₂ → cov×/-repi (P.w×/iswpbsq P×/of) (E.×/ispbsq E×/of) tr₁ tr₂
    }
    where open PC-is-left-cov-pb
          module P = ℙ.wpullback-of
          module E = 𝔼.pullback-of


  PC-is-left-cov : is-left-covering PC
  PC-is-left-cov = record
    { lc! = PC-is-left-cov-trm
    ; lc× = PC-is-left-cov-prd
    ; lceql = PC-is-left-cov-eql
    ; lc×/ = PC-is-left-cov-pb
    ; lcbw = lcov-eql+pb→lcov-bw 𝔼isreg fwlℙ.hasweql fwlℙ.haswpb PC-is-left-cov-eql PC-is-left-cov-pb
    }

-- end projective-cover-on-reg-cat-props


-- A projective cover into a regualr category is left covering

proj-cover-is-left-covering : {𝔼 : ecategory} (regE : is-regular 𝔼) {ℙ : ecategory} {PC : efunctor ℙ 𝔼}
                                 → is-projective-cover PC → is-left-covering PC
proj-cover-is-left-covering 𝔼isreg ispjcov = PC-is-left-cov
                                            where open projective-cover-on-reg-cat-props 𝔼isreg ispjcov
