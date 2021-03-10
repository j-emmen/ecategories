
-- disable the K axiom:

{-# OPTIONS --without-K #-}

-- Agda version 2.5.4.1

module ecats.exact-completion.exact.canonical-epi&mono where

open import ecats.basic-defs.ecat-def&not
open import ecats.basic-defs.commut-shapes
open import ecats.basic-defs.epi&mono
open import ecats.basic-defs.eqv-rel
open import ecats.basic-defs.kernel-pair
open import ecats.basic-props.epi&mono
open import ecats.finite-limits.defs.collective
open import ecats.finite-limits.d&n-weak-pullback
open import ecats.finite-limits.props.weak-pullback
open import ecats.finite-limits.defs.weak-Wlimit
open import ecats.finite-limits.props.relations-among-weak-limits
open import ecats.exact-completion.CVconstruction





module can-epi&mono-defs {ℂ : ecategory} (hasfwl : has-fin-weak-limits ℂ) where
  private
    module ℂ where
      open ecategory ℂ public
      open comm-shapes ℂ public
      open pseudo-eq-rel-defs ℂ public
      open weak-kernel-pairs-defs ℂ public
      open wpullback-squares ℂ public
      open weak-pullback-props ℂ public
      open weak-bow-defs ℂ public
      open wWlim-defs ℂ public
    module fwlℂ where
      open has-fin-weak-limits hasfwl public
      open has-weak-pullbacks haswpb using (wpb-of) public
      open has-weak-bows haswbw using (wbw-of) public
      open has-weak-Wlimits (has-wpb⇒has-wWlim haswpb) public
    module Exℂ where
      open ecategory Ex ℂ [ hasfwl ] public
      open comm-shapes Ex ℂ [ hasfwl ] public
      open epis&monos-defs Ex ℂ [ hasfwl ] public
      open epis&monos-props Ex ℂ [ hasfwl ] public
      open pullback-defs Ex ℂ [ hasfwl ] public
      open eq-rel-defs Ex ℂ [ hasfwl ] public
      open kernel-pairs-defs Ex ℂ [ hasfwl ] public



  -- canonical regular epi
  
  record canonical-repi {Lo : ℂ.Obj} (R/ S/ : ℂ.peqOver Lo) : Set₁ where
    private
      R = ℂ.mkpeq-c R/
      S = ℂ.mkpeq-c S/
      module R = ℂ.peq R
      module S = ℂ.peq S
    field
      crepi-hi : || ℂ.Hom R.Hi S.Hi ||
      crepi-ax₀ : S.%0 ℂ.∘ crepi-hi ℂ.~ R.%0
      crepi-ax₁ : S.%1 ℂ.∘ crepi-hi ℂ.~ R.%1

    ar : || Exℂ.Hom R S ||
    ar = record
      { lo = ℂ.idar Lo
      ; isext = record
        { hi = crepi-hi
        ; cmptb₀ = crepi-ax₀ ⊙ lidˢ
        ; cmptb₁ = crepi-ax₁ ⊙ lidˢ
        }
      }
      where open ecategory-aux-only ℂ
    can-repi-is-repi : Exℂ.is-regular-epi ar
    can-repi-is-repi = record
      { relOb = ℂ.freepeq S.Hi
      ; rel₁ = ℂ.freepeq-is-min R S.%0
      ; rel₂ = ℂ.freepeq-is-min R S.%1
      ; coeq = record
        { eq = eq
        ; univ = λ {U} f pf → un.uar U f pf
        ; univ-eq = λ {U} {f} pf → un.tr U f pf
        ; uniq = record { epi-pf = λ {U} {h} {h'} pf → uq U h h' pf }
        }
      }
      where open ecategory-aux-only ℂ
            eq : ar Exℂ.∘ ℂ.freepeq-is-min R S.%0 Exℂ.~ ar Exℂ.∘ ℂ.freepeq-is-min R S.%1
            eq = record
              { hty = ℂ.idar S.Hi
              ; hty₀ = ridgen lidˢ
              ; hty₁ = ridgen lidˢ
              }
            uq : (U : Exℂ.Obj) (h h' : || Exℂ.Hom S U ||)
                    → h Exℂ.∘ ar Exℂ.~ h' Exℂ.∘ ar → h Exℂ.~ h'
            uq U h h' pf = record
              { hty = pf.hty
              ; hty₀ = pf.hty₀ ⊙ rid
              ; hty₁ = pf.hty₁ ⊙ rid
              }
              where module pf = ℂ.peq-mor-eq pf
            module un (U : Exℂ.Obj) (f : || Exℂ.Hom R U ||)
                      (pf : f Exℂ.∘ ℂ.freepeq-is-min R S.%0 Exℂ.~ f Exℂ.∘ ℂ.freepeq-is-min R S.%1) where
              private
                module U = ℂ.peq U
                module f = ℂ.peq-mor f
                module pf = ℂ.peq-mor-eq pf
              uar : || Exℂ.Hom S U ||
              uar = record
                { lo = f.lo
                ; isext = record
                  { hi = pf.hty
                  ; cmptb₀ = pf.hty₀
                  ; cmptb₁ = pf.hty₁
                  }
                }
              tr : uar Exℂ.∘ ar Exℂ.~ f
              tr = record
                { hty = U.ρ ℂ.∘ f.lo
                ; hty₀ = ass ⊙ lidgg ridˢ U.ρ-ax₀
                ; hty₁ = ass ⊙ lidgg r U.ρ-ax₁
                }

{-            can-repi-is-coeq : Exℂ.is-coeq can-repi-peq₀ can-repi-peq₁ ar
            can-repi-is-coeq = record
              { eq = c-eq
              ; univ = c-univ
              ; univ-eq = λ {U} {f} pf → record
                        { hty = ρ U ℂ.∘ lo f
                        ; hty₀ = ass ⊙ lidgg ridˢ (ρ-ax₀ U)
                        ; hty₁ = ass ⊙ lidgg r (ρ-ax₁ U)
                        }
              ; uniq = record
                     { epi-pf = λ {V} {g} {g'} pf → record
                              { hty = hty pf
                              ; hty₀ = hty₀ pf ⊙ rid
                              ; hty₁ = hty₁ pf ⊙ rid
                              }
                     }
              }
              where open ecategory-aux-only ℂ
                    open ℂ.peq
                    open ℂ.peq-mor
                    open ℂ.peq-mor-eq
                    can-repi-peq : ℂ.peq
            can-repi-peq = ℂ.freepeq S.Hi
            can-repi-peq₀ can-repi-peq₁ : || Exℂ.Hom can-repi-peq R ||
            can-repi-peq₀ = ℂ.freepeq-is-min R S.%0
            can-repi-peq₁ = ℂ.freepeq-is-min R S.%1
                                                      c-univ : {U : Exℂ.Obj} (f : || Exℂ.Hom R U ||)
                                → f Exℂ.∘ can-repi-peq₀ Exℂ.~ f Exℂ.∘ can-repi-peq₁
                                  → || Exℂ.Hom S U ||
                    c-univ f pf = record { lo = lo f
                                         ; isext = record
                                           { hi = hty pf
                                           ; cmptb₀ = hty₀ pf
                                           ; cmptb₁ = hty₁ pf
                                           }
                                         }
-}

    module isrepi = Exℂ.is-regular-epi can-repi-is-repi
  -- end record canonical-repi


  module canonical-ex-seq (R : ℂ.peq) where
    private module R = ℂ.peq R
    freeLo freeHi : ℂ.peq
    freeLo = ℂ.freepeq R.Lo
    freeHi = ℂ.freepeq R.Hi
    module freeHi = ℂ.peq freeHi
    module freeLo = ℂ.peq freeLo
    crepi : canonical-repi freeLo.peqover R.peqover
    crepi = record
      { crepi-hi = R.ρ
      ; crepi-ax₀ = R.ρ-ax₀
      ; crepi-ax₁ = R.ρ-ax₁
      }
    coeq-of-free : Exℂ.coeq-of (ℂ.freepeq-mor R.%0) (ℂ.freepeq-mor R.%1)
    coeq-of-free = record
      { ar = cr.ar
      ; iscoeq = record
        { eq = sqpf
        ; univ = λ {U} f pf → un.ar U f pf
        ; univ-eq = λ {U} {f} pf → un.tr U f pf
        ; uniq = cr.isrepi.uniq
        }
      }
      where open ecategory-aux-only ℂ
            module cr = canonical-repi crepi
            sqpf : cr.ar Exℂ.∘ ℂ.freepeq-mor R.%0 Exℂ.~ cr.ar Exℂ.∘ ℂ.freepeq-mor R.%1
            sqpf = record
              { hty = ℂ.idar R.Hi
              ; hty₀ = ridgen {f' = ℂ.idar R.Lo ℂ.∘ R.%0} lidˢ
              ; hty₁ = ridgen {f' = ℂ.idar R.Lo ℂ.∘ R.%1} lidˢ
              }
            module un (U : Exℂ.Obj) (f : || Exℂ.Hom (ℂ.freepeq R.Lo) U ||)
                      (pf : f Exℂ.∘ ℂ.freepeq-mor R.%0 Exℂ.~ f Exℂ.∘ ℂ.freepeq-mor R.%1) where
              private
                module U = ℂ.peq U
                module f = ℂ.peq-mor f
                module pf = ℂ.peq-mor-eq pf
              ar : || Exℂ.Hom R U ||
              ar = record
                { lo = f.lo
                ; isext = record
                  { hi = pf.hty
                  ; cmptb₀ = pf.hty₀
                  ; cmptb₁ = pf.hty₁
                  }
                }
              tr : ar Exℂ.∘ cr.ar Exℂ.~ f
              tr = record
                { hty = U.ρ ℂ.∘ f.lo
                ; hty₀ = ass ⊙ lidgg ridˢ U.ρ-ax₀
                ; hty₁ = ass ⊙ lidgg r U.ρ-ax₁
                }
    module cre where
      open canonical-repi crepi hiding (can-repi-is-repi) public
      open ℂ.peq-mor ar public
      private module c = Exℂ.coeq-of coeq-of-free
      isrepi : Exℂ.is-regular-epi ar
      isrepi = record { coeq = c.iscoeq }
      open Exℂ.is-regular-epi isrepi public    

    module KP where
      open ℂ.has-wbw→has-wkerpairsp fwlℂ.haswbw
      open ℂ.wbow-of (wkpsp-of R.sp/) public
      iswkp : ℂ.is-wkernel-pair-sp wπ//₁ wπ//₂
      iswkp = wπ//iswkp R.sp/
    kpOb/ : ℂ.peqOver R.Hi
    kpOb/ = record
      { Hi = KP.Ob
      ; %0 = KP.wπ//₁
      ; %1 = KP.wπ//₂
      ; ispeq = ℂ.is-wkerpsp+τpb→is-peqr (KP.iswkp) (fwlℂ.wpb-of KP.wπ//₂ KP.wπ//₁)
      }
    kpOb : ℂ.peq
    kpOb = record
      { Lo = R.Hi
      ; peqover = kpOb/
      }
    module kpOb = ℂ.peq kpOb
    kp₁ kp₂ : ℂ.peq-mor kpOb freeLo
    kp₁ = record
      { lo = R.%0
      ; isext = record
        { hi = R.%0 ℂ.∘ KP.wπ//₁
        ; cmptb₀ = lid
        ; cmptb₁ = lidgen KP.sqpf₁
        }
      }
      where open ecategory-aux-only ℂ
    kp₂ = record
      { lo = R.%1
      ; isext = record
        { hi = R.%1 ℂ.∘ KP.wπ//₁
        ; cmptb₀ = lid
        ; cmptb₁ = lidgen KP.sqpf₂
        }
      }
      where open ecategory-aux-only ℂ
    kpsqpf : cre.ar Exℂ.∘ kp₁ Exℂ.~ cre.ar Exℂ.∘ kp₂
    kpsqpf = record
      { hty = ℂ.idar R.Hi
      ; hty₀ = R.%0 ℂ.∘ ℂ.idar R.Hi ~[ ridgen lidˢ ] ℂ.idar R.Lo ℂ.∘ R.%0
      ; hty₁ = R.%1 ℂ.∘ ℂ.idar R.Hi ~[ ridgen lidˢ ] ℂ.idar R.Lo ℂ.∘ R.%1
      }
      where open ecategory-aux-only ℂ

    private
      module KP-univ (U : ℂ.peq) (h k : ℂ.peq-mor U freeLo) (pf : ℂ.peq-mor-eq (cre.ar Exℂ.∘ h) (cre.ar Exℂ.∘ k))
                     where
        open ecategory-aux-only ℂ
        private
          module U = ℂ.peq U
          module h = ℂ.peq-mor h
          module k = ℂ.peq-mor k
          module pf = ℂ.peq-mor-eq pf
        kpunpf₁ = ~proof R.%0 ℂ.∘ pf.hty ℂ.∘ U.%0 ~[ ass ⊙ ∘e r pf.hty₀ ⊙ assˢ ] /
                         cre.lo ℂ.∘ h.lo ℂ.∘ U.%0 ~[ ∘e (h.cmptb₀ ˢ ⊙ h.cmptb₁) r ] /
                         cre.lo ℂ.∘ h.lo ℂ.∘ U.%1 ~[ ass ⊙ ∘e r (pf.hty₀ ˢ) ⊙ assˢ ]∎
                         R.%0 ℂ.∘ pf.hty ℂ.∘ U.%1 ∎
        kpunpf₂ = ~proof R.%1 ℂ.∘ pf.hty ℂ.∘ U.%0 ~[ ass ⊙ ∘e r pf.hty₁ ⊙ assˢ ] /
                         cre.lo ℂ.∘ k.lo ℂ.∘ U.%0 ~[ ∘e (k.cmptb₀ ˢ ⊙ k.cmptb₁) r ] /
                         cre.lo ℂ.∘ k.lo ℂ.∘ U.%1 ~[ ass ⊙ ∘e r (pf.hty₁ ˢ) ⊙ assˢ ]∎
                         R.%1 ℂ.∘ pf.hty ℂ.∘ U.%1 ∎
        kp-univ : || Exℂ.Hom U kpOb ||
        kp-univ = record
          { lo = pf.hty
          ; isext = record
            { hi = KP.⟨ pf.hty ℂ.∘ U.%0 , pf.hty ℂ.∘ U.%1 ⟩[ kpunpf₁ , kpunpf₂ ]
            ; cmptb₀ = KP.tr₁ kpunpf₁ kpunpf₂
            ; cmptb₁ = KP.tr₂ kpunpf₁ kpunpf₂
            }
          }
        kp-tr₁ : kp₁ Exℂ.∘ kp-univ Exℂ.~ h
        kp-tr₁ = ℂ.peq-mor-eq-ext (pf.hty₀ ⊙ lid)
        kp-tr₂ : kp₂ Exℂ.∘ kp-univ Exℂ.~ k
        kp-tr₂ = ℂ.peq-mor-eq-ext (pf.hty₁ ⊙ lid)
      -- end KP-univ
      kppbuq : (U : Exℂ.Obj) (h h' : || Exℂ.Hom U kpOb ||)
                  → kp₁ Exℂ.∘ h Exℂ.~ kp₁ Exℂ.∘ h' → kp₂ Exℂ.∘ h Exℂ.~ kp₂ Exℂ.∘ h'
                    → h Exℂ.~ h'
      kppbuq U h h' pf1 pf2 = record
        { hty = KP.⟨ h.lo , h'.lo ⟩[ pf1.hty₀ ˢ ⊙ pf1.hty₁ , pf2.hty₀ ˢ ⊙ pf2.hty₁ ]
        ; hty₀ = KP.tr₁ (pf1.hty₀ ˢ ⊙ pf1.hty₁) (pf2.hty₀ ˢ ⊙ pf2.hty₁)
        ; hty₁ = KP.tr₂ (pf1.hty₀ ˢ ⊙ pf1.hty₁) (pf2.hty₀ ˢ ⊙ pf2.hty₁)
        }
        where open ecategory-aux-only ℂ
              module U = ℂ.peq U
              module h = ℂ.peq-mor h
              module h' = ℂ.peq-mor h'
              module pf1 = ℂ.peq-mor-eq pf1
              module pf2 = ℂ.peq-mor-eq pf2

    kppbsq : Exℂ.is-pb-square (Exℂ.mksq {freeLo} {freeLo} (Exℂ.mksq/ kpsqpf))
    kppbsq = record
      { ⟨_,_⟩[_] = λ {U} h k pf → kp-univ U h k pf
      ; ×/tr₁ = λ {U} {h} {k} pf → kp-tr₁ U h k pf
      ; ×/tr₂ = λ {U} {h} {k} pf → kp-tr₂ U h k pf
      ; ×/uq = λ {U} {h} {h'} pf1 pf2 → kppbuq U h h' pf1 pf2
      }
      where open KP-univ    
    crepi-coeq-kp : Exℂ.is-coeq kp₁ kp₂ cre.ar
    crepi-coeq-kp = record
      { eq = kpsqpf
      ; univ = λ f pf → record
        { lo = lo f
        ; isext = record
          { hi = hty pf
          ; cmptb₀ = hty₀ pf
          ; cmptb₁ = hty₁ pf
          }
        }
      ; univ-eq = λ {U} {f} pf → record
                { hty = ρ U ℂ.∘ lo f
                ; hty₀ = ass ⊙ lidgg ridˢ (ρ-ax₀ U)
                ; hty₁ = ass ⊙ lidgg r (ρ-ax₁ U)
                }
      ; uniq = record
        { epi-pf = λ {V} {g} {g'} pf → record
          { hty = hty pf
          ; hty₀ = hty₀ pf ⊙ rid
          ; hty₁ = hty₁ pf ⊙ rid
          }
        }
      }
      where open ecategory-aux-only ℂ
            open ℂ.peq
            open ℂ.peq-mor
            open ℂ.peq-mor-eq
    isexseq : Exℂ.is-exact-seq kp₁ kp₂ cre.ar
    isexseq = record
      { iscoeq = crepi-coeq-kp
      ; iskerpair = kppbsq
      }

    can-cov : canonical-repi freeHi.peqover kpOb/
    can-cov = record
      { crepi-hi = KP.⟨ ℂ.idar R.Hi , ℂ.idar R.Hi ⟩[ r , r ]
      ; crepi-ax₀ = KP.tr₁ r r
      ; crepi-ax₁ = KP.tr₂ r r
      }
      where open ecategory-aux-only ℂ using (r)
    module cc where
      open canonical-repi can-cov public
      tr₁ : kp₁ Exℂ.∘ ar Exℂ.~ ℂ.freepeq-mor R.%0
      tr₁ = record
        { hty = R.%0
        ; hty₀ = lidgen ridˢ
        ; hty₁ = lid
        }
        where open ecategory-aux-only ℂ
      tr₂ : kp₂ Exℂ.∘ ar Exℂ.~ ℂ.freepeq-mor R.%1
      tr₂ = record
        { hty = R.%1
        ; hty₀ = lidgen ridˢ
        ; hty₁ = lid
        }
        where open ecategory-aux-only ℂ
  -- end canonical-ex-seq



  -- standard & canonical monos

{-
  record is-Ex-monic {A B : Exℂ.Obj} (f : || Exℂ.Hom A B ||) : Set₁ where
    -- this is a bit less than the universal property of weak limits of W diagrams
    private
      module A = ℂ.peq A
      module B = ℂ.peq B
      module f = ℂ.peq-mor f
    field
      ⟨_⟩[_,_] : {X : ℂ.Obj} {gl : || ℂ.Hom X A.Lo ||} {gr : || ℂ.Hom X A.Lo ||} (h : || ℂ.Hom X B.Hi ||)
                          → f.lo ℂ.∘ gl ℂ.~ B.%0 ℂ.∘ h → f.lo ℂ.∘ gr ℂ.~ B.%1 ℂ.∘ h
                            → || ℂ.Hom X A.Hi ||
      trl : {X : ℂ.Obj} {gl : || ℂ.Hom X A.Lo ||} {gr : || ℂ.Hom X A.Lo ||} {h : || ℂ.Hom X B.Hi ||}
              (pfl : f.lo ℂ.∘ gl ℂ.~ B.%0 ℂ.∘ h) (pfr : f.lo ℂ.∘ gr ℂ.~ B.%1 ℂ.∘ h)
                → A.%0 ℂ.∘ ⟨ h ⟩[ pfl , pfr ] ℂ.~ gl
      trr : {X : ℂ.Obj} {gl : || ℂ.Hom X A.Lo ||} {gr : || ℂ.Hom X A.Lo ||} {h : || ℂ.Hom X B.Hi ||}
              (pfl : f.lo ℂ.∘ gl ℂ.~ B.%0 ℂ.∘ h) (pfr : f.lo ℂ.∘ gr ℂ.~ B.%1 ℂ.∘ h)
                → A.%1 ℂ.∘ ⟨ h ⟩[ pfl , pfr ] ℂ.~ gr


  Ex-monic-is-monic : {A B : Exℂ.Obj} {f : || Exℂ.Hom A B ||}
                         → is-Ex-monic f → Exℂ.is-monic f
  Ex-monic-is-monic {A} {B} {f} isxm = record
    { mono-pf = λ {_} {g} {g'} pf → record
              { hty = ⟨ hty pf ⟩[ hty₀ pf ˢ , hty₁ pf ˢ ]
              ; hty₀ = trl (hty₀ pf ˢ) (hty₁ pf ˢ)
              ; hty₁ = trr (hty₀ pf ˢ) (hty₁ pf ˢ)
              }
    }
    where open ecategory-aux-only ℂ
          open is-Ex-monic isxm
          open ℂ.peq
          open ℂ.peq-mor
          open ℂ.peq-mor-eq
-}

  record canonical-mono {X Y : ℂ.Obj} (loar : || ℂ.Hom X Y ||) (R : ℂ.peqOver Y) : Set₁ where
    open ecategory-aux-only ℂ
    private module R = ℂ.peqOver R
    field
      Ob/ : ℂ.peqOver X
    --private module Ob = ℂ.peqOver Ob
    Ob : Exℂ.Obj
    Ob = ℂ.mkpeq-c Ob/
    field
      isext : ℂ.is-extensional-ar Ob (ℂ.mkpeq-c R) loar
    --private module ar = ℂ.is-extensional-ar isext
    open ℂ.is-extensional-ar isext public
    field
      iswW : ℂ.is-wWlim (cmptb₀ ˢ) (cmptb₁ ˢ)
    open ℂ.is-wWlim iswW public
    ar : || Exℂ.Hom Ob (ℂ.mkpeq-c R) ||
    ar = record
      { lo = loar
      ; isext = isext
      }
    ar-monic : Exℂ.is-monic ar
    ar-monic = record
      { mono-pf = λ {_} {g} {g'} pf → record
                { hty = ⟨ lo g , hty pf , lo g' ⟩[ hty₀ pf ˢ , hty₁ pf ˢ ]
                ; hty₀ = trl (hty₀ pf ˢ) (hty₁ pf ˢ)
                ; hty₁ = trr (hty₀ pf ˢ) (hty₁ pf ˢ)
                }
      }
      where open ℂ.peq-mor
            open ℂ.peq-mor-eq


  module can-mono-constr {X Y : ℂ.Obj} (lo-cm : || ℂ.Hom X Y ||) (R : ℂ.peqOver Y) where
    private
      module R  = ℂ.peqOver R
      module wW = fwlℂ.wW-of lo-cm (ℂ.mkspan/ R.%0 R.%1) lo-cm
      cmpeq/ : ℂ.peqOver X
      cmpeq/ = record
        { Hi = wW.wWOb
        ; %0 = wW.πl
        ; %1 = wW.πr
        ; ispeq = record
                { isρ = record
                { ρ = wW.⟨ idar X , R.ρ ∘ lo-cm , idar X ⟩[ ρpfl , ρpfr ]
                ; ρ-ax₀ = wW.trl ρpfl ρpfr
                ; ρ-ax₁ = wW.trr ρpfl ρpfr
                }
                ; isσ = record
                { σ = wW.⟨ wW.πr , R.σ ∘ wW.πc , wW.πl ⟩[ σpfl , σpfr ]
                ; σ-ax₀ = wW.trl σpfl σpfr
                ; σ-ax₁ = wW.trr σpfl σpfr
                }
                ; τwpb = τwpb
                ; iswτ = record
                { τ = wW.⟨ wW.πl ∘ τwpb.wπ/₁ , R.τ ∘ τmed , wW.πr ∘ τwpb.wπ/₂ ⟩[ τpfl , τpfr ]
                ; τ-ax₀ = wW.trl τpfl τpfr
                ; τ-ax₁ = wW.trr τpfl τpfr
                }
                }
        }
        where open ecategory-aux-only ℂ
              open ℂ
              module Rτ = ℂ.wpullback-of-not R.τwpb
              ρpfl : lo-cm ∘ ℂ.idar X ~ R.%0 ∘ R.ρ ∘ lo-cm
              ρpfl = lidggˢ rid R.ρ-ax₀ ⊙ assˢ
              ρpfr : lo-cm ∘ ℂ.idar X ~ R.%1 ∘ R.ρ ∘ lo-cm
              ρpfr = lidggˢ rid R.ρ-ax₁ ⊙ assˢ

              σpfl : lo-cm ∘ wW.πr ~ R.%0 ∘ R.σ ∘ wW.πc
              σpfl = wW.sqpfr ⊙ ∘e r (R.σ-ax₀ ˢ) ⊙ assˢ
              σpfr : lo-cm ∘ wW.πl ~ R.%1 ∘ R.σ ∘ wW.πc
              σpfr = wW.sqpfl ⊙ ∘e r (R.σ-ax₁ ˢ) ⊙ assˢ

              τwpb : ℂ.wpullback-of wW.πr wW.πl
              τwpb = fwlℂ.wpb-of wW.πr wW.πl
              module τwpb = ℂ.wpullback-of τwpb
              τaux-pf = ~proof
                R.%1 ∘ wW.πc ∘ τwpb.wπ/₁       ~[ ass ⊙ ∘e r (wW.sqpfr ˢ) ⊙ assˢ ] /
                lo-cm ∘ wW.πr ∘ τwpb.wπ/₁      ~[ ∘e τwpb.w×/sqpf r ] /
                lo-cm ∘ wW.πl ∘ τwpb.wπ/₂      ~[ ass ⊙ ∘e r wW.sqpfl ⊙ assˢ ]∎
                R.%0 ∘ wW.πc ∘ τwpb.wπ/₂ ∎
              τmed : || ℂ.Hom τwpb.ul Rτ.ul ||
              τmed = Rτ.w⟨ wW.πc ∘ τwpb.wπ/₁ , wW.πc ∘ τwpb.wπ/₂ ⟩[ τaux-pf ]
              τpfl = ~proof
                lo-cm ∘ wW.πl ∘ τwpb.wπ/₁                                       ~[ ass ⊙ ∘e r wW.sqpfl ⊙ assˢ ] /
                R.%0 ∘ wW.πc ∘ τwpb.wπ/₁                                        ~[ ∘e (Rτ.w×/tr₁ τaux-pf ˢ) r ] /
                R.%0 ∘ Rτ.wπ/₁ ∘ τmed    ~[ ass ⊙ ∘e r (R.τ-ax₀ ˢ) ⊙ assˢ ]∎
                R.%0 ∘ R.τ ∘ τmed ∎
              τpfr = ~proof
                lo-cm ∘ wW.πr ∘ τwpb.wπ/₂                                       ~[ ass ⊙ ∘e r wW.sqpfr ⊙ assˢ ] /
                R.%1 ∘ wW.πc ∘ τwpb.wπ/₂                                        ~[ ∘e (Rτ.w×/tr₂ τaux-pf ˢ) r ] /
                R.%1 ∘ Rτ.wπ/₂ ∘ τmed    ~[ ass ⊙ ∘e r (R.τ-ax₁ ˢ) ⊙ assˢ ]∎
                R.%1 ∘ R.τ ∘ τmed ∎
    -- end private
    
    cmar-data : canonical-mono lo-cm R
    cmar-data = record
      { Ob/ = cmpeq/
      ; isext = record
        { hi = wW.πc
        ; cmptb₀ = wW.sqpfl ˢ
        ; cmptb₁ = wW.sqpfr ˢ
        }
      ; iswW = record
        { ⟨_,_,_⟩[_,_] = wW.⟨_,_,_⟩[_,_]
        ; trl = wW.trl
        ; trc = wW.trc
        ; trr = wW.trr
        }
      }
      where open ecategory-aux-only ℂ
{-
    cmpeq : ℂ.peq
    cmpeq = ℂ.mkpeq-c cmpeq/

    cmar : ℂ.peq-mor cmpeq (ℂ.mkpeq-c R)
    cmar = record
      { lo = lo-cm
      ; isext = record
        { hi = wW.πc
        ; cmptb₀ = wW.sqpfl ˢ
        ; cmptb₁ = wW.sqpfr ˢ
        }
      }
      where open ecategory-aux-only ℂ

    cmar-is-Ex-monic : is-Ex-monic cmar
    cmar-is-Ex-monic = record
      { ⟨_⟩[_,_] = λ {_} {gl} {gr} h → wW.⟨ gl , h , gr ⟩[_,_]
      ; trl = wW.trl
      ; trr = wW.trr
      }
-}
  -- end can-mono-constr


  can-mono-over : {X Y : ℂ.Obj} (loar : || ℂ.Hom X Y ||) (R : ℂ.peqOver Y)
                       → canonical-mono loar R
  can-mono-over loar R = cmar-data
                         where open can-mono-constr loar R

{-
  module can-mono {X Y : ℂ.Obj} (loar : || ℂ.Hom X Y ||) (R : ℂ.peqOver Y) where
    open can-mono-constr loar R
    open canonical-mono cmar-data public
-}


  record is-Ex-monic-sp {O1 O2 : Exℂ.Obj} (sp/ : Exℂ.span/ O1 O2) : Set₁ where
    private
      module O1 = ℂ.peq O1
      module O2 = ℂ.peq O2
      module sp = Exℂ.span/ sp/
      module O12 = ℂ.peq sp.O12
      module a₁ = ℂ.peq-mor sp.a1
      module a₂ = ℂ.peq-mor sp.a2
    field
      ⟨_,_,_,_⟩[_,_,_,_] : {X : ℂ.Obj} (g₁ : || ℂ.Hom X O12.Lo ||) (h₁ : || ℂ.Hom X O1.Hi ||)
                           (h₂ : || ℂ.Hom X O2.Hi ||) (g₂ : || ℂ.Hom X O12.Lo ||)
                             → a₁.lo ℂ.∘ g₁ ℂ.~ O1.%0 ℂ.∘ h₁ → a₁.lo ℂ.∘ g₂ ℂ.~ O1.%1 ℂ.∘ h₁
                               → a₂.lo ℂ.∘ g₁ ℂ.~ O2.%0 ℂ.∘ h₂ → a₂.lo ℂ.∘ g₂ ℂ.~ O2.%1 ℂ.∘ h₂
                                 → || ℂ.Hom X O12.Hi ||
      trl₀ : {X : ℂ.Obj} {g₁ g₂ : || ℂ.Hom X O12.Lo ||} {h₁ : || ℂ.Hom X O1.Hi ||} {h₂ : || ℂ.Hom X O2.Hi ||}
             (pf₁₁ : a₁.lo ℂ.∘ g₁ ℂ.~ O1.%0 ℂ.∘ h₁) (pf₁₂ : a₁.lo ℂ.∘ g₂ ℂ.~ O1.%1 ℂ.∘ h₁)
             (pf₂₁ : a₂.lo ℂ.∘ g₁ ℂ.~ O2.%0 ℂ.∘ h₂) (pf₂₂ : a₂.lo ℂ.∘ g₂ ℂ.~ O2.%1 ℂ.∘ h₂)
                → O12.%0 ℂ.∘ ⟨ g₁ , h₁ , h₂ , g₂ ⟩[ pf₁₁ , pf₁₂ , pf₂₁ , pf₂₂ ] ℂ.~ g₁
      trl₁ : {X : ℂ.Obj} {g₁ g₂ : || ℂ.Hom X O12.Lo ||} {h₁ : || ℂ.Hom X O1.Hi ||} {h₂ : || ℂ.Hom X O2.Hi ||}
             (pf₁₁ : a₁.lo ℂ.∘ g₁ ℂ.~ O1.%0 ℂ.∘ h₁) (pf₁₂ : a₁.lo ℂ.∘ g₂ ℂ.~ O1.%1 ℂ.∘ h₁)
             (pf₂₁ : a₂.lo ℂ.∘ g₁ ℂ.~ O2.%0 ℂ.∘ h₂) (pf₂₂ : a₂.lo ℂ.∘ g₂ ℂ.~ O2.%1 ℂ.∘ h₂)
                → O12.%1 ℂ.∘ ⟨ g₁ , h₁ , h₂ , g₂ ⟩[ pf₁₁ , pf₁₂ , pf₂₁ , pf₂₂ ] ℂ.~ g₂
      trh₁ : {X : ℂ.Obj} {g₁ g₂ : || ℂ.Hom X O12.Lo ||} {h₁ : || ℂ.Hom X O1.Hi ||} {h₂ : || ℂ.Hom X O2.Hi ||}
             (pf₁₁ : a₁.lo ℂ.∘ g₁ ℂ.~ O1.%0 ℂ.∘ h₁) (pf₁₂ : a₁.lo ℂ.∘ g₂ ℂ.~ O1.%1 ℂ.∘ h₁)
             (pf₂₁ : a₂.lo ℂ.∘ g₁ ℂ.~ O2.%0 ℂ.∘ h₂) (pf₂₂ : a₂.lo ℂ.∘ g₂ ℂ.~ O2.%1 ℂ.∘ h₂)
               → a₁.hi ℂ.∘ ⟨ g₁ , h₁ , h₂ , g₂ ⟩[ pf₁₁ , pf₁₂ , pf₂₁ , pf₂₂ ] ℂ.~ h₁
      trh₂ : {X : ℂ.Obj} {g₁ g₂ : || ℂ.Hom X O12.Lo ||} {h₁ : || ℂ.Hom X O1.Hi ||} {h₂ : || ℂ.Hom X O2.Hi ||}
             (pf₁₁ : a₁.lo ℂ.∘ g₁ ℂ.~ O1.%0 ℂ.∘ h₁) (pf₁₂ : a₁.lo ℂ.∘ g₂ ℂ.~ O1.%1 ℂ.∘ h₁)
             (pf₂₁ : a₂.lo ℂ.∘ g₁ ℂ.~ O2.%0 ℂ.∘ h₂) (pf₂₂ : a₂.lo ℂ.∘ g₂ ℂ.~ O2.%1 ℂ.∘ h₂)
                → a₂.hi ℂ.∘ ⟨ g₁ , h₁ , h₂ , g₂ ⟩[ pf₁₁ , pf₁₂ , pf₂₁ , pf₂₂ ] ℂ.~ h₂


  module Ex-monic-sp-is-jm {O1 O2 : Exℂ.Obj} (sp/ : Exℂ.span/ O1 O2) (isxm : is-Ex-monic-sp sp/) where
    open ecategory-aux ℂ
    private
      module O1 = ℂ.peq O1
      module O2 =  ℂ.peq O2
      module sp where
        open Exℂ.span/ sp/ public
        open is-Ex-monic-sp isxm public
      module O12 =  ℂ.peq sp.O12
      module a₁ = ℂ.peq-mor sp.a1
      module a₂ = ℂ.peq-mor sp.a2

    isjm-pf : {C : Exℂ.Obj} (h h' : || Exℂ.Hom C sp.O12 ||)
                 → sp.a1 Exℂ.∘  h Exℂ.~ sp.a1 Exℂ.∘ h' → sp.a2 Exℂ.∘ h Exℂ.~ sp.a2 Exℂ.∘ h'
                   → h Exℂ.~ h'
    isjm-pf {C} h h' pf₁ pf₂ = record
      { hty = sp.⟨ h.lo , pf₁.hty , pf₂.hty , h'.lo ⟩[ pf₁.hty₀ ˢ , pf₁.hty₁ ˢ , pf₂.hty₀ ˢ , pf₂.hty₁ ˢ ]
      ; hty₀ = sp.trl₀ (pf₁.hty₀ ˢ) (pf₁.hty₁ ˢ) (pf₂.hty₀ ˢ) (pf₂.hty₁ ˢ)
      ; hty₁ = sp.trl₁ (pf₁.hty₀ ˢ) (pf₁.hty₁ ˢ) (pf₂.hty₀ ˢ) (pf₂.hty₁ ˢ)
      }
      where module h = ℂ.peq-mor h
            module h' = ℂ.peq-mor h'
            module pf₁ = ℂ.peq-mor-eq pf₁
            module pf₂ = ℂ.peq-mor-eq pf₂
    
  -- end Ex-monic-sp-is-jm
  
  Ex-monic-sp-is-jm : {O1 O2 : Exℂ.Obj} {sp/ : Exℂ.span/ O1 O2}
                          → is-Ex-monic-sp sp/ → Exℂ.is-jointly-monic/ sp/
  Ex-monic-sp-is-jm {O1} {O2} {sp/} isxm = record
    { jm-pf = λ {C} {h} {h'} → isjm-pf {C} h h'
    }
    where open Ex-monic-sp-is-jm sp/ isxm
    

  module canonical-mono-sp {O1 O2 : ℂ.Obj} (R/ : ℂ.peqOver O1) (S/ : ℂ.peqOver O2)
                           (sp/ : ℂ.span/ O1 O2)
                           where
    open ecategory ℂ
    open comm-shapes ℂ
    --open ecategory-aux-only ℂ
    private
      R S : Exℂ.Obj
      R = ℂ.mkpeq-c R/
      S = ℂ.mkpeq-c S/
      module R  = ℂ.peq R
      module S  = ℂ.peq S
      module Rτ = ℂ.wpullback-of-not R.τwpb
      module Sτ = ℂ.wpullback-of-not S.τwpb
      module sp = ℂ.span/ sp/
      module imgR where
        open fwlℂ.wW-of sp.a1 (ℂ.mkspan/ R.%0 R.%1) sp.a1 public
        πlr : span/ sp.O12 sp.O12
        πlr = mkspan/ πl πr
      module imgS where
        open fwlℂ.wW-of sp.a2 (ℂ.mkspan/ S.%0 S.%1) sp.a2 public
        πlr : span/ sp.O12 sp.O12
        πlr = mkspan/ πl πr
      module pbHi = ℂ.wbow-of (fwlℂ.wbw-of imgR.πlr imgS.πlr)
      pb%0 pb%1 : || ℂ.Hom pbHi.Ob sp.O12 ||
      pb%0 = imgR.πl ∘ pbHi.wπ//₁ -- ~[ pbHi.sqpf₁ ] imgS.πl ∘ pbHi.wπ//₂
      pb%1 = imgR.πr ∘ pbHi.wπ//₁ -- ~[ pbHi.sqpf₂ ] imgS.πr ∘ pbHi.wπ//₂

      cmsp-ρ : ℂ.is-reflexive pb%0 pb%1
      cmsp-ρ = record
              { ρ = pbHi.⟨ imgR.⟨ ℂ.idar sp.O12 , R.ρ ∘ sp.a1 , ℂ.idar sp.O12
                                ⟩[ ρimgR₀ , ρimgR₁ ]
                         , imgS.⟨ ℂ.idar sp.O12 , S.ρ ∘ sp.a2 , ℂ.idar sp.O12
                                ⟩[ ρimgS₀ , ρimgS₁ ]
                         ⟩[ ρpbHi₁ , ρpbHi₂ ]
              ; ρ-ax₀ = assˢ ⊙ ∘e (pbHi.tr₁ ρpbHi₁ ρpbHi₂) r ⊙ imgR.trl ρimgR₀ ρimgR₁
              ; ρ-ax₁ = assˢ ⊙ ∘e (pbHi.tr₁ ρpbHi₁ ρpbHi₂) r ⊙ imgR.trr ρimgR₀ ρimgR₁
              }
              where open ecategory-aux-only ℂ
                    ρimgR₀ = sp.a1 ∘ ℂ.idar sp.O12 ~[ lidggˢ rid R.ρ-ax₀ ⊙ assˢ ] R.%0 ∘ R.ρ ∘ sp.a1
                    ρimgR₁ = sp.a1 ∘ ℂ.idar sp.O12 ~[ lidggˢ rid R.ρ-ax₁ ⊙ assˢ ] R.%1 ∘ R.ρ ∘ sp.a1
                    ρimgS₀ = sp.a2 ∘ ℂ.idar sp.O12 ~[ lidggˢ rid S.ρ-ax₀ ⊙ assˢ ] S.%0 ∘ S.ρ ∘ sp.a2
                    ρimgS₁ = sp.a2 ∘ ℂ.idar sp.O12 ~[ lidggˢ rid S.ρ-ax₁ ⊙ assˢ ] S.%1 ∘ S.ρ ∘ sp.a2
                    ρpbHi₁ = imgR.πl ∘ imgR.⟨ ℂ.idar sp.O12 , R.ρ ∘ sp.a1 , ℂ.idar sp.O12 ⟩[ ρimgR₀ , ρimgR₁ ]
                             ~[ imgR.trl ρimgR₀ ρimgR₁ ⊙ imgS.trl ρimgS₀ ρimgS₁ ˢ ]
                             imgS.πl ∘ imgS.⟨ ℂ.idar sp.O12 , S.ρ ∘ sp.a2 , ℂ.idar sp.O12 ⟩[ ρimgS₀ , ρimgS₁ ]
                    ρpbHi₂ = imgR.πr ∘ imgR.⟨ ℂ.idar sp.O12 , R.ρ ∘ sp.a1 , ℂ.idar sp.O12 ⟩[ ρimgR₀ , ρimgR₁ ]
                             ~[ imgR.trr ρimgR₀ ρimgR₁ ⊙ imgS.trr ρimgS₀ ρimgS₁ ˢ ]
                             imgS.πr ∘ imgS.⟨ ℂ.idar sp.O12 , S.ρ ∘ sp.a2 , ℂ.idar sp.O12 ⟩[ ρimgS₀ , ρimgS₁ ]

      cmsp-σ : ℂ.is-symmetric pb%0 pb%1
      cmsp-σ = record
              { σ = pbHi.⟨ imgR.⟨ pb%1 , R.σ ∘ imgR.πc ∘ pbHi.wπ//₁ , pb%0
                                ⟩[ σimgR₀ , σimgR₁ ]
                         ,  imgS.⟨ pb%1 , S.σ ∘ imgS.πc ∘ pbHi.wπ//₂ , pb%0
                                 ⟩[ σimgS₀ , σimgS₁ ]
                         ⟩[ σpbHi₁ , σpbHi₂ ]
              ; σ-ax₀ = assˢ ⊙ ∘e (pbHi.tr₁ σpbHi₁ σpbHi₂) r ⊙ imgR.trl σimgR₀ σimgR₁
              ; σ-ax₁ = assˢ ⊙ ∘e (pbHi.tr₁ σpbHi₁ σpbHi₂) r ⊙ imgR.trr σimgR₀ σimgR₁
              }
              where open ecategory-aux-only ℂ
                    σimgR₀ = ~proof sp.a1 ∘ pb%1                             ~[ ass ] /
                                    (sp.a1 ∘ imgR.πr) ∘ pbHi.wπ//₁           ~[ ∘e r imgR.sqpfr ⊙ assˢ ] /
                                    R.%1 ∘ imgR.πc ∘ pbHi.wπ//₁                ~[ ∘e r (R.σ-ax₀ ˢ) ⊙ assˢ ]∎
                                    R.%0 ∘ R.σ ∘ imgR.πc ∘ pbHi.wπ//₁ ∎
                    σimgR₁ = ~proof sp.a1 ∘ pb%0                             ~[ ass ] /
                                    (sp.a1 ∘ imgR.πl) ∘ pbHi.wπ//₁           ~[ ∘e r imgR.sqpfl ⊙ assˢ ] /
                                    R.%0 ∘ imgR.πc ∘ pbHi.wπ//₁                ~[ ∘e r (R.σ-ax₁ ˢ) ⊙ assˢ ]∎
                                    R.%1 ∘ R.σ ∘ imgR.πc ∘ pbHi.wπ//₁ ∎
                    σimgS₀ = ~proof sp.a2 ∘ pb%1                              ~[ ∘e pbHi.sqpf₂ r ⊙ ass ] /
                                    (sp.a2 ∘ imgS.πr) ∘ pbHi.wπ//₂            ~[ ∘e r imgS.sqpfr ⊙ assˢ ] /
                                    S.%1 ∘ imgS.πc ∘ pbHi.wπ//₂                 ~[ ∘e r (S.σ-ax₀ ˢ) ⊙ assˢ ]∎
                                    S.%0 ∘ S.σ ∘ imgS.πc ∘ pbHi.wπ//₂ ∎
                    σimgS₁ = ~proof sp.a2 ∘ pb%0                              ~[ ∘e pbHi.sqpf₁ r ⊙ ass ] /
                                    (sp.a2 ∘ imgS.πl) ∘ pbHi.wπ//₂            ~[ ∘e r imgS.sqpfl ⊙ assˢ ] /
                                    S.%0 ∘ imgS.πc ∘ pbHi.wπ//₂                 ~[ ∘e r (S.σ-ax₁ ˢ) ⊙ assˢ ]∎
                                    S.%1 ∘ S.σ ∘ imgS.πc ∘ pbHi.wπ//₂ ∎
                    σpbHi₁ = imgR.πl ∘ imgR.⟨ pb%1 , R.σ ∘ imgR.πc ∘ pbHi.wπ//₁ , pb%0 ⟩[ σimgR₀ , σimgR₁ ]
                             ~[ imgR.trl σimgR₀ σimgR₁ ⊙ imgS.trl σimgS₀ σimgS₁ ˢ ]
                             imgS.πl ∘ imgS.⟨ pb%1 , S.σ ∘ imgS.πc ∘ pbHi.wπ//₂ , pb%0 ⟩[ σimgS₀ , σimgS₁ ]
                    σpbHi₂ = imgR.πr ∘ imgR.⟨ pb%1 , R.σ ∘ imgR.πc ∘ pbHi.wπ//₁ , pb%0 ⟩[ σimgR₀ , σimgR₁ ]
                             ~[ imgR.trr σimgR₀ σimgR₁ ⊙ imgS.trr σimgS₀ σimgS₁ ˢ ]
                             imgS.πr ∘ imgS.⟨ pb%1 , S.σ ∘ imgS.πc ∘ pbHi.wπ//₂ , pb%0 ⟩[ σimgS₀ , σimgS₁ ]

      cmsp-τwpb : ℂ.wpullback-of pb%1 pb%0
      cmsp-τwpb = fwlℂ.wpb-of pb%1 pb%0

      cmsp-wτ : ℂ.is-transitive/wpb cmsp-τwpb
      cmsp-wτ = record
               { τ = pbHi.⟨ imgR.⟨ pb%0 ∘ pbwτ.wπ/₁ , R.τ ∘ τRar , pb%1 ∘ pbwτ.wπ/₂
                                 ⟩[ τimgR₀ , τimgR₁ ]
                          , imgS.⟨ pb%0 ∘ pbwτ.wπ/₁ , S.τ ∘ τSar , pb%1 ∘ pbwτ.wπ/₂
                                 ⟩[ τimgS₀ , τimgS₁ ]
                          ⟩[ τpbHi₀ , τpbHi₁ ]
               ; τ-ax₀ = assˢ ⊙ ∘e (pbHi.tr₁ τpbHi₀ τpbHi₁) r ⊙ imgR.trl τimgR₀ τimgR₁
               ; τ-ax₁ = assˢ ⊙ ∘e (pbHi.tr₁ τpbHi₀ τpbHi₁) r ⊙ imgR.trr τimgR₀ τimgR₁
               }
               where open ecategory-aux-only ℂ
                     pbwτ : ℂ.wpullback-of pb%1 pb%0
                     pbwτ = fwlℂ.wpb-of pb%1 pb%0
                     module pbwτ = ℂ.wpullback-of-not pbwτ
                     τRarpf = ~proof R.%1 ∘ imgR.πc ∘ pbHi.wπ//₁ ∘ pbwτ.wπ/₁      ~[ ass ⊙ ∘e r (imgR.sqpfr ˢ) ⊙ assˢ ] /
                                     sp.a1 ∘ imgR.πr ∘ pbHi.wπ//₁ ∘ pbwτ.wπ/₁   ~[ ∘e (ass ⊙ pbwτ.w×/sqpf ⊙ assˢ) r ] /
                                     sp.a1 ∘ imgR.πl ∘ pbHi.wπ//₁ ∘ pbwτ.wπ/₂   ~[ ass ⊙ ∘e r imgR.sqpfl ⊙ assˢ ]∎
                                     R.%0 ∘ imgR.πc ∘ pbHi.wπ//₁ ∘ pbwτ.wπ/₂ ∎
                     τRar : || ℂ.Hom pbwτ.ul Rτ.ul ||
                     τRar = Rτ.w⟨ imgR.πc ∘ pbHi.wπ//₁ ∘ pbwτ.wπ/₁ , imgR.πc ∘ pbHi.wπ//₁ ∘ pbwτ.wπ/₂ ⟩[ τRarpf ]
                     τimgR₀ = ~proof sp.a1 ∘ pb%0 ∘ pbwτ.wπ/₁                 ~[ ∘e assˢ r ⊙ ass ⊙ ∘e r imgR.sqpfl ⊙ assˢ ] /
                                     R.%0 ∘ imgR.πc ∘ pbHi.wπ//₁ ∘ pbwτ.wπ/₁    ~[ ∘e (Rτ.w×/tr₁ τRarpf ˢ) r ] /
                                     R.%0 ∘ Rτ.wπ/₁ ∘ τRar                     ~[ ass ⊙ ∘e r (R.τ-ax₀ ˢ) ⊙ assˢ ]∎
                                     R.%0 ∘ R.τ ∘ τRar ∎
                     τimgR₁ = ~proof sp.a1 ∘ pb%1 ∘ pbwτ.wπ/₂                 ~[ ∘e assˢ r ⊙ ass ⊙ ∘e r imgR.sqpfr ⊙ assˢ ] /
                                     R.%1 ∘ imgR.πc ∘ pbHi.wπ//₁ ∘ pbwτ.wπ/₂    ~[ ∘e (Rτ.w×/tr₂ τRarpf ˢ) r ] /
                                     R.%1 ∘ Rτ.wπ/₂ ∘ τRar                     ~[ ass ⊙ ∘e r (R.τ-ax₁ ˢ) ⊙ assˢ ]∎
                                     R.%1 ∘ R.τ ∘ τRar ∎
                     τSarpf = ~proof S.%1 ∘ imgS.πc ∘ pbHi.wπ//₂ ∘ pbwτ.wπ/₁        ~[ ass ⊙ ∘e r (imgS.sqpfr ˢ) ⊙ assˢ ] /
                                     sp.a2 ∘ imgS.πr ∘ pbHi.wπ//₂ ∘ pbwτ.wπ/₁     ~[ ∘e (ass ⊙ ∘e r (pbHi.sqpf₂ ˢ)) r ] /
                                     sp.a2 ∘ (imgR.πr ∘ pbHi.wπ//₁) ∘ pbwτ.wπ/₁   ~[ ∘e pbwτ.w×/sqpf r ] /
                                     sp.a2 ∘ (imgR.πl ∘ pbHi.wπ//₁) ∘ pbwτ.wπ/₂   ~[ ∘e (∘e r pbHi.sqpf₁ ⊙ assˢ) r ] /
                                     sp.a2 ∘ imgS.πl ∘ pbHi.wπ//₂ ∘ pbwτ.wπ/₂     ~[ ass ⊙ ∘e r imgS.sqpfl ⊙ assˢ ]∎
                                     S.%0 ∘ imgS.πc ∘ pbHi.wπ//₂ ∘ pbwτ.wπ/₂ ∎
                     τSar : || ℂ.Hom pbwτ.ul Sτ.ul ||
                     τSar = Sτ.w⟨ imgS.πc ∘ pbHi.wπ//₂ ∘ pbwτ.wπ/₁ , imgS.πc ∘ pbHi.wπ//₂ ∘ pbwτ.wπ/₂ ⟩[ τSarpf ]
                     τimgS₀ = ~proof sp.a2 ∘ pb%0 ∘ pbwτ.wπ/₁                  ~[ ∘e (∘e r pbHi.sqpf₁ ⊙ assˢ) r ] /
                                     sp.a2 ∘ imgS.πl ∘ pbHi.wπ//₂ ∘ pbwτ.wπ/₁  ~[ ass ⊙ ∘e r imgS.sqpfl ⊙ assˢ ] /
                                     S.%0 ∘ imgS.πc ∘ pbHi.wπ//₂ ∘ pbwτ.wπ/₁     ~[ ∘e (Sτ.w×/tr₁ τSarpf ˢ) r ] /
                                     S.%0 ∘ Sτ.wπ/₁ ∘ τSar                      ~[ ass ⊙ ∘e r (S.τ-ax₀ ˢ) ⊙ assˢ ]∎
                                     S.%0 ∘ S.τ ∘ τSar ∎
                     τimgS₁ = ~proof sp.a2 ∘ pb%1 ∘ pbwτ.wπ/₂                 ~[ ∘e (∘e r pbHi.sqpf₂ ⊙ assˢ) r ] /
                                     sp.a2 ∘ imgS.πr ∘ pbHi.wπ//₂ ∘ pbwτ.wπ/₂  ~[ ass ⊙ ∘e r imgS.sqpfr ⊙ assˢ ] /
                                     S.%1 ∘ imgS.πc ∘ pbHi.wπ//₂ ∘ pbwτ.wπ/₂     ~[ ∘e (Sτ.w×/tr₂ τSarpf ˢ) r ] /
                                     S.%1 ∘ Sτ.wπ/₂ ∘ τSar                      ~[ ass ⊙ ∘e r (S.τ-ax₁ ˢ) ⊙ assˢ ]∎
                                     S.%1 ∘ S.τ ∘ τSar ∎
                     τpbHi₀ = imgR.πl ∘ imgR.⟨ pb%0 ∘ pbwτ.wπ/₁ , R.τ ∘ τRar , pb%1 ∘ pbwτ.wπ/₂ ⟩[ τimgR₀ , τimgR₁ ]
                              ~[ imgR.trl τimgR₀ τimgR₁ ⊙ imgS.trl τimgS₀ τimgS₁ ˢ ]
                              imgS.πl ∘ imgS.⟨ pb%0 ∘ pbwτ.wπ/₁ , S.τ ∘ τSar , pb%1 ∘ pbwτ.wπ/₂ ⟩[ τimgS₀ , τimgS₁ ]
                     τpbHi₁ = imgR.πr ∘ imgR.⟨ pb%0 ∘ pbwτ.wπ/₁ , R.τ ∘ τRar , pb%1 ∘ pbwτ.wπ/₂ ⟩[ τimgR₀ , τimgR₁ ]
                              ~[ imgR.trr τimgR₀ τimgR₁ ⊙ imgS.trr τimgS₀ τimgS₁ ˢ ]
                              imgS.πr ∘ imgS.⟨ pb%0 ∘ pbwτ.wπ/₁ , S.τ ∘ τSar , pb%1 ∘ pbwτ.wπ/₂ ⟩[ τimgS₀ , τimgS₁ ]


      cmsp-ob/ : ℂ.peqOver sp.O12
      cmsp-ob/ = record
        { Hi = pbHi.Ob
        ; %0 = pb%0
        ; %1 = pb%1
        ; ispeq = record
          { isρ = cmsp-ρ
          ; isσ = cmsp-σ
          ; iswτ = cmsp-wτ
          }
        }

      cmsp-ob : Exℂ.Obj
      cmsp-ob = ℂ.mkpeq-c cmsp-ob/

      cmsp-a₁ : || Exℂ.Hom cmsp-ob R ||
      cmsp-a₁ = record
              { lo = sp.a1
              ; isext = record
                { hi = imgR.πc ∘ pbHi.wπ//₁
                ; cmptb₀ = ass ⊙ ∘e r (imgR.sqpfl  ˢ) ⊙ assˢ
                ; cmptb₁ = ass ⊙ ∘e r (imgR.sqpfr  ˢ) ⊙ assˢ
                }
              }
              where open ecategory-aux-only ℂ
      cmsp-a₂ : || Exℂ.Hom cmsp-ob S ||
      cmsp-a₂ = record
              { lo = sp.a2
              ; isext = record
                { hi = imgS.πc ∘ pbHi.wπ//₂
                ; cmptb₀ = ass ⊙ ∘e r (imgS.sqpfl  ˢ) ⊙ assˢ ⊙ ∘e (pbHi.sqpf₁ ˢ) r
                ; cmptb₁ = ass ⊙ ∘e r (imgS.sqpfr  ˢ) ⊙ assˢ ⊙ ∘e (pbHi.sqpf₂ ˢ) r
                }
              }
              where open ecategory-aux-only ℂ
    -- end private
    
    cmsp : Exℂ.span/ R S
    cmsp = Exℂ.mkspan/ cmsp-a₁ cmsp-a₂
    private
      module cmsp = Exℂ.span/ cmsp
      module cmob = ℂ.peq cmsp.O12
      module cm₁ = ℂ.peq-mor cmsp.a1
      module cm₂ = ℂ.peq-mor cmsp.a2


    cmsp-is-Ex-monic : is-Ex-monic-sp cmsp
    cmsp-is-Ex-monic = record
      { ⟨_,_,_,_⟩[_,_,_,_] = λ g₁ h₁ h₂ g₂ pf₁₁ pf₁₂ pf₂₁ pf₂₂ →
                           pbHi.⟨ imgR.⟨ g₁ , h₁ , g₂ ⟩[ pf₁₁ , pf₁₂ ]
                                , imgS.⟨ g₁ , h₂ , g₂ ⟩[ pf₂₁ , pf₂₂ ]
                                ⟩[ un₁ pf₁₁ pf₁₂ pf₂₁ pf₂₂ , un₂ pf₁₁ pf₁₂ pf₂₁ pf₂₂ ]
      ; trl₀ = λ pf₁₁ pf₁₂ pf₂₁ pf₂₂ →
             assˢ ⊙ ∘e (pbHi.tr₁ (un₁ pf₁₁ pf₁₂ pf₂₁ pf₂₂) (un₂ pf₁₁ pf₁₂ pf₂₁ pf₂₂)) r
             ⊙ imgR.trl pf₁₁ pf₁₂
      ; trl₁ = λ pf₁₁ pf₁₂ pf₂₁ pf₂₂ →
             assˢ ⊙ ∘e (pbHi.tr₁ (un₁ pf₁₁ pf₁₂ pf₂₁ pf₂₂) (un₂ pf₁₁ pf₁₂ pf₂₁ pf₂₂)) r
             ⊙ imgR.trr pf₁₁ pf₁₂
      ; trh₁ = λ pf₁₁ pf₁₂ pf₂₁ pf₂₂ →
             assˢ ⊙ ∘e (pbHi.tr₁ (un₁ pf₁₁ pf₁₂ pf₂₁ pf₂₂) (un₂ pf₁₁ pf₁₂ pf₂₁ pf₂₂)) r
             ⊙ imgR.trc pf₁₁ pf₁₂
      ; trh₂ = λ pf₁₁ pf₁₂ pf₂₁ pf₂₂ →
             assˢ ⊙ ∘e (pbHi.tr₂ (un₁ pf₁₁ pf₁₂ pf₂₁ pf₂₂) (un₂ pf₁₁ pf₁₂ pf₂₁ pf₂₂)) r
             ⊙ imgS.trc pf₂₁ pf₂₂
      }
      where open ecategory-aux-only ℂ
            un₁ : {X : Obj} {g₁ g₂ : || Hom X cmob.Lo ||}
                  {h₁ : || Hom X R.Hi ||} {h₂ : || Hom X S.Hi ||}
                  (pf₁₁ : cm₁.lo ∘ g₁ ~ R.%0 ∘ h₁) (pf₁₂ : cm₁.lo ∘ g₂ ~ R.%1 ∘ h₁)
                  (pf₂₁ : cm₂.lo ∘ g₁ ~ S.%0 ∘ h₂) (pf₂₂ : cm₂.lo ∘ g₂ ~ S.%1 ∘ h₂)
                    → imgR.πl ∘ imgR.⟨ g₁ , h₁ , g₂ ⟩[ pf₁₁ , pf₁₂ ]
                                ~ imgS.πl ∘ imgS.⟨ g₁ , h₂ , g₂ ⟩[ pf₂₁ , pf₂₂ ]
            un₁ pf₁₁ pf₁₂ pf₂₁ pf₂₂ = imgR.trl pf₁₁ pf₁₂ ⊙ imgS.trl pf₂₁ pf₂₂ ˢ
            un₂ : {X : Obj} {g₁ g₂ : || Hom X cmob.Lo ||}
                  {h₁ : || Hom X R.Hi ||} {h₂ : || Hom X S.Hi ||}
                  (pf₁₁ : cm₁.lo ∘ g₁ ~ R.%0 ∘ h₁) (pf₁₂ : cm₁.lo ∘ g₂ ~ R.%1 ∘ h₁)
                  (pf₂₁ : cm₂.lo ∘ g₁ ~ S.%0 ∘ h₂) (pf₂₂ : cm₂.lo ∘ g₂ ~ S.%1 ∘ h₂)
                    → imgR.πr ∘ imgR.⟨ g₁ , h₁ , g₂ ⟩[ pf₁₁ , pf₁₂ ]
                                ~ imgS.πr ∘ imgS.⟨ g₁ , h₂ , g₂ ⟩[ pf₂₁ , pf₂₂ ]
            un₂ pf₁₁ pf₁₂ pf₂₁ pf₂₂ = imgR.trr pf₁₁ pf₁₂ ⊙ imgS.trr pf₂₁ pf₂₂ ˢ

    cmsp-is-jm/ : Exℂ.is-jointly-monic/ cmsp
    cmsp-is-jm/ = Ex-monic-sp-is-jm cmsp-is-Ex-monic
  -- end canonical-mono-sp

-- end can-epi&mono-defs
