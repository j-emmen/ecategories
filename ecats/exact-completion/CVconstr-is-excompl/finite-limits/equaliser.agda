
{-# OPTIONS --without-K #-}

module ecats.exact-completion.CVconstr-is-excompl.finite-limits.equaliser where

open import ecats.basic-defs.ecat-def&not
open import ecats.basic-defs.commut-shapes
open import ecats.basic-defs.epi&mono
open import ecats.basic-defs.eqv-rel
open import ecats.finite-limits.defs.collective
open import ecats.finite-limits.props.relations-among-limits
open import ecats.finite-limits.defs.equaliser
open import ecats.finite-limits.defs.weak-equaliser
--open import ecats.finite-limits.props.weak-pullback
open import ecats.finite-limits.defs.weak-bow
open import ecats.functors.defs.efunctor
open import ecats.exact-completion.CVconstruction
open import ecats.exact-completion.CVconstr-is-excompl.exact.canonical-epi&mono


-- Equalisers

module exact-compl-has-equalisers {ℂ : ecategory} (hasfwl : has-fin-weak-limits ℂ) where
  private
    module ℂ where
      open ecategory ℂ public
      open comm-shapes ℂ public
      open pseudo-eq-rel-defs ℂ public
      open wequaliser-defs ℂ public
      open weak-bow-defs ℂ public
    module fwlℂ where
      open has-fin-weak-limits hasfwl public using (hasweql; haswbw) -- haswpb;
      open has-weak-equalisers hasweql using (weql-of)
      open has-weak-bows haswbw public using (wbw-of)
      open can-epi&mono-defs hasfwl public
    module Exℂ where
      open ecategory Ex ℂ [ hasfwl ] public
      open comm-shapes Ex ℂ [ hasfwl ] public
      open epis&monos-defs Ex ℂ [ hasfwl ] public 
      open equaliser-defs Ex ℂ [ hasfwl ] public
    infixr 2  _~_
    infixr 5 _∘_
    _~_ : {A B : ℂ.Obj} (f f' : || ℂ.Hom A B ||) → Set
    _~_ =  ℂ._~_
    _∘_ : {A B C : ℂ.Obj} →  || ℂ.Hom B C ||  → || ℂ.Hom A B || → || ℂ.Hom A C ||
    _∘_ = ℂ._∘_


  module ExC-eql-of {A B : Exℂ.Obj} (f f' : || Exℂ.Hom A B ||) where
    private
      module A = ℂ.peq A
      module B = ℂ.peq B
      module f = ℂ.peq-mor f
      module f' = ℂ.peq-mor f'
    sp-lof : ℂ.span/ B.Lo B.Lo
    sp-lof = ℂ.mkspan/ f.lo f'.lo
    private
      module sp-lof = ℂ.span/ sp-lof

    eqlLo : ℂ.wbow-of sp-lof B.sp/
    eqlLo = fwlℂ.wbw-of sp-lof B.sp/
    private
      module eqlLo = ℂ.wbow-of eqlLo
    
    EqlLo : ℂ.Obj
    EqlLo = eqlLo.Ob

    loeqlar : || ℂ.Hom EqlLo A.Lo ||
    loeqlar = eqlLo.wπ//₁

    private
      module Eql = fwlℂ.canonical-mono (fwlℂ.can-mono-over loeqlar A.peqover)
      module eql-mono = Exℂ.is-monic Eql.ar-monic
      module eqlOb = ℂ.peq Eql.Ob

    eqlOb : Exℂ.Obj
    eqlOb = Eql.Ob

    eqlar : || Exℂ.Hom eqlOb A ||
    eqlar = Eql.ar

    eqleq : f Exℂ.∘ Eql.ar Exℂ.~ f' Exℂ.∘ Eql.ar
    eqleq = record
      { hty = eqlLo.wπ//₂
      ; hty₀ = eqlLo.sqpf₁ ˢ
      ; hty₁ = eqlLo.sqpf₂ ˢ
      }
      where open ecategory-aux-only ℂ


    module Eql-univ (C : Exℂ.Obj) (g : || Exℂ.Hom C A ||) (pf : f Exℂ.∘ g Exℂ.~ f' Exℂ.∘ g) where
      private
        module C = ℂ.peq C
        module g = ℂ.peq-mor g
        module pf = ℂ.peq-mor-eq pf

      log|f-pfl : f.lo ℂ.∘ g.lo ℂ.~ B.%0 ℂ.∘ pf.hty
      log|f-pfl = pf.hty₀ ˢ
                where open ecategory-aux-only ℂ
      log|f-pfr : f'.lo ℂ.∘ g.lo ℂ.~ B.%1 ℂ.∘ pf.hty
      log|f-pfr = pf.hty₁ ˢ
                where open ecategory-aux-only ℂ
      log|f : || ℂ.Hom C.Lo EqlLo ||
      log|f = eqlLo.⟨ g.lo , pf.hty ⟩[ log|f-pfl , log|f-pfr ]


      hig|f-pfl : loeqlar ℂ.∘ log|f ℂ.∘ C.%0 ℂ.~ A.%0 ℂ.∘ g.hi
      hig|f-pfl = ass ⊙ ∘e r (eqlLo.tr₁ log|f-pfl log|f-pfr) ⊙ g.cmptb₀ ˢ
                where open ecategory-aux-only ℂ
      hig|f-pfr : loeqlar ℂ.∘ log|f ℂ.∘ C.%1 ℂ.~ A.%1 ℂ.∘ g.hi
      hig|f-pfr = ass ⊙ ∘e r (eqlLo.tr₁ log|f-pfl log|f-pfr) ⊙ g.cmptb₁ ˢ
                where open ecategory-aux-only ℂ
      hig|f : || ℂ.Hom C.Hi eqlOb.Hi ||
      hig|f = Eql.⟨ log|f ℂ.∘ C.%0 , g.hi , log|f ℂ.∘ C.%1 ⟩[ hig|f-pfl , hig|f-pfr ]

      g|f : || Exℂ.Hom C eqlOb ||
      g|f = record
        { lo = log|f
        ; isext = record
          { hi = hig|f
          ; cmptb₀ = Eql.trl hig|f-pfl hig|f-pfr
          ; cmptb₁ = Eql.trr hig|f-pfl hig|f-pfr
          }
        }

      trpf : eqlar Exℂ.∘ g|f Exℂ.~ g
      trpf = record
        { hty = A.ρ ℂ.∘ g.lo
        ; hty₀ = ass ⊙ lidgg (eqlLo.tr₁ log|f-pfl log|f-pfr ˢ) A.ρ-ax₀
        ; hty₁ = ass ⊙ lidgg r A.ρ-ax₁
        }
        where open ecategory-aux-only ℂ
    -- end Eql-univ


    eql-of : Exℂ.equaliser-of f f'
    eql-of = record
      { Eql = eqlOb
      ; eqlar = eqlar
      ; eqleq = eqleq
      ; iseql = record
        { _|eql[_] = λ {C} g pf → g|f C g pf
        ; eqltr = λ {C} {g} pf → trpf C g pf
        ; eqluq = λ {C} {g} pf → eql-mono.mono-pf pf
        }
      }
      where open Eql-univ
  -- end ExC-eql-of


  ex-cmpl-eql : has-equalisers Ex ℂ [ hasfwl ]
  ex-cmpl-eql = record { eql-of = eql-of }
              where open ExC-eql-of using (eql-of)
-- end exact-compl-has-equalisers


exact-compl-has-equalisers : {ℂ : ecategory} (hasfwl : has-fin-weak-limits ℂ)
                                → has-equalisers Ex ℂ [ hasfwl ]
exact-compl-has-equalisers {ℂ} hasfwl = ex-cmpl-eql
                                     where open exact-compl-has-equalisers {ℂ} hasfwl using (ex-cmpl-eql)

exact-compl-qcart-has-equalisers : {ℂ : ecategory} (qcart : is-quasi-cartesian ℂ)
                                → has-equalisers Ex ℂ qc[ qcart ]
exact-compl-qcart-has-equalisers {ℂ} qcart = exact-compl-has-equalisers (qcart→has-fwlim qcart)
