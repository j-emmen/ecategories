
-- disable the K axiom:

{-# OPTIONS --without-K #-}

-- Agda version 2.5.4.1

module ecats.exact-completion.CVconstr-is-excompl.exact.is-exact where

open import ecats.basic-defs.ecat-def&not
open import ecats.basic-defs.all-arrows
open import ecats.basic-props.epi&mono
open import ecats.basic-props.image-fact
open import ecats.basic-defs.regular-ecat
open import ecats.basic-props.regular-ecat
open import ecats.basic-defs.exact-ecat
open import ecats.finite-limits.all
open import ecats.exact-completion.CVconstruction
open import ecats.exact-completion.CVconstr-is-excompl.finite-limits.fin-limits
open import ecats.exact-completion.CVconstr-is-excompl.finite-limits.pullback
open import ecats.exact-completion.CVconstr-is-excompl.exact.canonical-epi&mono
open import ecats.exact-completion.CVconstr-is-excompl.exact.is-regular


-- Equivalence relations are effective

module eq-rels-are-effective {ℂ : ecategory} (hasfwl : has-fin-weak-limits ℂ) where
  private
    module ℂ where
      open ecategory ℂ public
      open comm-shapes ℂ public
      open pseudo-eq-rel-defs ℂ public
      open finite-weak-limits ℂ public
      open can-epi&mono-defs hasfwl public
    module fwlℂ where
      open has-fin-weak-limits hasfwl public
      open has-weak-pullbacks haswpb using (wpb-of) public
      open has-weak-Wlimits (has-wpb⇒has-wW haswpb) public
    module Exℂ where
      open ecategory Ex ℂ [ hasfwl ] public
      open comm-shapes Ex ℂ [ hasfwl ] public
      open iso-defs Ex ℂ [ hasfwl ] public
      open iso-transports Ex ℂ [ hasfwl ] public
      open epis&monos-defs Ex ℂ [ hasfwl ] public
      open epis&monos-props Ex ℂ [ hasfwl ] public
      open eq-rel-defs Ex ℂ [ hasfwl ] public
      open kernel-pairs-defs Ex ℂ [ hasfwl ] public
      open image-fact-defs Ex ℂ [ hasfwl ] public
      open image-fact-props Ex ℂ [ hasfwl ] public
      open pullback-squares Ex ℂ [ hasfwl ] public
      open pullback-props Ex ℂ [ hasfwl ] public
    module flExℂ where
      open has-fin-limits (exact-compl-has-fin-limits hasfwl) public
      open has-pullbacks haspb public using (pb-of)
    infixr 2  _~_
    infixr 5 _∘_
    _~_ : {A B : ℂ.Obj} (f f' : || ℂ.Hom A B ||) → Set
    _~_ =  ℂ._~_
    _∘_ : {A B C : ℂ.Obj} →  || ℂ.Hom B C ||  → || ℂ.Hom A B || → || ℂ.Hom A C ||
    _∘_ = ℂ._∘_


  module eq-rel-are-kernel-pairs {A : Exℂ.Obj} (eqr : Exℂ.eqrel-over A) where
    open ecategory-aux-only ℂ
    private
      module A = ℂ.peq A
      module Aτwpb = ℂ.wpullback-of-not A.τwpb
      module eqr/ = Exℂ.eqrel-over eqr
      module R = ℂ.peq eqr/.relOb
      module r₁ = ℂ.peq-mor eqr/.r₁
      module r₂ = ℂ.peq-mor eqr/.r₂
      module rρ = ℂ.peq-mor eqr/.ρ
      module rρ-ax₀ = ℂ.peq-mor-eq eqr/.ρ-ax₀
      module rρ-ax₁ = ℂ.peq-mor-eq eqr/.ρ-ax₁
      HiQ : ℂ.wWlim-of A.%0 (ℂ.mkspan/ r₁.lo r₂.lo) A.%0
      HiQ = fwlℂ.wW-of A.%0 (ℂ.mkspan/ r₁.lo r₂.lo) A.%0
      module HiQ = ℂ.wWlim-of HiQ

    -- quotient peq
    private
      --symmetry
      module rσ = ℂ.peq-mor eqr/.σ
      module rσ-ax₀ = ℂ.peq-mor-eq eqr/.σ-ax₀
      module rσ-ax₁ = ℂ.peq-mor-eq eqr/.σ-ax₁
      Qσl-pf = A.%1 ∘ rσ-ax₀.hty ℂ.∘ HiQ.πc   ~[ rσ-ax₀.hty₁g ⊙ HiQ.sqpfr ˢ ]
               A.%0 ∘ HiQ.πr
      Qσl : || ℂ.Hom HiQ.wWOb A.Hi ||
      Qσl = A.τ ∘ Aτwpb.w⟨ rσ-ax₀.hty ∘ HiQ.πc , HiQ.πr ⟩[ Qσl-pf ]
      Qσr-pf = A.%1 ∘ rσ-ax₁.hty ℂ.∘ HiQ.πc   ~[ rσ-ax₁.hty₁g ⊙ HiQ.sqpfl ˢ ]
               A.%0 ∘ HiQ.πl
      Qσr : || ℂ.Hom HiQ.wWOb A.Hi ||
      Qσr = A.τ ∘ Aτwpb.w⟨ rσ-ax₁.hty ∘ HiQ.πc , HiQ.πl ⟩[ Qσr-pf ]
      Qσ-pfl = ~proof A.%0 ∘ Qσl                      ~[ A.τ-ax₀g ] /
                      A.%0 ∘ rσ-ax₀.hty ℂ.∘ HiQ.πc    ~[ rσ-ax₀.hty₀g ⊙ assˢ ]∎
                      r₁.lo ∘ rσ.lo ∘ HiQ.πc ∎
      Qσ-pfr = ~proof A.%0 ∘ Qσr                      ~[ A.τ-ax₀g ] /
                      A.%0 ∘ rσ-ax₁.hty ℂ.∘ HiQ.πc    ~[ rσ-ax₁.hty₀g ⊙ assˢ ]∎
                      r₂.lo ∘ rσ.lo ∘ HiQ.πc ∎
      --transitivity
      -- Lo of chosen pullback is W limit
      r₂×/r₁ : Exℂ.pullback-of eqr/.r₂ eqr/.r₁
      r₂×/r₁ = flExℂ.pb-of eqr/.r₂ eqr/.r₁
      module r₂×/r₁ = Exℂ.pullback-of-not r₂×/r₁
      module risτ' = Exℂ.is-transitive/pb (Exℂ.trans-is-pb-irrel r₂×/r₁ eqr/.isτ)
      module rτ' = ℂ.peq-mor risτ'.τ
      module rτ'-ax₀ = ℂ.peq-mor-eq risτ'.τ-ax₀
      module rτ'-ax₁ = ℂ.peq-mor-eq risτ'.τ-ax₁
      module Lo[r₂×/r₁] = ℂ.wWlim-of (fwlℂ.wW-of r₂.lo A.sp/ r₁.lo)
      Qτwpb : ℂ.wpullback-of (A.%1 ∘ HiQ.πr) (A.%1 ∘ HiQ.πl)
      Qτwpb = fwlℂ.wpb-of (A.%1 ∘ HiQ.πr) (A.%1 ∘ HiQ.πl)
      module Qτwpb = ℂ.wpullback-of-not Qτwpb
      Qτc-auxApf = ~proof A.%1 ∘ HiQ.πr ∘ Qτwpb.wπ/₁             ~[ ass ⊙ Qτwpb.w×/sqpf ⊙ assˢ ] /
                          A.%1 ∘ HiQ.πl ∘ Qτwpb.wπ/₂             ~[ ∘e r (A.σ-ax₀ ˢ) ⊙ assˢ ]∎
                          A.%0 ∘ A.σ ∘ HiQ.πl ∘ Qτwpb.wπ/₂ ∎
      Qτc-auxA : || ℂ.Hom Qτwpb.ul A.Hi ||
      Qτc-auxA = A.τ ∘ Aτwpb.w⟨ HiQ.πr ∘ Qτwpb.wπ/₁ , A.σ ∘ HiQ.πl ∘ Qτwpb.wπ/₂ ⟩[ Qτc-auxApf ]
      Qτc-auxpfl = ~proof r₂.lo ∘ HiQ.πc ∘ Qτwpb.wπ/₁        ~[ ass ⊙ ∘e r (HiQ.sqpfr ˢ) ⊙ assˢ ] /
                          A.%0 ∘ HiQ.πr ∘ Qτwpb.wπ/₁         ~[ A.τ-ax₀g ˢ ]∎
                          A.%0 ∘ Qτc-auxA ∎
      Qτc-auxpfr = ~proof r₁.lo ∘ HiQ.πc ∘ Qτwpb.wπ/₂        ~[ ass ⊙ ∘e r (HiQ.sqpfl ˢ) ⊙ assˢ ] /
                          A.%0 ∘  HiQ.πl ∘ Qτwpb.wπ/₂        ~[ A.σ-ax₁g ˢ ] /
                          A.%1 ∘ A.σ ∘ HiQ.πl ∘ Qτwpb.wπ/₂   ~[ A.τ-ax₁g ˢ ]∎
                          A.%1 ∘ Qτc-auxA ∎
      Qτc-aux : || ℂ.Hom Qτwpb.ul Lo[r₂×/r₁].wWOb ||
      Qτc-aux = Lo[r₂×/r₁].⟨ HiQ.πc ∘ Qτwpb.wπ/₁ , Qτc-auxA , HiQ.πc ∘ Qτwpb.wπ/₂
                           ⟩[ Qτc-auxpfl , Qτc-auxpfr ]
      Qτl-aux : || ℂ.Hom Qτwpb.ul Aτwpb.ul ||
      Qτl-aux = Aτwpb.w⟨ rτ'-ax₀.hty ∘ Qτc-aux , HiQ.πl ∘ Qτwpb.wπ/₁
                       ⟩[ ~proof A.%1 ∘ rτ'-ax₀.hty ∘ Qτc-aux              ~[ rτ'-ax₀.hty₁g ⊙ assˢ  ] /
                                r₁.lo ∘ Lo[r₂×/r₁].πl ∘ Qτc-aux
                                                       ~[ ∘e (Lo[r₂×/r₁].trl Qτc-auxpfl Qτc-auxpfr) r ] /
                                r₁.lo ∘ HiQ.πc ∘ Qτwpb.wπ/₁       ~[ ass ⊙ ∘e r (HiQ.sqpfl ˢ) ⊙ assˢ ]∎
                                A.%0 ∘ HiQ.πl ∘ Qτwpb.wπ/₁ ∎ ]
      Qτr-aux : || ℂ.Hom Qτwpb.ul Aτwpb.ul ||
      Qτr-aux = Aτwpb.w⟨ rτ'-ax₁.hty ∘ Qτc-aux , HiQ.πr ∘ Qτwpb.wπ/₂
                       ⟩[ ~proof A.%1 ∘ rτ'-ax₁.hty ∘ Qτc-aux              ~[ rτ'-ax₁.hty₁g ⊙ assˢ  ] /
                                r₂.lo ∘ Lo[r₂×/r₁].πr ∘ Qτc-aux
                                                       ~[ ∘e (Lo[r₂×/r₁].trr Qτc-auxpfl Qτc-auxpfr) r ] /
                                r₂.lo ∘ HiQ.πc ∘ Qτwpb.wπ/₂       ~[ ass ⊙ ∘e r (HiQ.sqpfr ˢ) ⊙ assˢ ]∎
                                A.%0 ∘ HiQ.πr ∘ Qτwpb.wπ/₂ ∎ ]
      Qτl-pf = ~proof A.%0 ∘ A.τ ∘ Qτl-aux            ~[ A.τ-ax₀g ] /
                      A.%0 ∘ rτ'-ax₀.hty ∘ Qτc-aux    ~[ rτ'-ax₀.hty₀g ⊙ assˢ ]∎
                      r₁.lo ∘ rτ'.lo ∘ Qτc-aux ∎
      Qτr-pf = ~proof A.%0 ∘ A.τ ∘ Qτr-aux            ~[ A.τ-ax₀g ] /
                      A.%0 ∘ rτ'-ax₁.hty ∘ Qτc-aux    ~[ rτ'-ax₁.hty₀g ⊙ assˢ ]∎
                      r₂.lo ∘ rτ'.lo ∘ Qτc-aux ∎
    -- end private
    
    Q : ℂ.peq
    Q = record
      { Lo = A.Lo
      ; peqover = record
        { Hi = HiQ.wWOb
        ; %0 = A.%1 ∘ HiQ.πl
        ; %1 = A.%1 ∘ HiQ.πr
        ; ispeq = record
                { isρ = record
                  { ρ = HiQ.⟨ rρ-ax₀.hty , rρ.lo , rρ-ax₁.hty ⟩[ rρ-ax₀.hty₀ , rρ-ax₁.hty₀ ]
                  ; ρ-ax₀ = assˢ ⊙ ∘e (HiQ.trl rρ-ax₀.hty₀ rρ-ax₁.hty₀) r ⊙ rρ-ax₀.hty₁ 
                  ; ρ-ax₁ = assˢ ⊙ ∘e (HiQ.trr rρ-ax₀.hty₀ rρ-ax₁.hty₀) r ⊙ rρ-ax₁.hty₁
                  }
                ; isσ = record
                  { σ = HiQ.⟨ Qσl , rσ.lo ∘ HiQ.πc , Qσr ⟩[ Qσ-pfl , Qσ-pfr ]
                  ; σ-ax₀ = ~proof
                          (A.%1 ∘ HiQ.πl) ∘ HiQ.⟨ Qσl , rσ.lo ∘ HiQ.πc , Qσr ⟩[ Qσ-pfl , Qσ-pfr ]
                                                ~[ assˢ ⊙ ∘e (HiQ.trl Qσ-pfl Qσ-pfr) r ] /
                          A.%1 ∘ Qσl            ~[ A.τ-ax₁g ]∎
                          A.%1 ∘ HiQ.πr ∎
                  ; σ-ax₁ = ~proof
                          (A.%1 ∘ HiQ.πr) ∘ HiQ.⟨ Qσl , rσ.lo ∘ HiQ.πc , Qσr ⟩[ Qσ-pfl , Qσ-pfr ]
                                                ~[ assˢ ⊙ ∘e (HiQ.trr Qσ-pfl Qσ-pfr) r ] /
                          A.%1 ∘ Qσr            ~[ A.τ-ax₁g ]∎
                          A.%1 ∘ HiQ.πl ∎
                  }
                ; τwpb = Qτwpb
                ; iswτ = record
                  { τ = HiQ.⟨ A.τ ∘ Qτl-aux , rτ'.lo ∘ Qτc-aux , A.τ ∘ Qτr-aux
                            ⟩[ Qτl-pf , Qτr-pf ]
                  ; τ-ax₀ = ~proof (A.%1 ∘ HiQ.πl)
                            ∘ HiQ.⟨ A.τ ∘ Qτl-aux , rτ'.lo ∘ Qτc-aux , A.τ ∘ Qτr-aux ⟩[ Qτl-pf , Qτr-pf ]
                                                    ~[ assˢ ⊙ ∘e (HiQ.trl Qτl-pf Qτr-pf) r ] /
                                   A.%1 ∘ A.τ ∘ Qτl-aux            ~[ A.τ-ax₁g ⊙ ass ]∎
                                   (A.%1 ∘ HiQ.πl) ∘ Qτwpb.wπ/₁ ∎
                  ; τ-ax₁ = ~proof (A.%1 ∘ HiQ.πr)
                            ∘ HiQ.⟨ A.τ ∘ Qτl-aux , rτ'.lo ∘ Qτc-aux , A.τ ∘ Qτr-aux ⟩[ Qτl-pf , Qτr-pf ]
                                                    ~[ assˢ ⊙ ∘e (HiQ.trr Qτl-pf Qτr-pf) r ] /
                                   A.%1 ∘ A.τ ∘ Qτr-aux            ~[ A.τ-ax₁g ⊙ ass ]∎
                                   (A.%1 ∘ HiQ.πr) ∘ Qτwpb.wπ/₂ ∎
                  }
                }
        }
      }
    private module Q = ℂ.peq Q      


    -- quotient arrow
    q-hi-r : || ℂ.Hom A.Hi A.Hi ||
    q-hi-r = A.τ ∘ Aτwpb.w⟨ rρ-ax₁.hty ∘ A.%0 , ℂ.idar A.Hi ⟩[ rρ-ax₁.hty₁g ⊙ lidgen ridˢ ]
    q-hi-pfl = A.%0 ∘ rρ-ax₀.hty ∘ A.%0 ~[ rρ-ax₀.hty₀g ⊙ assˢ ]
               r₁.lo ∘ rρ.lo ∘ A.%0
    q-hi-pfr = A.%0 ∘ q-hi-r ~[ A.τ-ax₀g ⊙ rρ-ax₁.hty₀g ⊙ assˢ ]
               r₂.lo ∘ rρ.lo ∘ A.%0
    q-hi : || ℂ.Hom A.Hi HiQ.wWOb ||
    q-hi = HiQ.⟨ rρ-ax₀.hty ∘ A.%0 , rρ.lo ∘ A.%0 , q-hi-r
               ⟩[ q-hi-pfl , q-hi-pfr ]
    q-hi0 : Q.%0 ∘ q-hi ~ A.%0
    q-hi0 = ~proof Q.%0 ∘ q-hi                   ~[ assˢ ⊙ ∘e (HiQ.trl q-hi-pfl q-hi-pfr) r ] /
                   A.%1 ∘ rρ-ax₀.hty ∘ A.%0      ~[ rρ-ax₀.hty₁g ⊙ lid ]∎
                   A.%0 ∎
    q-hi1 : Q.%1 ∘ q-hi ~ A.%1
    q-hi1 = ~proof Q.%1 ∘ q-hi                   ~[ assˢ ⊙ ∘e (HiQ.trr q-hi-pfl q-hi-pfr) r ] /
                   A.%1 ∘ q-hi-r                 ~[ A.τ-ax₁g ⊙ rid ]∎
                   A.%1 ∎
    qdata : ℂ.canonical-repi A.peqover Q.peqover
    qdata = record { crepi-hi = q-hi
                   ; crepi-ax₀ = q-hi0
                   ; crepi-ax₁ = q-hi1
                   }
    private
      module q where
        open ℂ.canonical-repi qdata public
        open ℂ.peq-mor ar public
    q : || Exℂ.Hom A Q ||
    q = q.ar


    -- kernel pair square
    q-sq : q Exℂ.∘ eqr/.r₁ Exℂ.~ q Exℂ.∘ eqr/.r₂
    q-sq = record
      { hty = q-hty
      ; hty₀ = ~proof Q.%0 ∘ q-hty          ~[ assˢ ⊙ ∘e (HiQ.trl (A.ρ-ax₀g ⊙ ridˢ) (A.ρ-ax₀g ⊙ ridˢ)) r ] /
                      A.%1 ∘ A.ρ ∘ r₁.lo    ~[ A.ρ-ax₁g ⊙ lidˢ ]∎
                      q.lo ∘ r₁.lo ∎
      ; hty₁ = ~proof Q.%1 ∘ q-hty          ~[ assˢ ⊙ ∘e (HiQ.trr (A.ρ-ax₀g ⊙ ridˢ) (A.ρ-ax₀g ⊙ ridˢ)) r ] /
                      A.%1 ∘ A.ρ ∘ r₂.lo    ~[ A.ρ-ax₁g ⊙ lidˢ ]∎
                      q.lo ∘ r₂.lo ∎
      }
      where q-hty : || ℂ.Hom R.Lo HiQ.wWOb ||
            q-hty = HiQ.⟨ A.ρ ∘ r₁.lo , ℂ.idar R.Lo , A.ρ ∘ r₂.lo ⟩[ A.ρ-ax₀g ⊙ ridˢ , A.ρ-ax₀g ⊙ ridˢ ]
    private module qsq = ℂ.peq-mor-eq q-sq


    module qsq-is-pb {B : Exℂ.Obj} (h k : || Exℂ.Hom B A ||) (eqpf : q Exℂ.∘ h Exℂ.~ q Exℂ.∘ k) where
      private
        module B = ℂ.peq B
        module h = ℂ.peq-mor h
        module k = ℂ.peq-mor k
        module eqpf = ℂ.peq-mor-eq eqpf

      loun : || ℂ.Hom B.Lo R.Lo ||
      loun = HiQ.πc ∘ eqpf.hty

      r₁un~h r₂un~k : || ℂ.Hom B.Lo A.Hi ||
      r₁un~h = HiQ.πl ∘ eqpf.hty
      r₂un~k = HiQ.πr ∘ eqpf.hty
      r₁un~h₀ = A.%0 ∘ r₁un~h   ~[ ass ⊙ ∘e r HiQ.sqpfl ⊙ assˢ ]   r₁.lo ∘ loun
      r₁un~h₁ = A.%1 ∘ r₁un~h   ~[ ass ⊙ eqpf.hty₀ ⊙ lid ]        h.lo
      r₂un~k₀ = A.%0 ∘ r₂un~k   ~[ ass ⊙ ∘e r HiQ.sqpfr ⊙ assˢ ]   r₂.lo ∘ loun
      r₂un~k₁ = A.%1 ∘ r₂un~k   ~[ ass ⊙ eqpf.hty₁ ⊙ lid ]        k.lo

      eq-conc-aux : {X : ℂ.Obj} {x₁ x₂ x₃ x₄ : || ℂ.Hom X A.Lo ||} {y₁ y₂ y₃ : || ℂ.Hom X A.Hi ||}
                    (y₁₀ : A.%0 ∘ y₁ ~ x₁) (y₁₁ : A.%1 ∘ y₁ ~ x₂) (y₂₀ : A.%0 ∘ y₂ ~ x₂)
                    (y₂₁ : A.%1 ∘ y₂ ~ x₃) (y₃₀ : A.%0 ∘ y₃ ~ x₄) (y₃₁ : A.%1 ∘ y₃ ~ x₃)
                      → ℂ.freepeq-is-min A x₁ Exℂ.~ ℂ.freepeq-is-min A x₄
      eq-conc-aux {y₁ = y₁} {y₂} {y₃} y₁₀ y₁₁ y₂₀ y₂₁ y₃₀ y₃₁ = record
        { hty = A.τ ∘ Aτwpb.w⟨ A.τ ∘ Aτwpb.w⟨ y₁ , y₂ ⟩[ fstpf ] , A.σ ∘ y₃ ⟩[ sndpf ]
        ; hty₀ = A.τ-ax₀g ⊙ A.τ-ax₀g ⊙ y₁₀
        ; hty₁ = A.τ-ax₁g ⊙ A.σ-ax₁g ⊙ y₃₀
        }
        where fstpf = A.%1 ∘ y₁   ~[ y₁₁ ⊙ y₂₀ ˢ ]   A.%0 ∘ y₂
              sndpf = A.%1 ∘ A.τ ∘ Aτwpb.w⟨ y₁ , y₂ ⟩[ fstpf ]
                               ~[ A.τ-ax₁g ⊙ (y₂₁ ⊙ y₃₁ ˢ) ⊙ A.σ-ax₀g ˢ ]
                      A.%0 ∘ A.σ ∘ y₃

      loun-ext-pf1 : eqr/.r₁ Exℂ.∘ ℂ.freepeq-is-min eqr/.relOb (loun ∘ B.%0)
                       Exℂ.~    eqr/.r₁ Exℂ.∘ ℂ.freepeq-is-min eqr/.relOb (loun ∘ B.%1)
      loun-ext-pf1 = record
        { hty = r₁un-ext.hty
        ; hty₀ = r₁un-ext.hty₀
        ; hty₁ = r₁un-ext.hty₁
        }
        where r₁un-ext : ℂ.freepeq-is-min A (r₁.lo ∘ loun ∘ B.%0) Exℂ.~ ℂ.freepeq-is-min A (r₁.lo ∘ loun ∘ B.%1)
              r₁un-ext = eq-conc-aux {y₁ = r₁un~h ∘ B.%0} {y₂ = h.hi} {y₃ = r₁un~h ∘ B.%1}
                                     (ass ⊙ ∘e r r₁un~h₀ ⊙ assˢ) (ass ⊙ ∘e r r₁un~h₁) h.cmptb₀
                                     h.cmptb₁ (ass ⊙ ∘e r r₁un~h₀ ⊙ assˢ) (ass ⊙ ∘e r r₁un~h₁)
              module r₁un-ext = ℂ.peq-mor-eq r₁un-ext
      loun-ext-pf2 : eqr/.r₂ Exℂ.∘ ℂ.freepeq-is-min eqr/.relOb (loun ∘ B.%0)
                       Exℂ.~    eqr/.r₂ Exℂ.∘ ℂ.freepeq-is-min eqr/.relOb (loun ∘ B.%1)
      loun-ext-pf2 = record
        { hty = r₂un-ext.hty
        ; hty₀ = r₂un-ext.hty₀
        ; hty₁ = r₂un-ext.hty₁
        }
        where r₂un-ext : ℂ.freepeq-is-min A (r₂.lo ∘ loun ∘ B.%0) Exℂ.~ ℂ.freepeq-is-min A (r₂.lo ∘ loun ∘ B.%1)
              r₂un-ext = eq-conc-aux {y₁ = r₂un~k ∘ B.%0} {y₂ = k.hi} {y₃ = r₂un~k ∘ B.%1}
                                     (ass ⊙ ∘e r r₂un~k₀ ⊙ assˢ) (ass ⊙ ∘e r r₂un~k₁) k.cmptb₀
                                     k.cmptb₁ (ass ⊙ ∘e r r₂un~k₀ ⊙ assˢ) (ass ⊙ ∘e r r₂un~k₁)
              module r₂un-ext = ℂ.peq-mor-eq r₂un-ext
      loun-ext : ℂ.freepeq-is-min eqr/.relOb (loun ∘ B.%0)
                          Exℂ.~    ℂ.freepeq-is-min eqr/.relOb (loun ∘ B.%1)
      loun-ext = eqr/.jm-pf loun-ext-pf1 loun-ext-pf2
      module hilo = ℂ.peq-mor-eq loun-ext


      univ : || Exℂ.Hom B eqr/.relOb ||
      univ = record { lo = loun
                    ; isext = record
                      { hi = hilo.hty
                      ; cmptb₀ = hilo.hty₀
                      ; cmptb₁ = hilo.hty₁
                      }
                    }

    -- end qsq-is-pb


    q-pbsq : Exℂ.is-pb-square (Exℂ.mksq (Exℂ.mksq/ q-sq))
    q-pbsq = record
      { ⟨_,_⟩[_] = univ
      ; ×/tr₁ = λ {_} {h} {k} pf → record
              { hty = r₁un~h h k pf
              ; hty₀ = r₁un~h₀ h k pf
              ; hty₁ = r₁un~h₁ h k pf
              }
      ; ×/tr₂ = λ {_} {h} {k} pf → record
              { hty = r₂un~k h k pf
              ; hty₀ = r₂un~k₀ h k pf
              ; hty₁ = r₂un~k₁ h k pf
              }
      ; ×/uq = eqr/.jm-pf
      }
      where open qsq-is-pb
    
  --end eq-rel-are-kernel-pairs


  private module eqr = Exℂ.eqrel-over
  eqrel→kp : {A : Exℂ.Obj} (eqr : Exℂ.eqrel-over A) → Exℂ.is-kernel-pair (eqr.r₁ eqr) (eqr.r₂ eqr)
  eqrel→kp eqr = record
    { ispbsq = q-pbsq
    }
    where open eq-rel-are-kernel-pairs eqr

-- end eq-rels-are-effective



-----------------------------
-- Exact completion is exact
-----------------------------


exact-compl-is-exact//hasfl : {ℂ : ecategory} (hasfwl : has-fin-weak-limits ℂ)
                              → is-exact//has-fin-lim (exact-compl-has-fin-limits hasfwl)
exact-compl-is-exact//hasfl hasfwl = reg2exact eqrel→kp
                                   where open regular-cat-props (exact-compl-is-regular hasfwl)
                                         open eq-rels-are-effective hasfwl

exact-compl-is-exact : {ℂ : ecategory} (hasfwl : has-fin-weak-limits ℂ) → is-exact Ex ℂ [ hasfwl ]
exact-compl-is-exact {ℂ} hasfwl = record { hasfl = exact-compl-has-fin-limits hasfwl
                                         ; isex/fl = exact-compl-is-exact//hasfl hasfwl
                                         }


exact-compl-qcart-is-exact//hasfl : {ℂ : ecategory} (qcart : is-quasi-cartesian ℂ)
                                       → is-exact//has-fin-lim (exact-compl-qcart-has-fin-limits qcart)
exact-compl-qcart-is-exact//hasfl qcart = exact-compl-is-exact//hasfl (qcart→has-fwlim qcart)

exact-compl-qcart-is-exact : {ℂ : ecategory} (qcart : is-quasi-cartesian ℂ) → is-exact Ex ℂ qc[ qcart ]
exact-compl-qcart-is-exact qcart = exact-compl-is-exact (qcart→has-fwlim qcart)
