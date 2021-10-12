
{-# OPTIONS --without-K --show-implicit  #-}

module ecats.exact-completion.projcov-is-excompl.eqv-to-CVconstr where

open import ecats.basic-defs.ecat-def&not
open import ecats.basic-defs.all-arrows
open import ecats.basic-props.epi&mono
open import ecats.basic-defs.regular-ecat
open import ecats.basic-defs.exact-ecat
open import ecats.basic-props.exact-ecat
open import ecats.finite-limits.all
open import ecats.functors.defs.efunctor-d&n
open import ecats.functors.defs.basic-defs
open import ecats.functors.defs.natural-transformation
open import ecats.functors.defs.projective-cover
open import ecats.functors.defs.left-covering
open import ecats.functors.props.basic-props
open import ecats.functors.props.projective-cover
open import ecats.constructions.ecat-eqrel
open import ecats.exact-completion.def
open import ecats.exact-completion.CVconstruction
open import ecats.exact-completion.CVconstr-is-excompl
open import ecats.exact-completion.CVconstr-is-excompl.embedding.universal-property.eqrel-from-peq

------------------------------------------------------------------
-- A projective cover ℙ → 𝔼 of 𝔼 exact is equivalent to
-- the CVconstruction on ℙ as a category with weak finite limits
------------------------------------------------------------------

module projcov-of-exact-is-eqv-to-CVconstr {𝔼 : ecategory} (ex𝔼 : is-exact 𝔼){ℙ : ecategory}
                                           {PC : efunctor ℙ 𝔼} (pjcPC : is-projective-cover PC)
                                           where
  private
    module 𝔼 where
      open ecategory 𝔼 public
      open iso-defs 𝔼 public
      open epis&monos-defs 𝔼 public
      open epis&monos-props 𝔼 public
      open kernel-pairs-defs 𝔼 public
      open eq-rel-defs 𝔼 public
      open finite-limits-d&p 𝔼 public
    module ex𝔼 where
      open exact-cat-d&p ex𝔼 public
      open has-pullbacks haspb using (pb-of) public
    reg𝔼 : is-regular 𝔼
    reg𝔼 = ex𝔼.is-reg
    -- it seems that declaring reg𝔼 explicitly is crucial
    -- for typechecking F↑ex-coeq.Ob A = F↑ex.ₒ A
    module ℙ where
      open ecategory ℙ public
      open pseudo-eq-rel-defs ℙ public
      open finite-weak-limits-d&p ℙ public
    fwlℙ : has-fin-weak-limits ℙ
    fwlℙ = proj-cov-has-wlim pjcPC ex𝔼.hasfl
    module fwlℙ where
      open has-fin-weak-limits fwlℙ public
      open has-weak-pullbacks haswpb using (wpb-of) public
    module PC where
      open efunctor-aux PC public
      open is-projective-cover pjcPC public
      islcov : is-left-covering PC
      islcov = pjcov-of-reg-is-lcov reg𝔼 pjcPC

    -- the exact completion of ℙ
    module Exℙ where
      open ecategory Ex ℙ [ fwlℙ ] public
      open iso-defs Ex ℙ [ fwlℙ ] public
      open epis&monos-defs Ex ℙ [ fwlℙ ] public
      open epis&monos-props Ex ℙ [ fwlℙ ] public
      open image-fact-defs Ex ℙ [ fwlℙ ] public
    module CVex where
      open efunctor-aux CVex ℙ [ fwlℙ ] public
      open is-exwlex-completion (CVconstr-is-excompl fwlℙ) public

    -- the canonical functor Exℙ → 𝔼 induced by PC
    module PC↑ex where
      open CVex.unv ex𝔼 PC.islcov using (fctr) public
      open efunctor-aux fctr public

    -- The equivalence relation in 𝔼 induced by a peq in ℙ...
    module CRF (R : Exℙ.Obj) where
      open eqrel-from-peq-funct fwlℙ
      open eqrel-from-peq-via-left-covering reg𝔼 PC.islcov
      open eqrel-as-repi-mono-fact R public
      open rmfF% using (C; C-is-repi) public
    PCRel : efunctor Ex ℙ [ fwlℙ ] (EqRel 𝔼)
    PCRel = Rel reg𝔼 PC.islcov
         where open eqrel-from-peq-funct fwlℙ
    module PCRel where
      open efunctor-aux PCRel public
      private
        module tmpOb (A : Exℙ.Obj) = 𝔼.eqrel (ₒ A)
        module tmpAr {A B : Exℙ.Obj} (f : || Exℙ.Hom A B ||) = 𝔼.eqrel-mor (ₐ f)
      open tmpOb public
      open tmpAr public

    -- ... and its quotient
    Q/PC↑ex : (A : Exℙ.Obj) → 𝔼.coeq-of (PCRel.r₁ A) (PCRel.r₂ A)
    Q/PC↑ex A = ex𝔼.eqr-has-coeq (PCRel.eqrelover A)
    module Q/PC↑ex (A : Exℙ.Obj) where
      open 𝔼.coeq-of (Q/PC↑ex A) public
      repi : 𝔼.is-regular-epi {PCRel.baseOb A} {Ob} ar
      repi = record { coeq = iscoeq }
      open 𝔼.is-exact-seq (ex𝔼.ex-seq (PCRel.eqrelover A))
      module kp = 𝔼.pullback-of-not (𝔼.mkpb-of iskerpair)
    qQ/PC↑ex : (A : Exℙ.Obj) → 𝔼.is-coeq (PC.ₐ (ℙ.peq.%0 A)) (PC.ₐ (ℙ.peq.%1 A)) (Q/PC↑ex.ar A)
    qQ/PC↑ex A = 𝔼.epi/coeq-so-coeq (𝔼.repi-is-epic C-is-repi) rmfF%tr₁ rmfF%tr₂ (Q/PC↑ex.iscoeq A)
               where open CRF A
    module qQ/PC↑ex (A : Exℙ.Obj) = 𝔼.is-coeq (qQ/PC↑ex A)


  ------------------------------
  -- PC↑ex is full and faithful
  ------------------------------
  
  private
    module PC↑ex-full {R S : Exℙ.Obj} (g : || 𝔼.Hom (PC↑ex.ₒ R) (PC↑ex.ₒ S) ||) where
      private
        module R where
          open ℙ.peq R public
          module RMF = CRF R
          module rpL = PC.rprj Lo
          module rpH = PC.rprj Hi
          module Q = Q/PC↑ex R
        module S where
          open ℙ.peq S public
          module RMF = CRF S
          module rpL = PC.rprj Lo
          module rpH = PC.rprj Hi
          module Q = Q/PC↑ex S
        lo : || ℙ.Hom R.Lo S.Lo ||
        lo = PC.full-ar (R.rpL.lift S.Q.repi (g 𝔼.∘ R.Q.ar))
        hiaux-pf : S.Q.ar 𝔼.∘ PC.ₐ (lo ℙ.∘ R.%0) 𝔼.~ S.Q.ar 𝔼.∘ PC.ₐ (lo ℙ.∘ R.%1)
        hiaux-pf = ~proof
          S.Q.ar 𝔼.∘ PC.ₐ (lo ℙ.∘ R.%0)
                 ~[ ∘e (PC.∘ax-rf ˢ ⊙ ∘e (R.RMF.rmfF%tr₁ ˢ) PC.full-pf) r ⊙ ass ⊙ ∘e r R.rpL.lift-tr ⊙ assˢ ] /
          g 𝔼.∘ R.Q.ar 𝔼.∘ R.Q.kp.π/₁ 𝔼.∘ R.RMF.C              ~[ ∘e (ass ⊙ ∘e r R.Q.kp.×/sqpf ⊙ assˢ) r ] /
          g 𝔼.∘ R.Q.ar 𝔼.∘ R.Q.kp.π/₂ 𝔼.∘ R.RMF.C
            ~[ (ass ⊙ ∘e r (R.rpL.lift-tr ˢ)) ⊙ assˢ ⊙ ∘e (∘e R.RMF.rmfF%tr₂ (PC.full-pf ˢ) ⊙ PC.∘ax-rf) r ]∎
          S.Q.ar 𝔼.∘ PC.ₐ (lo ℙ.∘ R.%1) ∎
                 where open ecategory-aux-only 𝔼
        hiaux : || 𝔼.Hom (PC.ₒ R.Hi) S.Q.kp.ul ||
        hiaux = S.Q.kp.⟨ PC.ₐ (lo ℙ.∘ R.%0) , PC.ₐ (lo ℙ.∘ R.%1) ⟩[ hiaux-pf ]
        hi : || ℙ.Hom R.Hi S.Hi ||
        hi = PC.full-ar (R.rpH.lift S.RMF.C-is-repi hiaux)
      ar : ℙ.peq-mor R S
      ar = record
        { lo = lo
        ; isext = record
          { hi = hi
          ; cmptb₀ = PC.faith-pf (~proof
                   PC.ₐ (S.%0 ℙ.∘ hi)
                        ~[ PC.∘ax-rf ˢ ⊙ ∘e PC.full-pf (S.RMF.rmfF%tr₁ ˢ) ⊙ ass ˢ ⊙ ∘e R.rpH.lift-tr r ] /
                   S.Q.kp.π/₁ 𝔼.∘ hiaux   ~[ S.Q.kp.×/tr₁ hiaux-pf ]∎
                   PC.ₐ (lo ℙ.∘ R.%0) ∎)
          ; cmptb₁ = PC.faith-pf (~proof
                   PC.ₐ (S.%1 ℙ.∘ hi)
                        ~[ PC.∘ax-rf ˢ ⊙ ∘e PC.full-pf (S.RMF.rmfF%tr₂ ˢ) ⊙ assˢ ⊙ ∘e R.rpH.lift-tr r ] /
                   S.Q.kp.π/₂ 𝔼.∘ hiaux   ~[ S.Q.kp.×/tr₂ hiaux-pf ]∎
                   PC.ₐ (lo ℙ.∘ R.%1) ∎)
          }
        }
        where open ecategory-aux-only 𝔼
      module ar = ℙ.peq-mor ar
      sqpf : g 𝔼.∘ R.Q.ar 𝔼.~ S.Q.ar 𝔼.∘ PC.ₐ ar.lo
      sqpf = (∘e PC.full-pf r ⊙ R.rpL.lift-tr) ˢ
           where open ecategory-aux-only 𝔼
      eqpf : PC↑ex.ₐ {R} {S} ar 𝔼.~ g
      eqpf = R.Q.epi-pf (q-sq (PCRel.ₐ ar) ⊙ ∘e PC.full-pf r ⊙ R.rpL.lift-tr)
           where open ecategory-aux-only 𝔼
                 open quot-of-eqrel-funct ex𝔼 using (q-sq)
    -- end PC↑ex-full
    
    module PC↑ex-faithful {R S : Exℙ.Obj} {f f' : || Exℙ.Hom R S ||}
                          (eqpf : PC↑ex.ₐ f 𝔼.~ PC↑ex.ₐ f')
                          where
      open ecategory-aux-only 𝔼
      private
        module R where
          open ℙ.peq R public
          module RMF = CRF R
          module rpL = PC.rprj Lo
          module rpH = PC.rprj Hi
          module Q = Q/PC↑ex R
        module S where
          open ℙ.peq S public
          module RMF = CRF S
          module rpL = PC.rprj Lo
          module rpH = PC.rprj Hi
          module Q = Q/PC↑ex S
        module f = ℙ.peq-mor f
        module f' = ℙ.peq-mor f'
        haux-pf : S.Q.ar 𝔼.∘ PC.ₐ f.lo 𝔼.~ S.Q.ar 𝔼.∘ PC.ₐ f'.lo
        haux-pf = ~proof S.Q.ar 𝔼.∘ PC.ₐ f.lo            ~[ q-sq (PCRel.ₐ {R} {S} f) ˢ ] /
                         PC↑ex.ₐ {R} {S} f 𝔼.∘ R.Q.ar    ~[ ∘e r eqpf ] /
                         PC↑ex.ₐ {R} {S} f' 𝔼.∘ R.Q.ar   ~[ q-sq (PCRel.ₐ {R} {S} f') ]∎
                         S.Q.ar 𝔼.∘ PC.ₐ f'.lo ∎
                where open quot-of-eqrel-funct ex𝔼 using (q-sq)
        haux : || 𝔼.Hom (PC.ₒ R.Lo) (PCRel.relOb S) ||
        haux = S.Q.kp.⟨ PC.ₐ f.lo , PC.ₐ f'.lo ⟩[ haux-pf ]
        h : || ℙ.Hom R.Lo S.Hi ||
        h = PC.full-ar (R.rpL.lift S.RMF.C-is-repi haux)
      pf : f Exℙ.~ f'
      pf = record
        { hty = h
        ; hty₀ = PC.faith-pf (~proof PC.ₐ (S.%0 ℙ.∘ h)
                        ~[ PC.∘ax-rf ˢ ⊙ ∘e PC.full-pf (S.RMF.rmfF%tr₁ ˢ) ⊙ assˢ ⊙ ∘e R.rpL.lift-tr r ] /
                                     S.RMF.r₁ 𝔼.∘ haux             ~[ S.Q.kp.×/tr₁ haux-pf ]∎
                                     PC.ₐ f.lo ∎)
        ; hty₁ = PC.faith-pf (~proof PC.ₐ (S.%1 ℙ.∘ h)
                        ~[ PC.∘ax-rf ˢ ⊙ ∘e PC.full-pf (S.RMF.rmfF%tr₂ ˢ) ⊙ assˢ ⊙ ∘e R.rpL.lift-tr r ] /
                                     S.RMF.r₂ 𝔼.∘ haux             ~[ S.Q.kp.×/tr₂ haux-pf ]∎
                                     PC.ₐ f'.lo ∎)
        }
    -- end PC↑ex-faithful
  -- end private

  PC↑ex-full : is-full PC↑ex.fctr
  PC↑ex-full = record
    { full-ar = λ {R} {S} g → ar {R} {S} g
    ; full-pf = λ {R} {S} {g} → eqpf {R} {S} g
    }
    where open PC↑ex-full
    
  PC↑ex-faithful : is-faithful PC↑ex.fctr
  PC↑ex-faithful = record
    { faith-pf = λ {R} {S} {f} {f'} eqpf → pf {R} {S} {f} {f'} eqpf
    }
    where open PC↑ex-faithful


  -------------------------------------------
  -- PC is essentailly surjective on objects
  -------------------------------------------

  -- peq in ℙ from quasi-exact seq in 𝔼
  private
    module peq-from-Obj (A : 𝔼.Obj) where
      -- cover of A
      module rc where
        open PC.rcov-of A public
        open PC.rprj Ob public
      private
        kpA : 𝔼.pullback-of rc.ar rc.ar
        kpA = ex𝔼.pb-of rc.ar rc.ar
        module kpA = 𝔼.pullback-of-not kpA
      exs : 𝔼.is-exact-seq kpA.π/₁ kpA.π/₂ rc.ar
      exs = record
        { iscoeq = 𝔼.repi-is-coeq-of-ker-pair rc.is-repi kpA
        ; iskerpair = kpA.×/ispbsq
        }
      module exs where
        open 𝔼.is-exact-seq exs using (iscoeq; iskerpair) public
        open 𝔼.pullback-of-not kpA public
        open 𝔼.is-coeq iscoeq public
        open 𝔼.is-eq-rel (𝔼.is-kerp+τpb→is-eqr (record { ispbsq = ×/ispbsq }) (ex𝔼.pb-of π/₂ π/₁)) public
      -- cover of the  kernel pair on A
      module rcK where
        open PC.rcov-of exs.ul public
        open PC.rprj Ob public
      private
        %0A %1A : || ℙ.Hom rcK.Ob rc.Ob ||
        %0A = PC.full-ar (exs.π/₁ 𝔼.∘ rcK.ar)
        %1A = PC.full-ar (exs.π/₂ 𝔼.∘ rcK.ar)

      peq/ : ℙ.peqOver rc.Ob
      peq/ = record
        { Hi = rcK.Ob
        ; %0 = %0A
        ; %1 = %1A
        ; ispeq = record
          { isρ = record
            { ρ = PC.full-ar (rc.lift rcK.is-repi exs.ρ)
            ; ρ-ax₀ = PC.faith-pf (~proof
                    PC.ₐ (%0A ℙ.∘ PC.full-ar (rc.lift rcK.is-repi exs.ρ))
                                                       ~[ PC.∘ax-rf ˢ ⊙ ∘e PC.full-pf PC.full-pf ⊙ assˢ ] /
                    exs.π/₁ 𝔼.∘ rcK.ar 𝔼.∘ rc.lift rcK.is-repi exs.ρ              ~[ ∘e rc.lift-tr r ] /
                    exs.π/₁ 𝔼.∘ exs.ρ                                               ~[ exs.ρ-ax₀ ⊙ PC.idˢ ]∎
                    PC.ₐ (ℙ.idar rc.Ob) ∎)
            ; ρ-ax₁ = PC.faith-pf (~proof
                    PC.ₐ (%1A ℙ.∘ PC.full-ar (rc.lift rcK.is-repi exs.ρ))
                                                       ~[ PC.∘ax-rf ˢ ⊙ ∘e PC.full-pf PC.full-pf ⊙ assˢ ] /
                    exs.π/₂ 𝔼.∘ rcK.ar 𝔼.∘ rc.lift rcK.is-repi exs.ρ              ~[ ∘e rc.lift-tr r ] /
                    exs.π/₂ 𝔼.∘ exs.ρ                                             ~[ exs.ρ-ax₁ ⊙ PC.idˢ ]∎
                    PC.ₐ (ℙ.idar rc.Ob) ∎)
            }
          ; isσ = record
            { σ = PC.full-ar (rcK.lift rcK.is-repi (exs.σ 𝔼.∘ rcK.ar))
            ; σ-ax₀ = PC.faith-pf (~proof
                    PC.ₐ (%0A ℙ.∘ PC.full-ar (rcK.lift rcK.is-repi (exs.σ 𝔼.∘ rcK.ar)))
                                                       ~[ PC.∘ax-rf ˢ ⊙ ∘e PC.full-pf PC.full-pf ⊙ assˢ ] /
                    exs.π/₁ 𝔼.∘ rcK.ar 𝔼.∘ rcK.lift rcK.is-repi (exs.σ 𝔼.∘ rcK.ar)      ~[ ∘e rcK.lift-tr r ] /
                    exs.π/₁ 𝔼.∘ exs.σ 𝔼.∘ rcK.ar                    ~[ ass ⊙ ∘e r exs.σ-ax₀ ⊙ PC.full-pf ˢ ]∎
                    PC.ₐ %1A ∎)
            ; σ-ax₁ = PC.faith-pf (~proof
                    PC.ₐ (%1A ℙ.∘ PC.full-ar (rcK.lift rcK.is-repi (exs.σ 𝔼.∘ rcK.ar)))
                                                       ~[ PC.∘ax-rf ˢ ⊙ ∘e PC.full-pf PC.full-pf ⊙ assˢ ] /
                    exs.π/₂ 𝔼.∘ rcK.ar 𝔼.∘ rcK.lift rcK.is-repi (exs.σ 𝔼.∘ rcK.ar)      ~[ ∘e rcK.lift-tr r ] /
                    exs.π/₂ 𝔼.∘ exs.σ 𝔼.∘ rcK.ar                    ~[ ass ⊙ ∘e r exs.σ-ax₁ ⊙ PC.full-pf ˢ ]∎
                    PC.ₐ %0A ∎)
            }
          ; τwpb = τwpb
          ; iswτ = record
            { τ = PC.full-ar (τwpb.lift rcK.is-repi τaux)
            ; τ-ax₀ = PC.faith-pf (~proof
                    PC.ₐ (%0A ℙ.∘ PC.full-ar (τwpb.lift rcK.is-repi τaux))
                                                        ~[ PC.∘ax-rf ˢ ⊙ ∘e PC.full-pf PC.full-pf ⊙ assˢ ] /
                    exs.π/₁ 𝔼.∘ rcK.ar 𝔼.∘ τwpb.lift rcK.is-repi τaux      ~[ ∘e τwpb.lift-tr r ] /
                    exs.π/₁ 𝔼.∘  τaux                                       ~[ exs.×/tr₁ τaux-pf ]∎
                    PC.ₐ (%0A ℙ.∘ τwpb.wπ/₁) ∎)
            ; τ-ax₁ = PC.faith-pf (~proof
                    PC.ₐ (%1A ℙ.∘ PC.full-ar (τwpb.lift rcK.is-repi τaux))
                                                        ~[ PC.∘ax-rf ˢ ⊙ ∘e PC.full-pf PC.full-pf ⊙ assˢ ] /
                    exs.π/₂ 𝔼.∘ rcK.ar 𝔼.∘ τwpb.lift rcK.is-repi τaux      ~[ ∘e τwpb.lift-tr r ] /
                    exs.π/₂ 𝔼.∘  τaux                                       ~[ exs.×/tr₂ τaux-pf ]∎
                    PC.ₐ (%1A ℙ.∘ τwpb.wπ/₂) ∎)
            }
          }
        }
        where open ecategory-aux-only 𝔼
              τwpb : ℙ.wpullback-of %1A %0A
              τwpb = fwlℙ.wpb-of %1A %0A
              module τwpb where
                open ℙ.wpullback-of τwpb public
                open PC.rprj ul public
              τaux-pf : rc.ar 𝔼.∘ PC.ₐ (%0A ℙ.∘ τwpb.wπ/₁) 𝔼.~ rc.ar 𝔼.∘ PC.ₐ (%1A ℙ.∘ τwpb.wπ/₂)
              τaux-pf = ~proof
                rc.ar 𝔼.∘ PC.ₐ (%0A ℙ.∘ τwpb.wπ/₁)                ~[ ∘e (PC.∘ax-rf ˢ ⊙ ∘e r PC.full-pf ⊙ assˢ) r ] /
                rc.ar 𝔼.∘ exs.π/₁ 𝔼.∘ rcK.ar 𝔼.∘ PC.ₐ τwpb.wπ/₁    ~[ ass ⊙ ∘e r exs.×/sqpf ⊙ assˢ ] /
                rc.ar 𝔼.∘ exs.π/₂ 𝔼.∘ rcK.ar 𝔼.∘ PC.ₐ τwpb.wπ/₁ ~[ ∘e (ass ⊙ ∘e r (PC.full-pf ˢ) ⊙ PC.∘ax-rf) r ] /
                rc.ar 𝔼.∘ PC.ₐ (%1A ℙ.∘ τwpb.wπ/₁)                  ~[ ∘e (PC.ext τwpb.w×/sqpf) r ] /
                rc.ar 𝔼.∘ PC.ₐ (%0A ℙ.∘ τwpb.wπ/₂)                 ~[ ∘e (PC.∘ax-rf ˢ ⊙ ∘e r PC.full-pf ⊙ assˢ) r ] /
                rc.ar 𝔼.∘ exs.π/₁ 𝔼.∘ rcK.ar 𝔼.∘ PC.ₐ τwpb.wπ/₂    ~[ ass ⊙ ∘e r exs.×/sqpf ⊙ assˢ ] /
                rc.ar 𝔼.∘ exs.π/₂ 𝔼.∘ rcK.ar 𝔼.∘ PC.ₐ τwpb.wπ/₂   ~[ ∘e (ass ⊙ ∘e r (PC.full-pf ˢ) ⊙ PC.∘ax-rf) r ]∎
                rc.ar 𝔼.∘ PC.ₐ (%1A ℙ.∘ τwpb.wπ/₂) ∎
              τaux : || 𝔼.Hom (PC.ₒ τwpb.ul) exs.ul ||
              τaux = exs.⟨ PC.ₐ (%0A ℙ.∘ τwpb.wπ/₁) , PC.ₐ (%1A ℙ.∘ τwpb.wπ/₂) ⟩[ τaux-pf ]
      peq : ℙ.peq
      peq = ℙ.mkpeq-c peq/
      module peq = ℙ.peq peq
      qexs : 𝔼.is-coeq (PC.ₐ peq.%0) (PC.ₐ peq.%1) rc.ar
      qexs = 𝔼.epi/coeq-so-coeq (𝔼.repi-is-epic rcK.is-repi) (PC.full-pf ˢ) (PC.full-pf ˢ) exs.iscoeq
           where open ecategory-aux-only 𝔼 using (_ˢ)
      --module qexs = 𝔼.is-coeq qexs
    -- end peq-from-Obj
  -- end private
  
  PC↑ex-ess-surj-obs : is-ess-surjective-ob PC↑ex.fctr
  PC↑ex-ess-surj-obs = record
    { ob = ob
    ; ar = iso.ar
    ; iso = iso.ar-iso
    }
    where ob : 𝔼.Obj → Exℙ.Obj
          ob = peq-from-Obj.peq
          module ob (A : 𝔼.Obj) = ℙ.peq (ob A)
          module iso (A : 𝔼.Obj) where
            open 𝔼.uniq-of-coequalisers {PC.ₒ (ob.Hi A)} {PC.ₒ (ob.Lo A)}
                                         {PC.ₐ (ob.%0 A)} {PC.ₐ (ob.%1 A)}
                                         {PC↑ex.ₒ (ob A)} {Q/PC↑ex.ar (ob A)}
                                         (qQ/PC↑ex (ob A))
            open same-rel-so-iso-coeq {A} {peq-from-Obj.rc.ar A} (peq-from-Obj.qexs A) public


  PC↑ex-eequiv : is-ess-equivalence PC↑ex.fctr
  PC↑ex-eequiv = record
    { isfull = PC↑ex-full
    ; isfaithful = PC↑ex-faithful
    ; isesurjobj = PC↑ex-ess-surj-obs
    }

  PC↑ex-is-eqv : is-equivalence PC↑ex.fctr
  PC↑ex-is-eqv = ess-equiv-is-equiv PC↑ex-eequiv
  module PC↑ex-is-eqv where
    open is-equivalence PC↑ex-is-eqv public
    private module Cat = Large-ecategory-aux Cat
    tr-inv : invF ○ PC ≅ₐ CVex ℙ [ fwlℙ ]
    tr-inv = eqv-tr {F = CVex ℙ [ fwlℙ ]} {PC↑ex.fctr} {invF} {PC} iseqv (CVex.unv.tr ex𝔼 PC.islcov)

{-
natiso-vcmp {ℙ} {Ex ℙ [ fwlℙ ]}
                         {invF ○ PC} {invF ○ PC↑ex.fctr ○ CVex ℙ [ fwlℙ ]} {CVex ℙ [ fwlℙ ]}
                         ( natiso-vcmp {F = invF ○ PC↑ex.fctr ○ CVex ℙ [ fwlℙ ]} {(invF ○ PC↑ex.fctr) ○ CVex ℙ [ fwlℙ ]} {CVex ℙ [ fwlℙ ]}
                                        (natiso-vcmp {F = (invF ○ PC↑ex.fctr) ○ CVex ℙ [ fwlℙ ]} {IdF ○ CVex ℙ [ fwlℙ ]} {CVex ℙ [ fwlℙ ]}
                                                     (○lid {F = CVex ℙ [ fwlℙ ]})
                                                     (natiso-hcmp {F = CVex ℙ [ fwlℙ ]} {CVex ℙ [ fwlℙ ]} {invF ○ PC↑ex.fctr} {IdF {Ex ℙ [ fwlℙ ]}}
                                                                  {!ι2!} (≅ₐrefl {F = CVex ℙ [ fwlℙ ]})))
                                        (○ass {F = CVex ℙ [ fwlℙ ]} {PC↑ex.fctr} {invF}) )
                         ( natiso-hcmp {ℙ} {𝔼} {Ex ℙ [ fwlℙ ]}
                                       {PC} {PC↑ex.fctr ○ CVex ℙ [ fwlℙ ]} {invF} {invF}
                                       (≅ₐrefl {F = invF}) (≅ₐsym (CVex.unv.tr ex𝔼 PC.islcov)) )
-}

{-
    tr-inv = ~proof efunctor-cmp {ℙ} {𝔼} {Ex ℙ [ fwlℙ ]} invF PC  --invF ○ PC
                                  ~[ {!∘e (CVex.unv.tr ex𝔼 PC.islcov ˢ) r!} ] /
                    
                    efunctor-cmp {ℙ} {𝔼} {Ex ℙ [ fwlℙ ]} invF
                                 (efunctor-cmp {ℙ} {Ex ℙ [ fwlℙ ]} {𝔼} PC↑ex.fctr CVex ℙ [ fwlℙ ])
                                  ~[ {!ass ⊙ lidgg r ?!} ]∎
                    CVex ℙ [ fwlℙ ] ∎
           where open Large-ecategory-aux-only Cat
                 -- open large-ecategory-aux (Fctr ℙ (Ex ℙ [ fwlℙ ]))
-}

-- end projcov-of-exact-is-eqv-to-CVconstr
