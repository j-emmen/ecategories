
-- disable the K axiom:

{-# OPTIONS --without-K  #-}

-- Agda version 2.5.4.1

module ecats.exact-completion.characterisation where

open import ecats.basic-defs.ecat-def&not
open import ecats.basic-defs.all-arrows
open import ecats.basic-props.epi&mono
open import ecats.basic-defs.regular-ecat
open import ecats.basic-defs.exact-ecat
open import ecats.basic-props.exact-ecat
open import ecats.finite-limits.all
open import ecats.functors.defs.efunctor-d&n
open import ecats.functors.defs.natural-transformation
open import ecats.functors.defs.basic-defs
open import ecats.functors.defs.preserving-functor
open import ecats.functors.defs.projective-cover
open import ecats.functors.defs.left-covering
open import ecats.functors.props.basic-props
open import ecats.functors.props.left-covering
open import ecats.functors.props.projective-cover
open import ecats.constructions.ecat-eqrel
open import ecats.exact-completion.CVconstruction
--open import ecats.exact-completion.finite-limits.fin-limits
--open import ecats.exact-completion.exact.is-regular
open import ecats.exact-completion.definition
open import ecats.exact-completion.embedding.universal-prop
open import ecats.exact-completion.embedding.universal-property.eqrel-from-peq




module exact-compl-character {𝔼 : ecategory} (ex𝔼 : is-exact 𝔼)
                             {ℙ : ecategory} {PC : efunctor ℙ 𝔼} (pjcPC : is-projective-cover PC)
                             where
  private
    module 𝔼 where
      open ecategory 𝔼 public
      open comm-shapes 𝔼 public
      open iso-defs 𝔼 public
      open epis&monos-defs 𝔼 public
      open epis&monos-props 𝔼 public
      open kernel-pairs-defs 𝔼 public
      open eq-rel-defs 𝔼 public
      open finite-limits-d&p 𝔼 public
    module ex𝔼 where
      open exact-cat-d&p ex𝔼 public
    reg𝔼 : is-regular 𝔼
    reg𝔼 = ex𝔼.exact-is-regular
    module ℙ where
      open ecategory ℙ public
      open comm-shapes ℙ public
      open epis&monos-defs ℙ public
      open epis&monos-props ℙ public
      open kernel-pairs-defs ℙ public
      open pseudo-eq-rel-defs ℙ public
      open finite-limits-d&p ℙ public
      open finite-weak-limits-d&p ℙ public
      open limits→weak-limits ℙ public
    fwlℙ : has-fin-weak-limits ℙ
    fwlℙ = proj-cov-has-wlim pjcPC ex𝔼.hasfl
    module PC where
      open efunctor-aux PC public
      open is-projective-cover pjcPC public
      open projective-cover-on-reg-cat-props reg𝔼 pjcPC using ()
                                                         renaming (PC-is-left-cov to islcov)
                                                         public
    module eqr (A : 𝔼.Obj) = projective-cover-on-reg-cat-props.Peq-from-Obj reg𝔼 pjcPC A
    module fwlℙ where
      open has-fin-weak-limits fwlℙ public
      open has-weak-pullbacks haswpb using (wpb-of) public
    module Exℙ where
      open ecategory Ex ℙ [ fwlℙ ] public
      open iso-defs Ex ℙ [ fwlℙ ] public
      open epis&monos-defs Ex ℙ [ fwlℙ ] public
      open epis&monos-props Ex ℙ [ fwlℙ ] public
      open image-fact-defs Ex ℙ [ fwlℙ ] public
    module Γex = efunctor-aux Γex ℙ [ fwlℙ ]
    module PC↑ex where
      open exact-compl-universal-prop fwlℙ ex𝔼 PC.islcov public
      open ↑ex public
    PC↑ex : efunctor Ex ℙ [ fwlℙ ] 𝔼
    PC↑ex = PC↑ex.↑ex
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
    Q/PC↑ex : (A : Exℙ.Obj) → 𝔼.coeq-of (PCRel.r₁ A) (PCRel.r₂ A)
    Q/PC↑ex A = ex𝔼.eqr-has-coeq (PCRel.eqrelover A)
    module Q/PC↑ex (A : Exℙ.Obj) where
      open 𝔼.coeq-of (Q/PC↑ex A) public
      repi : 𝔼.is-regular-epi {PCRel.baseOb A} {Ob} ar
      repi = record { coeq = iscoeq }
      open 𝔼.is-exact-seq (ex𝔼.ex-seq (PCRel.eqrelover A))
      module kp = 𝔼.pullback-of-not (𝔼.mkpb-of iskerpair)

    qQ/PC↑ex : (A : Exℙ.Obj) → 𝔼.is-coeq (PC.ₐ (ℙ.Peq.%0 A)) (PC.ₐ (ℙ.Peq.%1 A)) (Q/PC↑ex.ar A)
    qQ/PC↑ex A = 𝔼.epi/coeq-so-coeq (𝔼.repi-is-epic C-is-repi) rmfF%tr₁ rmfF%tr₂ (Q/PC↑ex.iscoeq A)
               where open CRF A
    module qQ/PC↑ex (A : Exℙ.Obj) = 𝔼.is-coeq (qQ/PC↑ex A)



  PC↑ex-ess-surj-obs : is-ess-surjective-ob PC↑ex
  PC↑ex-ess-surj-obs = record
    { ob = ob
    ; ar = iso.ar
    ; iso = iso.ar-iso
    }
    where ob : (A : 𝔼.Obj) → Exℙ.Obj
          ob A = eqr.peq A
          module ob (A : 𝔼.Obj) = ℙ.Peq (ob A)
          module iso (A : 𝔼.Obj) where
            open 𝔼.uniq-of-coequalisers {PC.ₒ (ob.Hi A)} {PC.ₒ (ob.Lo A)}
                                         {PC.ₐ (ob.%0 A)} {PC.ₐ (ob.%1 A)}
                                         {PC↑ex.ₒ (ob A)} {Q/PC↑ex.ar (ob A)}
                                         (qQ/PC↑ex (ob A))
            open same-rel-so-iso-coeq {A} {eqr.rc.ar A} (eqr.qexs A) public


  private
    module PC↑ex-full {R S : Exℙ.Obj} (g : || 𝔼.Hom (PC↑ex.ₒ R) (PC↑ex.ₒ S) ||) where
      private
        module R where
          open ℙ.Peq R public
          module RMF = CRF R
          module rpL = PC.rprj Lo
          module rpH = PC.rprj Hi
          module Q = Q/PC↑ex R
        module S where
          open ℙ.Peq S public
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
      ar : ℙ.Peq-mor R S
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
      module ar = ℙ.Peq-mor ar
      sqpf : g 𝔼.∘ R.Q.ar 𝔼.~ S.Q.ar 𝔼.∘ PC.ₐ ar.lo
      sqpf = (∘e PC.full-pf r ⊙ R.rpL.lift-tr) ˢ
           where open ecategory-aux-only 𝔼
      eqpf : PC↑ex.ₐ {R} {S} ar 𝔼.~ g
      eqpf = R.Q.epi-pf (q-sq (PCRel.ₐ ar) ⊙ ∘e PC.full-pf r ⊙ R.rpL.lift-tr)
           where open ecategory-aux-only 𝔼
                 open quot-of-eqrel-funct ex𝔼 using (q-sq)
    -- end PC↑ex-full

  PC↑ex-full : is-full PC↑ex
  PC↑ex-full = record
    { full-ar = λ {R} {S} g → ar {R} {S} g
    ; full-pf = λ {R} {S} {g} → eqpf {R} {S} g
    }
    where open PC↑ex-full

  private
    module PC↑ex-faithful {R S : Exℙ.Obj} {f f' : || Exℙ.Hom R S ||}
                          (eqpf : PC↑ex.ₐ f 𝔼.~ PC↑ex.ₐ f')
                          where
      open ecategory-aux-only 𝔼
      private
        module R where
          open ℙ.Peq R public
          module RMF = CRF R
          module rpL = PC.rprj Lo
          module rpH = PC.rprj Hi
          module Q = Q/PC↑ex R
        module S where
          open ℙ.Peq S public
          module RMF = CRF S
          module rpL = PC.rprj Lo
          module rpH = PC.rprj Hi
          module Q = Q/PC↑ex S
        module f = ℙ.Peq-mor f
        module f' = ℙ.Peq-mor f'
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
    
  PC↑ex-faithful : is-faithful PC↑ex
  PC↑ex-faithful = record
    { faith-pf = λ {R} {S} {f} {f'} eqpf → pf {R} {S} {f} {f'} eqpf
    }
    where open PC↑ex-faithful


  PC↑ex-eequiv : is-ess-equivalence PC↑ex
  PC↑ex-eequiv = record
    { isfull = PC↑ex-full
    ; isfaithful = PC↑ex-faithful
    ; isesurjobj = PC↑ex-ess-surj-obs
    }

  PC↑ex-is-eqv : is-equivalence PC↑ex
  PC↑ex-is-eqv = ess-equiv-is-equiv PC↑ex-eequiv
-- end exact-compl-character
