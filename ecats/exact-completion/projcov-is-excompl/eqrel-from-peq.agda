
{-# OPTIONS --without-K #-}

module ecats.exact-completion.projcov-is-excompl.eqrel-from-peq where

open import ecats.basic-defs.ecat-def&not
open import ecats.basic-defs.all-arrows
open import ecats.basic-props.epi&mono
open import ecats.basic-defs.regular-ecat
open import ecats.basic-props.regular-ecat
open import ecats.finite-limits.all
open import ecats.constructions.ecat-eqrel
open import ecats.functors.defs.efunctor-d&n
open import ecats.functors.defs.natural-transformation
open import ecats.functors.defs.projective-cover
open import ecats.functors.defs.left-covering
open import ecats.functors.props.projective-cover
open import ecats.functors.props.left-covering
open import ecats.exact-completion.CVconstruction



-- Definition of the functor 𝔸 → EqRel 𝔹 induced by a left covering ℙ → 𝔹 into 𝔹 regular.

module eqrel-from-peq-funct {𝔸 : ecategory}(reg𝔸 : is-regular 𝔸)
                            {ℙ : ecategory}{PC : efunctor ℙ 𝔸}(pjcPC : is-projective-cover PC)
                            where
  private
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
    module 𝔸 where
      open ecategory 𝔸 public
      open comm-shapes 𝔸 public
      open iso-defs 𝔸 public
      open epis&monos-defs 𝔸 public
      open epis&monos-props 𝔸 public
      open kernel-pairs-defs 𝔸 public
      open eq-rel-defs 𝔸 public
      open finite-limits-d&p 𝔸 public
      --open finite-weak-limits-d&p 𝔸 public
      --open limits→weak-limits 𝔸 public
      --open relations-among-limit-diagrams 𝔸 public
      open projective-defs 𝔸 public
    module reg𝔸 where
      open regular-cat-d&p reg𝔸 public
      --open has-fin-limits hasfl public
      open has-terminal hastrm public
      open has-bin-products hasprd using (prd-of) public
      open has-equalisers haseql using (eql-of) public
      open has-pullbacks haspb using (pb-of) public
      open has-bows hasbw using (bw-of) public
    fwlℙ : has-fin-weak-limits ℙ
    fwlℙ = proj-cov-has-wlim pjcPC reg𝔸.hasfl
    module fwlℙ where
      open has-fin-weak-limits fwlℙ public
      open has-weak-pullbacks haswpb using (wpb-of) public
    module PC where
      open efunctor-aux PC public
      open is-projective-cover pjcPC public
      open projective-cover-props reg𝔸.hasfl pjcPC public


  module eqrel-from-peq-via-left-covering {𝔹 : ecategory} (reg𝔹 : is-regular 𝔹)
                                          {F : efunctor ℙ 𝔹} (lcovF : is-left-covering F)
                                          where
    private
      module 𝔹 where
        open ecategory 𝔹 public
        open comm-shapes 𝔹 public
        open epis&monos-defs 𝔹 public
        open epis&monos-props 𝔹 public
        open eq-rel-defs 𝔹 public
        open finite-limits-d&p 𝔹 public
      module reg𝔹 where
        open is-regular reg𝔹 public
        open has-bin-products hasprd using (prd-of) public
        open has-pullbacks haspb using (pb-of) public
        open regular-cat-props reg𝔹 public
      module F = efunctor-aux F
      module lcF = is-left-covering lcovF

    module eqrel-as-repi-mono-fact (A : ℙ.peq) where
      private
        module A = ℙ.peq A
        module FAL² = 𝔹.product-of-not (reg𝔹.prd-of (F.ₒ A.Lo) (F.ₒ A.Lo))
      -- main definitions, to be used elsewhere
      F% : || 𝔹.Hom (F.ₒ A.Hi) FAL².O12 ||
      F% = FAL².< F.ₐ A.%0 , F.ₐ A.%1 >
      module rmfF% = reg𝔹.rmf-of F% --𝔹.repi-mono-fact-of rmfF%
      module CF% = 𝔹.is-regular-epi rmfF%.C-is-repi
      CF%cov : 𝔹.reg-cover-of rmfF%.Ob
      CF%cov = record { Ob = F.ₒ A.Hi ; cov = record { ar = rmfF%.C ; is-repi = rmfF%.C-is-repi } }
      r₁ r₂ : || 𝔹.Hom rmfF%.Ob (F.ₒ A.Lo) ||    
      r₁ = FAL².π₁ 𝔹.∘ rmfF%.M
      r₂ = FAL².π₂ 𝔹.∘ rmfF%.M
      rmfF%tr₁ = ~proof r₁ 𝔹.∘ rmfF%.C            ~[ assˢ ⊙ ∘e rmfF%.tr r  ] /
                        FAL².π₁ 𝔹.∘ F%            ~[ FAL².×tr₁ ]∎
                        F.ₐ A.%0 ∎
               where open ecategory-aux-only 𝔹                     
      rmfF%tr₂ = ~proof r₂ 𝔹.∘ rmfF%.C           ~[ assˢ ⊙ ∘e rmfF%.tr r  ] /
                        FAL².π₂ 𝔹.∘ F%           ~[ FAL².×tr₂ ]∎
                        F.ₐ A.%1 ∎
               where open ecategory-aux-only 𝔹
      F%rel : F% 𝔹.∘ CF%.rel₁ 𝔹.~ F% 𝔹.∘ CF%.rel₂
      F%rel = ∘e r (rmfF%.tr ˢ) ⊙ assˢ ⊙ ∘e CF%.eq r ⊙ ass ⊙ ∘e r rmfF%.tr
            where open ecategory-aux-only 𝔹

      -- auxiliary definitions
      private
      -- jointly monic
        rjm : 𝔹.is-jointly-monic/ (𝔹.mkspan/ r₁ r₂)
        rjm = 𝔹.<>monic→isjm/-ar FAL².×of rmfF%.M-is-monic
      -- reflexive
        rρ : || 𝔹.Hom (F.ₒ A.Lo) rmfF%.Ob ||
        rρ  = rmfF%.C 𝔹.∘ F.ₐ A.ρ    
      -- symmetric
        module σrmfF% = reg𝔹.rmf-of FAL².< F.ₐ A.%1 , F.ₐ A.%0 >
        rσ-monic : 𝔹.is-monic FAL².< r₂ , r₁ >
        rσ-monic = 𝔹.isjm/→<>monic (𝔹.jointly-monic-sym rjm) FAL².×of
        rσ-comm : FAL².< r₂ , r₁ > 𝔹.∘ rmfF%.C 𝔹.∘ F.ₐ A.σ 𝔹.~ F%
        rσ-comm = ~proof
          FAL².< r₂ , r₁ > 𝔹.∘ rmfF%.C 𝔹.∘ F.ₐ A.σ   ~[ ass ⊙ ∘e r (FAL².<>ar~<> rmfF%tr₂ rmfF%tr₁) ] /
          FAL².< F.ₐ A.%1 , F.ₐ A.%0 > 𝔹.∘ F.ₐ A.σ    ~[ FAL².<>ar~<> (F.∘ax A.σ-ax₁) (F.∘ax A.σ-ax₀) ]∎
          F% ∎
                    where open ecategory-aux-only 𝔹
        rσ-eq : (rmfF%.C 𝔹.∘ F.ₐ A.σ) 𝔹.∘ CF%.rel₁ 𝔹.~ (rmfF%.C 𝔹.∘ F.ₐ A.σ) 𝔹.∘ CF%.rel₂
        rσ-eq = mono-pf (~proof
          FAL².< r₂ , r₁ > 𝔹.∘ (rmfF%.C 𝔹.∘ F.ₐ A.σ) 𝔹.∘ CF%.rel₁   ~[ ass ⊙ ∘e r rσ-comm  ] /
          F% 𝔹.∘ CF%.rel₁                                            ~[ ∘e r (rmfF%.tr ˢ) ⊙ assˢ ] /
          rmfF%.M 𝔹.∘ rmfF%.C 𝔹.∘ CF%.rel₁                          ~[ ∘e CF%.eq r ] /
          rmfF%.M 𝔹.∘ rmfF%.C 𝔹.∘ CF%.rel₂                          ~[ ass ⊙ ∘e r rmfF%.tr ] /
          F% 𝔹.∘ CF%.rel₂                                            ~[ ∘e r (rσ-comm ˢ) ⊙ assˢ ]∎
          FAL².< r₂ , r₁ > 𝔹.∘ (rmfF%.C 𝔹.∘ F.ₐ A.σ) 𝔹.∘ CF%.rel₂ ∎)
                  where open ecategory-aux-only 𝔹
                        open 𝔹.is-monic rσ-monic
        rσ : || 𝔹.Hom rmfF%.Ob rmfF%.Ob ||
        rσ = CF%.univ (rmfF%.C 𝔹.∘ F.ₐ A.σ) rσ-eq
        rσ-ax₀ : r₁ 𝔹.∘ rσ 𝔹.~ r₂
        rσ-ax₀ = CF%.epi-pf (~proof
          (r₁ 𝔹.∘ rσ) 𝔹.∘ rmfF%.C        ~[ assˢ ⊙ ∘e (CF%.univ-eq rσ-eq) r ] /
          r₁ 𝔹.∘ rmfF%.C 𝔹.∘ F.ₐ A.σ     ~[ ass ⊙ ∘e r rmfF%tr₁ ⊙ F.∘ax A.σ-ax₀ ⊙ rmfF%tr₂ ˢ ]∎
          r₂ 𝔹.∘ rmfF%.C ∎)
               where open ecategory-aux-only 𝔹
        rσ-ax₁ : r₂ 𝔹.∘ rσ 𝔹.~ r₁
        rσ-ax₁ = CF%.epi-pf (~proof
          (r₂ 𝔹.∘ rσ) 𝔹.∘ rmfF%.C        ~[ assˢ ⊙ ∘e (CF%.univ-eq rσ-eq) r ] /
          r₂ 𝔹.∘ rmfF%.C 𝔹.∘ F.ₐ A.σ     ~[ ass ⊙ ∘e r rmfF%tr₂ ⊙ F.∘ax A.σ-ax₁ ⊙ rmfF%tr₁ ˢ ]∎
          r₁ 𝔹.∘ rmfF%.C ∎)
               where open ecategory-aux-only 𝔹
      -- transitive
        τrpb : 𝔹.pullback-of r₂ r₁
        τrpb = reg𝔹.pb-of r₂ r₁
        module τrpb = 𝔹.pullback-of-not τrpb
        module τAwpb = ℙ.wpullback-of-not A.τwpb
        module C×C where
          open reg𝔹.pb-of-reg-covers-is-reg-cover-of-pb τrpb CF%cov CF%cov public
          open 𝔹.is-regular-epi diagl-repi public
        τF%pb : 𝔹.pullback-of (F.ₐ A.%1) (F.ₐ A.%0)
        τF%pb = 𝔹.mkpb-of (𝔹.×/ext-dr C×C.outsq-pb rmfF%tr₂ rmfF%tr₁)
        module τF%pb = 𝔹.pullback-of-not τF%pb
        F%τeq : F% 𝔹.∘ F.ₐ A.τ   𝔹.~   FAL².< F.ₐ (A.%0 ℙ.∘ τAwpb.wπ/₁) , F.ₐ (A.%1 ℙ.∘ τAwpb.wπ/₂) >
        F%τeq = FAL².<>ar~<> (F.∘ax A.τ-ax₀) (F.∘ax A.τ-ax₁)          
        outcov-pf = F.ₐ A.%1 𝔹.∘ F.ₐ τAwpb.wπ/₁  ~[ F.∘ax-rf ⊙ F.ext τAwpb.w×/sqpf ⊙ F.∘ax-rfˢ ]
                    F.ₐ A.%0 𝔹.∘ F.ₐ τAwpb.wπ/₂
                  where open ecategory-aux-only 𝔹
        outcov : || 𝔹.Hom (F.ₒ τAwpb.ul) τF%pb.ul ||
        outcov = τF%pb.⟨ F.ₐ τAwpb.wπ/₁ , F.ₐ τAwpb.wπ/₂ ⟩[ outcov-pf ]
        outcov-repi : 𝔹.is-regular-epi outcov
        outcov-repi = lcF.pbuniv-is-repi A.τwpb τF%pb (τF%pb.×/tr₁ outcov-pf) (τF%pb.×/tr₂ outcov-pf)        
        τcov : || 𝔹.Hom (F.ₒ τAwpb.ul) τrpb.ul ||
        τcov = C×C.diagl 𝔹.∘ outcov 
        τcov-repi : 𝔹.is-regular-epi τcov
        τcov-repi = ∘c C×C.diagl-repi outcov-repi
                  where open is-ecat-congr reg𝔹.regular-epi-is-congr
        private
          module τc = 𝔹.is-regular-epi τcov-repi
        rmfF%τ-pf-aux1 = ~proof
          r₁ 𝔹.∘ τrpb.π/₁ 𝔹.∘ τcov                     ~[ ∘e (ass ⊙ ∘e r C×C.trl₁) r ] /
          r₁ 𝔹.∘ (rmfF%.C 𝔹.∘ τF%pb.π/₁) 𝔹.∘ outcov   ~[ ass ⊙ ∘e r (ass ⊙ ∘e r rmfF%tr₁) ⊙ assˢ ] /
          F.ₐ A.%0 𝔹.∘ τF%pb.π/₁ 𝔹.∘ outcov            ~[  ∘e (τF%pb.×/tr₁ outcov-pf) r ⊙ F.∘ax-rf ]∎
          F.ₐ (A.%0 ℙ.∘ τAwpb.wπ/₁) ∎
                     where open ecategory-aux-only 𝔹
        rmfF%τ-pf-aux2 = ~proof
          r₂ 𝔹.∘ τrpb.π/₂ 𝔹.∘ τcov                     ~[ ∘e (ass ⊙ ∘e r C×C.trl₂) r ] /
          r₂ 𝔹.∘ (rmfF%.C 𝔹.∘ τF%pb.π/₂) 𝔹.∘ outcov   ~[ ass ⊙ ∘e r (ass ⊙ ∘e r rmfF%tr₂) ⊙ assˢ ] /
          F.ₐ A.%1 𝔹.∘ τF%pb.π/₂ 𝔹.∘ outcov            ~[  ∘e (τF%pb.×/tr₂ outcov-pf) r ⊙ F.∘ax-rf ]∎
          F.ₐ (A.%1 ℙ.∘ τAwpb.wπ/₂) ∎
                     where open ecategory-aux-only 𝔹
        rmfF%τ-pf-aux : FAL².< F.ₐ (A.%0 ℙ.∘ τAwpb.wπ/₁) , F.ₐ (A.%1 ℙ.∘ τAwpb.wπ/₂) >
                               𝔹.~ FAL².< r₁ 𝔹.∘ τrpb.π/₁ , r₂ 𝔹.∘ τrpb.π/₂ > 𝔹.∘ τcov
        rmfF%τ-pf-aux = FAL².<>ar~<>ˢ (assˢ ⊙ rmfF%τ-pf-aux1) (assˢ ⊙ rmfF%τ-pf-aux2)
                      where open ecategory-aux-only 𝔹
        rmfF%τ-pf : (rmfF%.C 𝔹.∘ F.ₐ A.τ) 𝔹.∘ τc.rel₁ 𝔹.~ (rmfF%.C 𝔹.∘ F.ₐ A.τ) 𝔹.∘ τc.rel₂
        rmfF%τ-pf = mono-pf (~proof
          rmfF%.M 𝔹.∘ (rmfF%.C 𝔹.∘ F.ₐ A.τ) 𝔹.∘ τc.rel₁                        ~[ ass ⊙ ∘e r (ass ⊙ ∘e r rmfF%.tr) ] /
          (F% 𝔹.∘ F.ₐ A.τ) 𝔹.∘ τc.rel₁                                                ~[ ∘e r F%τeq ] /
          FAL².< F.ₐ (A.%0 ℙ.∘ τAwpb.wπ/₁) , F.ₐ (A.%1 ℙ.∘ τAwpb.wπ/₂) > 𝔹.∘ τc.rel₁   ~[ ∘e r rmfF%τ-pf-aux ⊙ assˢ  ] /
          FAL².< r₁ 𝔹.∘ τrpb.π/₁ , r₂ 𝔹.∘ τrpb.π/₂ > 𝔹.∘ τcov 𝔹.∘ τc.rel₁            ~[ ∘e τc.eq r  ] /
          FAL².< r₁ 𝔹.∘ τrpb.π/₁ , r₂ 𝔹.∘ τrpb.π/₂ > 𝔹.∘ τcov 𝔹.∘ τc.rel₂         ~[  ass ⊙ ∘e r (rmfF%τ-pf-aux ˢ) ] /
          FAL².< F.ₐ (A.%0 ℙ.∘ τAwpb.wπ/₁) , F.ₐ (A.%1 ℙ.∘ τAwpb.wπ/₂) > 𝔹.∘ τc.rel₂   ~[ ∘e r (F%τeq ˢ) ] /
          (F% 𝔹.∘ F.ₐ A.τ) 𝔹.∘ τc.rel₂                                      ~[ ∘e r (∘e r (rmfF%.tr ˢ) ⊙ assˢ) ⊙ assˢ ]∎
          rmfF%.M 𝔹.∘ (rmfF%.C 𝔹.∘ F.ₐ A.τ) 𝔹.∘ τc.rel₂ ∎)
                where open ecategory-aux-only 𝔹
                      open 𝔹.is-monic rmfF%.M-is-monic
        rmfF%τ : || 𝔹.Hom τrpb.ul rmfF%.Ob ||
        rmfF%τ = τc.univ {rmfF%.Ob} (rmfF%.C 𝔹.∘ F.ₐ A.τ) rmfF%τ-pf
        rmfF%τ-tr : rmfF%τ 𝔹.∘ τcov 𝔹.~ rmfF%.C 𝔹.∘ F.ₐ A.τ
        rmfF%τ-tr = τc.univ-eq {rmfF%.Ob} {rmfF%.C 𝔹.∘ F.ₐ A.τ} rmfF%τ-pf
        rmfF%τ-ax₀ : r₁ 𝔹.∘ rmfF%τ 𝔹.~ r₁ 𝔹.∘ τrpb.π/₁
        rmfF%τ-ax₀ = τc.epi-pf (~proof
          (r₁ 𝔹.∘ rmfF%τ) 𝔹.∘ τcov            ~[ assˢ ⊙ ∘e rmfF%τ-tr r ⊙ ass ⊙ ∘e r rmfF%tr₁ ] /
          F.ₐ A.%0 𝔹.∘ F.ₐ A.τ                 ~[ F.∘ax A.τ-ax₀ ⊙ rmfF%τ-pf-aux1 ˢ ⊙ ass ]∎
          (r₁ 𝔹.∘ τrpb.π/₁) 𝔹.∘ τcov ∎)
                   where open ecategory-aux-only 𝔹
        rmfF%τ-ax₁ = τc.epi-pf (~proof
          (r₂ 𝔹.∘ rmfF%τ) 𝔹.∘ τcov            ~[ assˢ ⊙ ∘e rmfF%τ-tr r ⊙ ass ⊙ ∘e r rmfF%tr₂ ] / 
          F.ₐ A.%1 𝔹.∘ F.ₐ A.τ                 ~[ F.∘ax A.τ-ax₁ ⊙ (rmfF%τ-pf-aux2 ˢ) ⊙ ass ]∎
          (r₂ 𝔹.∘ τrpb.π/₂) 𝔹.∘ τcov ∎)
                   where open ecategory-aux-only 𝔹

      -- equivalece relation
        iseqr : 𝔹.is-eq-rel {rmfF%.Ob} {F.ₒ A.Lo} r₁ r₂
        iseqr = record
          { isjm/ = rjm
          ; isρ = record
                { ρ = rρ
                ; ρ-ax₀ = ass ⊙ ∘e r rmfF%tr₁ ⊙ F.∘ax-rf ⊙ F.idax A.ρ-ax₀
                ; ρ-ax₁ = ass ⊙ ∘e r rmfF%tr₂ ⊙ F.∘ax-rf ⊙ F.idax A.ρ-ax₁
                }
          ; isσ = record
                { σ = rσ
                ; σ-ax₀ = rσ-ax₀
                ; σ-ax₁ = rσ-ax₁
                }
          ; τpb = τrpb
          ; isτ = record
                { τ = rmfF%τ
                ; τ-ax₀ = rmfF%τ-ax₀
                ; τ-ax₁ = rmfF%τ-ax₁
                }
          }
          where open ecategory-aux-only 𝔹
      -- end private

      eqrel/ : 𝔹.eqrel-over (F.ₒ A.Lo)
      eqrel/ = record
        { relOb = rmfF%.Ob
        ; r₁ = r₁
        ; r₂ = r₂
        ; iseqrel = iseqr
        }
    -- end eqrel-as-repi-mono-fact

    --eqr/ : (A : Exℙ.Obj) → 𝔹.eqrel-over (F.ₒ (ℙ.peq.Lo A))
    --eqr/ A = F.eqrel-from-peq-via-left-covering.eqrel/ A

    private
      Exℙ : ecategory
      Exℙ = Ex ℙ [ fwlℙ ]
      module Exℙ where
        open ecategory Exℙ public

    private
      module CRF% (A : ℙ.peq) where
        open eqrel-as-repi-mono-fact A public -- hiding (eqrel/)
        open rmfF% public
        open CF% public

    eqr : Exℙ.Obj → 𝔹.eqrel
    eqr A = record { eqrelover = CRF%.eqrel/ A }
    {-module eqr where
      open 𝔹.eqrel-over public
      open 𝔹.eqrel-mor public-}

    eqr-ar : {A B : Exℙ.Obj} (f : || Exℙ.Hom A B ||) → 𝔹.eqrel-mor (eqr A) (eqr B)
    eqr-ar {A} {B} f = record
      { base-ar = F.ₐ f.lo
      ; isext = record
              { rel-ar = rel-ar
              ; cmptb₀ = CRA.epi-pf (~proof
                       (CRB.r₁ 𝔹.∘ rel-ar) 𝔹.∘ CRA.C      ~[ assˢ ⊙ ∘e rel-ar-tr r ] /
                       CRB.r₁ 𝔹.∘ CRB.C 𝔹.∘ F.ₐ f.hi      ~[ ass ⊙ ∘e r CRB.rmfF%tr₁ ⊙ F.∘∘ f.cmptb₀ ] /
                       F.ₐ f.lo 𝔹.∘ F.ₐ A.%0                ~[ ∘e (CRA.rmfF%tr₁ ˢ) r ⊙ ass ]∎
                       (F.ₐ f.lo 𝔹.∘ CRA.r₁) 𝔹.∘ CRA.C ∎)
              ; cmptb₁ = CRA.epi-pf (~proof
                       (CRB.r₂ 𝔹.∘ rel-ar) 𝔹.∘ CRA.C      ~[ assˢ ⊙ ∘e rel-ar-tr r ] /
                       CRB.r₂ 𝔹.∘ CRB.C 𝔹.∘ F.ₐ f.hi      ~[ ass ⊙ ∘e r CRB.rmfF%tr₂ ⊙ F.∘∘ f.cmptb₁ ] /
                       F.ₐ f.lo 𝔹.∘ F.ₐ A.%1                ~[ ∘e (CRA.rmfF%tr₂ ˢ) r ⊙ ass ]∎
                       (F.ₐ f.lo 𝔹.∘ CRA.r₂) 𝔹.∘ CRA.C ∎)
              }
      }
      where open ecategory-aux-only 𝔹
            module f = ℙ.peq-mor f
            module A = ℙ.peq A
            module FAL² = 𝔹.product-of-not (reg𝔹.prd-of (F.ₒ A.Lo) (F.ₒ A.Lo))
            module B = ℙ.peq B
            module FBL² = 𝔹.product-of-not (reg𝔹.prd-of (F.ₒ B.Lo) (F.ₒ B.Lo))
            open 𝔹.×ₐdef FBL².prdsp FAL².prdsp
            Ffl×Ffl : || 𝔹.Hom FAL².O12 FBL².O12 ||
            Ffl×Ffl = F.ₐ f.lo ×ₐ F.ₐ f.lo
            module CRA = CRF% A
            module CRB = CRF% B
            cmptbF% : CRB.F% 𝔹.∘ F.ₐ f.hi 𝔹.~ Ffl×Ffl 𝔹.∘ CRA.F%
            cmptbF% = FBL².<>ar~<>ar (F.∘∘ f.cmptb₀ ⊙ ∘e (FAL².×tr₁ {g = F.ₐ A.%1} ˢ) r ⊙ ass)
                                     (F.∘∘ f.cmptb₁ ⊙ ∘e (FAL².×tr₂ {f = F.ₐ A.%0} ˢ) r ⊙ ass)
            rel-ar-pf : (CRB.C 𝔹.∘ F.ₐ f.hi) 𝔹.∘ CRA.rel₁ 𝔹.~ (CRB.C 𝔹.∘ F.ₐ f.hi) 𝔹.∘ CRA.rel₂
            rel-ar-pf = CRB.mono-pf (~proof
              CRB.M 𝔹.∘ (CRB.C 𝔹.∘ F.ₐ f.hi) 𝔹.∘ CRA.rel₁    ~[ ass ⊙ ∘e r (ass ⊙ ∘e r CRB.tr ⊙ cmptbF%) ⊙ assˢ ] /
              Ffl×Ffl 𝔹.∘ CRA.F% 𝔹.∘ CRA.rel₁                ~[ ∘e CRA.F%rel r ] /
              Ffl×Ffl 𝔹.∘ CRA.F% 𝔹.∘ CRA.rel₂            ~[ ass ⊙ ∘e r (cmptbF% ˢ ⊙ ∘e r (CRB.tr ˢ) ⊙ assˢ) ⊙ assˢ ]∎
              CRB.M 𝔹.∘ (CRB.C 𝔹.∘ F.ₐ f.hi) 𝔹.∘ CRA.rel₂ ∎)
            rel-ar : || 𝔹.Hom CRA.Ob CRB.Ob ||
            rel-ar = CRA.univ {CRB.Ob} (CRB.C 𝔹.∘ F.ₐ f.hi) rel-ar-pf
            rel-ar-tr : rel-ar 𝔹.∘ CRA.C 𝔹.~ CRB.C 𝔹.∘ F.ₐ f.hi
            rel-ar-tr = CRA.univ-eq {CRB.Ob} {CRB.C 𝔹.∘ F.ₐ f.hi} rel-ar-pf

    eqr-ar-ext : {A B : Exℙ.Obj} (f f' : || Exℙ.Hom A B ||)
                    → f Exℙ.~ f' → 𝔹.eqrel-mor-eq (eqr-ar {A} {B} f) (eqr-ar {A} {B} f')
    eqr-ar-ext {A} {B} f f' hty = record
      { wit = CRB.C 𝔹.∘ F.ₐ f~f'.hty
      ; wit₀ = ~proof CRB.r₁ 𝔹.∘ CRB.C 𝔹.∘ F.ₐ f~f'.hty      ~[ ass ⊙ ∘e r CRB.rmfF%tr₁ ] /
                      F.ₐ B.%0 𝔹.∘ F.ₐ f~f'.hty               ~[ F.∘ax f~f'.hty₀ ]∎
                      F.ₐ f.lo ∎
      ; wit₁ = ~proof CRB.r₂ 𝔹.∘ CRB.C 𝔹.∘ F.ₐ f~f'.hty      ~[ ass ⊙ ∘e r CRB.rmfF%tr₂ ] /
                      F.ₐ B.%1 𝔹.∘ F.ₐ f~f'.hty               ~[ F.∘ax f~f'.hty₁ ]∎
                      F.ₐ f'.lo ∎
      }
      where module B = ℙ.peq B
            module f = ℙ.peq-mor f
            module f' = ℙ.peq-mor f'
            module f~f' = ℙ.peq-mor-eq hty
            module CRB = CRF% B
            open ecategory-aux-only 𝔹
  -- end eqrel-from-peq-via-left-covering


  Rel :  {𝔹 : ecategory} (reg𝔹 : is-regular 𝔹) {F : efunctor ℙ 𝔹} (Flcov : is-left-covering F)
                         → efunctor Ex ℙ [ fwlℙ ] (EqRel 𝔹)
  Rel {𝔹} reg𝔹 {F} Flcov = record
    { FObj = eqr
    ; FHom = eqr-ar
    ; isF = record
          { ext = λ {A} {B} {f} {f'} pf → eqr-ar-ext f f' pf
          ; id = λ {A} → 𝔹.eqrel-mor-eq-ext F.id
          ; cmp = λ {A} {B} {C} f g → 𝔹.eqrel-mor-eq-ext F.∘ax-rf
          }
    }
    where open eqrel-from-peq-via-left-covering reg𝔹 Flcov
          module 𝔹 = eq-rel-defs 𝔹
          module F = efunctor-aux F


  module Rel-on-free  {𝔹 : ecategory} (reg𝔹 : is-regular 𝔹) {F : efunctor ℙ 𝔹} (Flcov : is-left-covering F) where
    private
      module 𝔹 = ecategory 𝔹
      module Exℙ = ecategory (Ex ℙ [ fwlℙ ])
      module F = efunctor-aux F
      module I = efunctor-aux (Rel reg𝔹 Flcov)
      module ΔER = efunctor-aux (ΔER 𝔹)
    
    module CRF% (A : Exℙ.Obj) where
      open eqrel-from-peq-via-left-covering reg𝔹 Flcov
      open eqrel-as-repi-mono-fact A public
      open rmfF% public
      open CF% public

    module CRF%-is-iso {A : Exℙ.Obj} (isfree : ℙ.peq.%0 A ℙ.~ ℙ.peq.%1 A) where
      private
        module A = ℙ.peq A
        module CRA = CRF% A

      r₁~r₂ : CRA.r₁ 𝔹.~ CRA.r₂
      r₁~r₂ = CRA.epi-pf (CRA.rmfF%tr₁ ⊙ F.ext isfree ⊙ CRA.rmfF%tr₂ ˢ)
            where open ecategory-aux-only 𝔹
{-
      inv : || 𝔹.Hom CRA.Ob (F.ₒ A.Hi) ||
      inv = F.ₐ A.ρ 𝔹.∘ CRA.r₁
      isop₁  : 𝔹.is-iso-pair CRA.ar inv
      isop₁ = record
        { iddom = {!!} --CRA.r₁tr ⊙ F.id
        ; idcod = {!!} --CRA.jm-pf (ass ⊙ ∘e r CRA.r₁tr ⊙ lidgg ridˢ F.id)
                      --      (ass ⊙ ∘e r₁~r₂ CRA.r₂tr ⊙ lidgg ridˢ F.id)
        }
        where open ecategory-aux-only 𝔹        
      isop₂  : 𝔹.is-iso-pair CRA.ar CRA.r₂
      isop₂ = record
        { iddom = CRA.r₂tr ⊙ F.id
        ; idcod = CRA.jm-pf (ass ⊙ ∘e (r₁~r₂ ˢ) CRA.r₁tr ⊙ lidgg ridˢ F.id)
                            (ass ⊙ ∘e r CRA.r₂tr ⊙ lidgg ridˢ F.id)
        }
        where open ecategory-aux-only 𝔹
      qF%iso₁ qF%iso₂ : 𝔹.is-iso CRA.ar
      qF%iso₁ = iso-defs.mkis-iso isop₁
      qF%iso₂ = iso-defs.mkis-iso isop₂
-}
    -- end CRF%-is-iso

    eqrelΔ2Δ : natural-transformation ((Rel reg𝔹 Flcov) ○ (CVex ℙ [ fwlℙ ])) (ΔER 𝔹 ○ F)
    eqrelΔ2Δ = record
        { fnc = λ {X} → record
              { base-ar = 𝔹.idar (F.ₒ X)
              ; isext = record
                      { rel-ar = CRF%.r₁ (ℙ.freepeq X)
                      ; cmptb₀ = r {f = 𝔹.idar (F.ₒ X) 𝔹.∘ CRF%.r₁ (ℙ.freepeq X)}
                      ; cmptb₁ = ∘e (CRF%-is-iso.r₁~r₂ {ℙ.freepeq X} rℙ) r
                      }
              }
        ; nat = λ {X} {Y} f → record
              { wit = F.ₐ f
              ; wit₀ = r
              ; wit₁ = lidgen (ridˢ {f = F.ₐ f})
              }
        }
        where open ecategory-aux-only 𝔹
              open ecategory-aux-only ℙ using () renaming (r to rℙ)

    Δ2eqrelΔ : natural-transformation (ΔER 𝔹 ○ F) (Rel reg𝔹 Flcov ○ CVex ℙ [ fwlℙ ])
    Δ2eqrelΔ = record
        { fnc = λ {X} → record
              { base-ar = 𝔹.idar (F.ₒ  X)
              ; isext = record
                      { rel-ar = CRF%.C (ℙ.freepeq X)
                      ; cmptb₀ = CRF%.rmfF%tr₁ (ℙ.freepeq X) ⊙ lidgenˢ F.id
                      ; cmptb₁ = CRF%.rmfF%tr₂ (ℙ.freepeq X) ⊙ lidgenˢ F.id
                      }
              }
        ; nat = λ {X} {Y} f → record
              { wit = CRF%.C (ℙ.freepeq Y) 𝔹.∘ F.ₐ f
              ; wit₀ = ass ⊙ ∘e r (CRF%.rmfF%tr₁ (ℙ.freepeq Y) ⊙ F.id)
              ; wit₁ = ass ⊙ lidgg (ridˢ {f = F.ₐ f}) (CRF%.rmfF%tr₂ (ℙ.freepeq Y) ⊙ F.id) 
              }
        }
        where open ecategory-aux-only 𝔹
  -- end Rel-on-free


  Rel-sq : {𝔹 : ecategory} (reg𝔹 : is-regular 𝔹) {F : efunctor ℙ 𝔹} (Flcov : is-left-covering F)
                 → natural-iso (Rel reg𝔹 Flcov ○ CVex ℙ [ fwlℙ ]) (ΔER 𝔹 ○ F)
  Rel-sq {𝔹} reg𝔹 {F} Flcov = record
    { natt = eqrelΔ2Δ
    ; natt⁻¹ = Δ2eqrelΔ
    ; isiso = λ {X} → record
            { iddom = record
                    { wit = CRF%.C (ℙ.freepeq X)
                    ; wit₀ = CRF%.rmfF%tr₁ (ℙ.freepeq X) ⊙ lidgenˢ F.id
                    ; wit₁ = CRF%.rmfF%tr₂ (ℙ.freepeq X) ⊙ F.id
                    }
            ; idcod = record
                    { wit = 𝔹.idar (F.ₒ X)
                    ; wit₀ = r
                    ; wit₁ = lid
                    }
            }
    }
    where open Rel-on-free reg𝔹 Flcov
          open ecategory-aux-only 𝔹
          module 𝔹 = ecategory 𝔹
          module F = efunctor-aux F

-- end eqrel-from-peq-funct



--   module imgpeq-def {𝔹 : ecategory} (𝔹isex : is-exact 𝔹) {F : efunctor ℙ 𝔹} (Flcov : is-left-covering F) where
--     private
--       module 𝔹 where
--         open ecategory 𝔹 public
--         --open comm-shapes 𝔹 public
--         --open iso-defs 𝔹 public
--         --open iso-transports 𝔹 public
--         open epis&monos-defs 𝔹 public
--         open epis&monos-props 𝔹 public
--         open kernel-pairs-defs 𝔹 public
--         open pseudo-eq-rel-defs 𝔹 public
--         open eq-rel-defs 𝔹 public
--         open image-fact-defs 𝔹 public
--         --open image-fact-props 𝔹 public
--         open binary-products 𝔹 public
--         --open pullback-squares 𝔹 public
--         --open pullback-props 𝔹 public
--         open projective-defs 𝔹 public
--         --open cat-of-equivalence-relations 𝔹 public
--         --open eqrel-mor-are-arrows public
--       module ex𝔹 where
--         open exact-cat-d&p 𝔹isex public
--         open has-bin-products hasprd using (prd-of) public
--       {-module ER𝔹 where
--         open ecategory (EqRel 𝔹) public-}
--       module F where
--         open efunctor-aux F public
--         open is-left-covering Flcov public
--         --open left-covering-into-exact-props hasfwl 𝔹isex Flcov public
--       open eqrel-from-peq-via-left-covering ex𝔹.exact-is-regular Flcov

--     --eqr/ : (A : Exℙ.Obj) → 𝔹.eqrel-over (F.ₒ (ℙ.peq.Lo A))
--     --eqr/ A = F.eqrel-from-peq-via-left-covering.eqrel/ A
--     module qrF% (A : Exℙ.Obj) where
--       --open F.eqrel-from-peq-via-left-covering.imgF% A public
--       open F.eqrel-as-repi-mono-fact A public -- hiding (eqrel/) 
--       open qF% public
--       open 𝔹.is-eq-rel iseqr using (jm-pf) renaming (isjm/ to risjm/) public
--     eqr : Exℙ.Obj → 𝔹.eqrel
--     eqr A = record { eqrelover = qrF%.eqrel/ A }
--     {-module eqr where
--       open 𝔹.eqrel-over public
--       open 𝔹.eqrel-mor public-}


--     eqr-ar : {A B : Exℙ.Obj} (f : || Exℙ.Hom A B ||) → 𝔹.eqrel-mor (eqr A) (eqr B)
--     eqr-ar {A} {B} f = record
--       { base-ar = F.ₐ f.lo
--       ; isext = record
--               { rel-ar = rel-ar
--               ; cmptb₀ = qrA.epi-pf (~proof
--                        (qrB.r₁ 𝔹.∘ rel-ar) 𝔹.∘ qrA.ar      ~[ assˢ ⊙ ∘e rel-ar-tr r ] /
--                        qrB.r₁ 𝔹.∘ qrB.ar 𝔹.∘ F.ₐ f.hi      ~[ ass ⊙ ∘e r qrB.r₁tr ⊙ F.∘∘ f.cmptb₀ ] /
--                        F.ₐ f.lo 𝔹.∘ F.ₐ A.%0                ~[ ∘e (qrA.r₁tr ˢ) r ⊙ ass ]∎
--                        (F.ₐ f.lo 𝔹.∘ qrA.r₁) 𝔹.∘ qrA.ar ∎)
--               ; cmptb₁ = qrA.epi-pf (~proof
--                        (qrB.r₂ 𝔹.∘ rel-ar) 𝔹.∘ qrA.ar      ~[ assˢ ⊙ ∘e rel-ar-tr r ] /
--                        qrB.r₂ 𝔹.∘ qrB.ar 𝔹.∘ F.ₐ f.hi      ~[ ass ⊙ ∘e r qrB.r₂tr ⊙ F.∘∘ f.cmptb₁ ] /
--                        F.ₐ f.lo 𝔹.∘ F.ₐ A.%1                ~[ ∘e (qrA.r₂tr ˢ) r ⊙ ass ]∎
--                        (F.ₐ f.lo 𝔹.∘ qrA.r₂) 𝔹.∘ qrA.ar ∎)
--               }
--       }
--       where open ecategory-aux-only 𝔹
--             module f = ℙ.peq-mor f
--             module A = ℙ.peq A
--             module B = ℙ.peq B
--             module qrA = qrF% A
--             module qrB = qrF% B
--             rel-ar-pf : (qrB.ar 𝔹.∘ F.ₐ f.hi) 𝔹.∘ qrA.kpF%.π//₁ 𝔹.~ (qrB.ar 𝔹.∘ F.ₐ f.hi) 𝔹.∘ qrA.kpF%.π//₂
--             rel-ar-pf = qrB.jm-pf (~proof
--               qrB.r₁ 𝔹.∘ (qrB.ar 𝔹.∘ F.ₐ f.hi) 𝔹.∘ qrA.kpF%.π//₁ ~[ ass ⊙ ∘e r (ass ⊙ ∘e r qrB.r₁tr ⊙ F.∘∘ f.cmptb₀) ] /
--               (F.ₐ f.lo 𝔹.∘ F.ₐ A.%0) 𝔹.∘ qrA.kpF%.π//₁               ~[ assˢ ⊙ ∘e qrA.kpF%.sqpf₁ r ⊙ ass ] /
--               (F.ₐ f.lo 𝔹.∘ F.ₐ A.%0) 𝔹.∘ qrA.kpF%.π//₂    ~[ ∘e r (F.∘∘ f.cmptb₀ ˢ ⊙ ∘e r (qrB.r₁tr ˢ) ⊙ assˢ) ⊙ assˢ ]∎
--               qrB.r₁ 𝔹.∘ (qrB.ar 𝔹.∘ F.ₐ f.hi) 𝔹.∘ qrA.kpF%.π//₂ ∎)
--                                  (~proof
--               qrB.r₂ 𝔹.∘ (qrB.ar 𝔹.∘ F.ₐ f.hi) 𝔹.∘ qrA.kpF%.π//₁ ~[ ass ⊙ ∘e r (ass ⊙ ∘e r qrB.r₂tr ⊙ F.∘∘ f.cmptb₁) ] /
--               (F.ₐ f.lo 𝔹.∘ F.ₐ A.%1) 𝔹.∘ qrA.kpF%.π//₁               ~[ assˢ ⊙ ∘e qrA.kpF%.sqpf₂ r ⊙ ass ] /
--               (F.ₐ f.lo 𝔹.∘ F.ₐ A.%1) 𝔹.∘ qrA.kpF%.π//₂    ~[ ∘e r (F.∘∘ f.cmptb₁ ˢ ⊙ ∘e r (qrB.r₂tr ˢ) ⊙ assˢ) ⊙ assˢ ]∎
--               qrB.r₂ 𝔹.∘ (qrB.ar 𝔹.∘ F.ₐ f.hi) 𝔹.∘ qrA.kpF%.π//₂ ∎)
--             rel-ar : || 𝔹.Hom qrA.Ob qrB.Ob ||
--             rel-ar = qrA.univ {qrB.Ob} (qrB.ar 𝔹.∘ F.ₐ f.hi) rel-ar-pf
--             rel-ar-tr : rel-ar 𝔹.∘ qrA.ar 𝔹.~ qrB.ar 𝔹.∘ F.ₐ f.hi
--             rel-ar-tr = qrA.univ-eq {qrB.Ob} {qrB.ar 𝔹.∘ F.ₐ f.hi} rel-ar-pf

--     eqr-ar-ext : {A B : Exℙ.Obj} (f f' : || Exℙ.Hom A B ||)
--                     → f Exℙ.~ f' → 𝔹.eqrel-mor-eq (eqr-ar {A} {B} f) (eqr-ar {A} {B} f')
--     eqr-ar-ext {A} {B} f f' hty = record
--       { wit = qrB.ar 𝔹.∘ F.ₐ f~f'.hty
--       ; wit₀ = ~proof qrB.r₁ 𝔹.∘ qrB.ar 𝔹.∘ F.ₐ f~f'.hty      ~[ ass ⊙ ∘e r qrB.r₁tr ] /
--                       F.ₐ B.%0 𝔹.∘ F.ₐ f~f'.hty               ~[ F.∘ax f~f'.hty₀ ]∎
--                       F.ₐ f.lo ∎
--       ; wit₁ = ~proof qrB.r₂ 𝔹.∘ qrB.ar 𝔹.∘ F.ₐ f~f'.hty      ~[ ass ⊙ ∘e r qrB.r₂tr ] /
--                       F.ₐ B.%1 𝔹.∘ F.ₐ f~f'.hty               ~[ F.∘ax f~f'.hty₁ ]∎
--                       F.ₐ f'.lo ∎
--       }
--       where module B = ℙ.peq B
--             module f = ℙ.peq-mor f
--             module f' = ℙ.peq-mor f'
--             module f~f' = ℙ.peq-mor-eq hty
--             module qrB = qrF% B
--             open ecategory-aux-only 𝔹
--   -- end imgpeq-def


--   imgpeq :  {𝔹 : ecategory} (𝔹isex : is-exact 𝔹) {F : efunctor ℙ 𝔹} (Flcov : is-left-covering F)
--                → efunctor Ex ℙ [ hasfwl ] (EqRel 𝔹)
--   imgpeq {𝔹} 𝔹isex {F} Flcov = record
--     { FObj = eqr
--     ; FHom = eqr-ar
--     ; isF = record
--           { ext = λ {A} {B} {f} {f'} pf → eqr-ar-ext f f' pf
--           ; id = λ {A} → 𝔹.eqrel-mor-eq-ext F.id
--           ; cmp = λ {A} {B} {C} f g → 𝔹.eqrel-mor-eq-ext F.∘ax-rf
--           }
--     }
--     where open imgpeq-def 𝔹isex Flcov
--           module 𝔹 = eq-rel-defs 𝔹
--           module F = efunctor-aux F

--   module imgpeq-on-free  {𝔹 : ecategory} (𝔹isex : is-exact 𝔹) {F : efunctor ℙ 𝔹} (Flcov : is-left-covering F) where
--     private
--       module 𝔹 where
--         open ecategory 𝔹 public
--         --open comm-shapes 𝔹 public
--         open iso-defs 𝔹 public
--         --open iso-transports 𝔹 public
--         open epis&monos-defs 𝔹 public
--         open epis&monos-props 𝔹 public
--         open kernel-pairs-defs 𝔹 public
--         open pseudo-eq-rel-defs 𝔹 public
--         open eq-rel-defs 𝔹 public
--         open image-fact-defs 𝔹 public
--         open image-fact-props 𝔹 public
--         open binary-products 𝔹 public
--         --open pullback-squares 𝔹 public
--         --open pullback-props 𝔹 public
--         open projective-defs 𝔹 public
--         --open cat-of-equivalence-relations 𝔹 public
--         --open eqrel-mor-are-arrows public
--       module ex𝔹 where
--         open exact-cat-d&p 𝔹isex public
--         open has-bin-products hasprd using (prd-of) public
--       {-module ER𝔹 where
--         open ecategory (EqRel 𝔹) public-}
--       module ER𝔹 where
--         open ecategory (EqRel 𝔹) public
--       module F where
--         open efunctor-aux F public
--         open is-left-covering Flcov public
--         open left-covering-into-exact-props hasfwl 𝔹isex Flcov public
--       module I = efunctor-aux (imgpeq 𝔹isex Flcov)
--       module ΔER = efunctor-aux (ΔER 𝔹)
      
--     module qrF% (A : Exℙ.Obj) where
--       open F.eqrel-from-peq-via-left-covering A public -- hiding (eqrel/) 
--       open qF% public
--       open 𝔹.is-eq-rel iseqr using (jm-pf) renaming (isjm/ to risjm/) public
--       eqr : 𝔹.eqrel
--       eqr = record { eqrelover = eqrel/ }
            
--     module qrF%-is-iso {A : Exℙ.Obj} (isfree : ℙ.peq.%0 A ℙ.~ ℙ.peq.%1 A) where
--       private
--         module A = ℙ.peq A
--         module qrA = qrF% A

--       r₁~r₂ : qrA.r₁ 𝔹.~ qrA.r₂
--       r₁~r₂ = qrA.epi-pf (qrA.r₁tr ⊙ F.ext isfree ⊙ qrA.r₂tr ˢ)
--             where open ecategory-aux-only 𝔹

-- {-
--       inv : || 𝔹.Hom qrA.Ob (F.ₒ A.Hi) ||
--       inv = F.ₐ A.ρ 𝔹.∘ qrA.r₁
--       isop₁  : 𝔹.is-iso-pair qrA.ar inv
--       isop₁ = record
--         { iddom = {!!} --qrA.r₁tr ⊙ F.id
--         ; idcod = {!!} --qrA.jm-pf (ass ⊙ ∘e r qrA.r₁tr ⊙ lidgg ridˢ F.id)
--                       --      (ass ⊙ ∘e r₁~r₂ qrA.r₂tr ⊙ lidgg ridˢ F.id)
--         }
--         where open ecategory-aux-only 𝔹        
--       isop₂  : 𝔹.is-iso-pair qrA.ar qrA.r₂
--       isop₂ = record
--         { iddom = qrA.r₂tr ⊙ F.id
--         ; idcod = qrA.jm-pf (ass ⊙ ∘e (r₁~r₂ ˢ) qrA.r₁tr ⊙ lidgg ridˢ F.id)
--                             (ass ⊙ ∘e r qrA.r₂tr ⊙ lidgg ridˢ F.id)
--         }
--         where open ecategory-aux-only 𝔹
--       qF%iso₁ qF%iso₂ : 𝔹.is-iso qrA.ar
--       qF%iso₁ = iso-defs.mkis-iso isop₁
--       qF%iso₂ = iso-defs.mkis-iso isop₂
-- -}
--     -- end qrF%-is-iso

--     eqrelΔ2Δ : natural-transformation (imgpeq 𝔹isex Flcov ○ Γex ℙ [ hasfwl ]) (ΔER 𝔹 ○ F)
--     eqrelΔ2Δ = record
--         { fnc = λ {X} → record
--               { base-ar = 𝔹.idar (F.ₒ X)
--               ; isext = record
--                       { rel-ar = qrF%.r₁ (ℙ.freepeq X) --qrF%.r₁ (ℙ.freepeq X)
--                       ; cmptb₀ = r --r --{qrF%.Ob X} {F.ₒ X} {f = 𝔹.idar (F.ₒ X) 𝔹.∘ qrF%.r₁ X}
--                       ; cmptb₁ = ∘e (qrF%-is-iso.r₁~r₂ {ℙ.freepeq X} rℙ) r
--                       --∘e (qrF%-is-iso.r₁~r₂ rℙ) r --∘e (qrF%-is-iso.r₁~r₂ X) (r {f = 𝔹.idar (F.ₒ X)})
--                       }
--               }
--         ; nat = λ {X} {Y} f → record
--               { wit = F.ₐ f
--               ; wit₀ = r
--               ; wit₁ = lidgen (ridˢ {f = F.ₐ f})
--               }
--         }
--         where open ecategory-aux-only 𝔹
--               open ecategory-aux-only ℙ using () renaming (r to rℙ)

--     Δ2eqrelΔ : natural-transformation (ΔER 𝔹 ○ F) (imgpeq 𝔹isex Flcov ○ Γex ℙ [ hasfwl ])
--     Δ2eqrelΔ = record
--         { fnc = λ {X} → record
--               { base-ar = 𝔹.idar (F.ₒ  X)
--               ; isext = record
--                       { rel-ar = qrF%.ar (ℙ.freepeq X)
--                       ; cmptb₀ = qrF%.r₁tr (ℙ.freepeq X) ⊙ lidgenˢ F.id
--                       ; cmptb₁ = qrF%.r₂tr (ℙ.freepeq X) ⊙ lidgenˢ F.id
--                       }
--               }
--         ; nat = λ {X} {Y} f → record
--               { wit = qrF%.ar (ℙ.freepeq Y) 𝔹.∘ F.ₐ f
--               ; wit₀ = ass ⊙ ∘e r (qrF%.r₁tr (ℙ.freepeq Y) ⊙ F.id)
--               ; wit₁ = ass ⊙ lidgg (ridˢ {f = F.ₐ f}) (qrF%.r₂tr (ℙ.freepeq Y) ⊙ F.id) 
--               }
--         }
--         where open ecategory-aux-only 𝔹
--   -- end imgpeq-on-free



--   imgpeq-sq : {𝔹 : ecategory} (𝔹isex : is-exact 𝔹) {F : efunctor ℙ 𝔹} (Flcov : is-left-covering F)
--                  → natural-iso (imgpeq 𝔹isex Flcov ○ Γex ℙ [ hasfwl ]) (ΔER 𝔹 ○ F)
--   imgpeq-sq {𝔹} 𝔹isex {F} Flcov = record
--     { natt = eqrelΔ2Δ
--     ; natt⁻¹ = Δ2eqrelΔ
--     ; isiso = λ {X} → record
--             { iddom = record
--                     { wit = qrF%.ar (ℙ.freepeq X)
--                     ; wit₀ = qrF%.r₁tr (ℙ.freepeq X) ⊙ lidgenˢ F.id
--                     ; wit₁ = qrF%.r₂tr (ℙ.freepeq X) ⊙ F.id
--                     }
--             ; idcod = record
--                     { wit = 𝔹.idar (F.ₒ X)
--                     ; wit₀ = r
--                     ; wit₁ = lid
--                     }
--             }
--     }
--     where open imgpeq-on-free 𝔹isex Flcov
--           open ecategory-aux-only 𝔹
--           module 𝔹 = ecategory 𝔹
--           module F = efunctor-aux F

-- -- end eqrel-from-peq-funct

    
-- -- {-
-- --   module imgpeq-on-free  {𝔹 : ecategory} (𝔹isex : is-exact 𝔹) {F : efunctor ℙ 𝔹} (Flcov : is-left-covering F) where
-- --     private
-- --       module 𝔹 where
-- --         open ecategory 𝔹 public
-- --         --open comm-shapes 𝔹 public
-- --         open iso-defs 𝔹 public
-- --         --open iso-transports 𝔹 public
-- --         open epis&monos-defs 𝔹 public
-- --         open epis&monos-props 𝔹 public
-- --         open kernel-pairs-defs 𝔹 public
-- --         open pseudo-eq-rel-defs 𝔹 public
-- --         open eq-rel-defs 𝔹 public
-- --         open image-fact-defs 𝔹 public
-- --         open image-fact-props 𝔹 public
-- --         open binary-products 𝔹 public
-- --         --open pullback-squares 𝔹 public
-- --         --open pullback-props 𝔹 public
-- --         open projective-defs 𝔹 public
-- --         --open cat-of-equivalence-relations 𝔹 public
-- --         --open eqrel-mor-are-arrows public
-- --       module ex𝔹 where
-- --         open exact-cat-d&p 𝔹isex public
-- --         open has-bin-products hasprd using (prd-of) public
-- --       {-module ER𝔹 where
-- --         open ecategory (EqRel 𝔹) public-}
-- --       module ER𝔹 where
-- --         open ecategory (EqRel 𝔹) public
-- --       module F where
-- --         open efunctor-aux F public
-- --         open is-left-covering Flcov public
-- --         open left-covering-into-exact-props hasfwl 𝔹isex Flcov public
-- --       module I = efunctor-aux (imgpeq 𝔹isex Flcov)
-- --       module ΔER = efunctor-aux (ΔER 𝔹)
      
-- --     module qrF% (X : ℙ.Obj) where
-- --       open F.eqrel-from-peq-via-left-covering (ℙ.freepeq X) public -- hiding (eqrel/) 
-- --       open qF% public
-- --       open 𝔹.is-eq-rel iseqr using (jm-pf) renaming (isjm/ to risjm/) public
-- --       eqr : 𝔹.eqrel
-- --       eqr = record { eqrelover = eqrel/ }

-- --     {-F%check : (X : ℙ.Obj) → || 𝔹.Hom (F.ₒ X) (img.FX².O12 X) ||
-- --     F%check X = img.F% X
-- --     F%free-isΔ : (X : ℙ.Obj) → img.F% X 𝔹.~ img.FX².<_,_> X (𝔹.idar (F.ₒ X)) (𝔹.idar (F.ₒ X))
-- --     --(F.ₐ (ℙ.idar X)) (F.ₐ (ℙ.idar X))
-- --     F%free-isΔ X = img.FX².<>~<> X F.id F.id
-- --                  where open ecategory-aux-only 𝔹-}
-- --     {-F%free-monic : (X : ℙ.Obj) → 𝔹.is-monic (img.F% X)
-- --     F%free-monic X = record
-- --       { mono-pf = λ {_} {g} {g'} pf → ~proof
-- --                 g                                 ~[ lidggˢ r (imgX.FX².×tr₁ ⊙ F.id) ⊙ assˢ ] /
-- --                 imgX.FX².π₁ 𝔹.∘ imgX.F% 𝔹.∘ g    ~[ ∘e pf r ] /
-- --                 imgX.FX².π₁ 𝔹.∘ imgX.F% 𝔹.∘ g'   ~[ ass ⊙ lidgg r (imgX.FX².×tr₁ ⊙ F.id) ]∎
-- --                 g' ∎
-- --       }
-- --       where open ecategory-aux-only 𝔹
-- --             module imgX = img X-}
            
-- --     module qrF%-is-iso (X : ℙ.Obj) where
-- --       module qrX = qrF% X

-- --       r₁~r₂ : qrX.r₁ 𝔹.~ qrX.r₂
-- --       r₁~r₂ = qrX.epi-pf (qrX.r₁tr ⊙ qrX.r₂tr ˢ)
-- --             where open ecategory-aux-only 𝔹
-- --       isop₁  : 𝔹.is-iso-pair qrX.ar qrX.r₁
-- --       isop₁ = record
-- --         { iddom = qrX.r₁tr ⊙ F.id
-- --         ; idcod = qrX.jm-pf (ass ⊙ ∘e r qrX.r₁tr ⊙ lidgg ridˢ F.id)
-- --                             (ass ⊙ ∘e r₁~r₂ qrX.r₂tr ⊙ lidgg ridˢ F.id)
-- --         }
-- --         where open ecategory-aux-only 𝔹
-- --       isop₂  : 𝔹.is-iso-pair qrX.ar qrX.r₂
-- --       isop₂ = record
-- --         { iddom = qrX.r₂tr ⊙ F.id
-- --         ; idcod = qrX.jm-pf (ass ⊙ ∘e (r₁~r₂ ˢ) qrX.r₁tr ⊙ lidgg ridˢ F.id)
-- --                             (ass ⊙ ∘e r qrX.r₂tr ⊙ lidgg ridˢ F.id)
-- --         }
-- --         where open ecategory-aux-only 𝔹
-- --       qF%iso₁ qF%iso₂ : 𝔹.is-iso qrX.ar
-- --       qF%iso₁ = iso-defs.mkis-iso isop₁
-- --       qF%iso₂ = iso-defs.mkis-iso isop₂
-- --     -- end qrF%-is-iso
-- -- -}

-- -- {-
-- --     module eqrelΔ2Δ-ar (X : ℙ.Obj) where
-- --       private
-- --         module X = ℙ.peq
-- --         module qrX = qrF% X
-- --         module qrXiso = qrF%-is-iso X

-- --       ar : || ER𝔹.Hom qrX.eqr (𝔹.free-eqrel (F.ₒ X)) ||
-- --       ar = record
-- --          { base-ar = 𝔹.idar (F.ₒ X)
-- --          ; isext = record
-- --                  { rel-ar = qrX.r₁
-- --                  ; cmptb₀ = r
-- --                  ; cmptb₁ = ∘e qrXiso.r₁~r₂ r
-- --                  }
-- --          }
-- --          where open ecategory-aux-only 𝔹
-- --     -- end eqrelΔ2Δ-ar
-- -- -}


-- --     eqrelΔ2Δ : natural-transformation (imgpeq 𝔹isex Flcov ○ Γex ℙ [ hasfwl ]) (ΔER 𝔹 ○ F)
-- --     eqrelΔ2Δ = record
-- --         { fnc = λ {X} → record
-- --               { base-ar = 𝔹.idar (F.ₒ X)
-- --               ; isext = record
-- --                       { rel-ar = qrF%.r₁ X
-- --                       ; cmptb₀ = r --{qrF%.Ob X} {F.ₒ X} {f = 𝔹.idar (F.ₒ X) 𝔹.∘ qrF%.r₁ X}
-- --                       ; cmptb₁ = ∘e (qrF%-is-iso.r₁~r₂ X) r --∘e (qrF%-is-iso.r₁~r₂ X) (r {f = 𝔹.idar (F.ₒ X)})
-- --                       }
-- --               }
-- --         ; nat = λ {X} {Y} f → record
-- --               { wit = F.ₐ f
-- --               ; wit₀ = r
-- --               ; wit₁ = lidgen (ridˢ {f = F.ₐ f})
-- --               }
-- --         }
-- --         where open ecategory-aux-only 𝔹

-- --     Δ2eqrelΔ : natural-transformation (ΔER 𝔹 ○ F) (imgpeq 𝔹isex Flcov ○ Γex ℙ [ hasfwl ])
-- --     Δ2eqrelΔ = record
-- --         { fnc = λ {X} → record
-- --               { base-ar = 𝔹.idar (F.ₒ X)
-- --               ; isext = record
-- --                       { rel-ar = qrF%.ar X
-- --                       ; cmptb₀ = qrF%.r₁tr X ⊙ lidgenˢ F.id
-- --                       ; cmptb₁ = qrF%.r₂tr X ⊙ lidgenˢ F.id
-- --                       }
-- --               }
-- --         ; nat = λ {X} {Y} f → record
-- --               { wit = qrF%.ar Y 𝔹.∘ F.ₐ f
-- --               ; wit₀ = ass ⊙ ∘e r (qrF%.r₁tr Y ⊙ F.id)
-- --               ; wit₁ = ass ⊙ lidgg (ridˢ {f = F.ₐ f}) (qrF%.r₂tr Y ⊙ F.id) 
-- --               }
-- --         }
-- --         where open ecategory-aux-only 𝔹


-- --   -- end imgpeq-on-free


-- --   imgpeq-sq : {𝔹 : ecategory} (𝔹isex : is-exact 𝔹) {F : efunctor ℙ 𝔹} (Flcov : is-left-covering F)
-- --                  → natural-iso (imgpeq 𝔹isex Flcov ○ Γex ℙ [ hasfwl ]) (ΔER 𝔹 ○ F)
-- --   imgpeq-sq {𝔹} 𝔹isex {F} Flcov = record
-- --     { natt = eqrelΔ2Δ
-- --     ; natt⁻¹ = Δ2eqrelΔ
-- --     ; isiso = λ {X} → record
-- --             { iddom = record
-- --                     { wit = qrF%.ar X
-- --                     ; wit₀ = qrF%.r₁tr X ⊙ lidgenˢ F.id
-- --                     ; wit₁ = qrF%.r₂tr X ⊙ F.id
-- --                     }
-- --             ; idcod = record
-- --                     { wit = 𝔹.idar (F.ₒ X)
-- --                     ; wit₀ = r
-- --                     ; wit₁ = lid
-- --                     }
-- --             }
-- --     }
-- --     where open imgpeq-on-free 𝔹isex Flcov
-- --           open ecategory-aux-only 𝔹
-- --           module 𝔹 = ecategory 𝔹
-- --           module F = efunctor-aux F

-- -- -- end eqrel-from-peq-funct



-- -- -- -- OLD
  
-- -- --   module imgpeq-def {𝔹 : ecategory} (𝔹isex : is-exact 𝔹) {F : efunctor ℙ 𝔹} (Flcov : is-left-covering F) where
-- -- --     private
-- -- --       module 𝔹 where
-- -- --         open ecategory 𝔹 public
-- -- --         --open comm-shapes 𝔹 public
-- -- --         --open iso-defs 𝔹 public
-- -- --         --open iso-transports 𝔹 public
-- -- --         open epis&monos-defs 𝔹 public
-- -- --         open epis&monos-props 𝔹 public
-- -- --         open kernel-pairs-defs 𝔹 public
-- -- --         open pseudo-eq-rel-defs 𝔹 public
-- -- --         open eq-rel-defs 𝔹 public
-- -- --         open image-fact-defs 𝔹 public
-- -- --         --open image-fact-props 𝔹 public
-- -- --         open binary-products 𝔹 public
-- -- --         --open pullback-squares 𝔹 public
-- -- --         --open pullback-props 𝔹 public
-- -- --         open projective-defs 𝔹 public
-- -- --         --open cat-of-equivalence-relations 𝔹 public
-- -- --         --open eqrel-mor-are-arrows public
-- -- --       module ex𝔹 where
-- -- --         open exact-cat-d&p 𝔹isex public
-- -- --         open has-bin-products hasprd using (prd-of) public
-- -- --       {-module ER𝔹 where
-- -- --         open ecategory (EqRel 𝔹) public-}
-- -- --       module F where
-- -- --         open efunctor-aux F public
-- -- --         open is-left-covering Flcov public
-- -- --         open left-covering-into-exact-props hasfwl 𝔹isex Flcov public

-- -- --     eqr/ : (A : Exℙ.Obj) → 𝔹.eqrel-over (F.ₒ (ℙ.peq.Lo A))
-- -- --     eqr/ A = F.eqrel-from-peq-via-left-covering.eqrel/ A
-- -- --     module img (A : Exℙ.Obj) where
-- -- --       open F.eqrel-from-peq-via-left-covering.imgF% A public
-- -- --       open F.eqrel-from-peq-via-left-covering A hiding (eqrel/) public
-- -- --     eqr : Exℙ.Obj → 𝔹.eqrel
-- -- --     eqr A = record { eqrelover = eqr/ A }
-- -- --     module eqr where
-- -- --       open 𝔹.eqrel-over public
-- -- --       open 𝔹.eqrel-mor public


-- -- --     eqr-ar : {A B : Exℙ.Obj} (f : || Exℙ.Hom A B ||) → 𝔹.eqrel-mor (eqr A) (eqr B)
-- -- --     eqr-ar {A} {B} f = record
-- -- --       { base-ar = F.ₐ f.lo
-- -- --       ; isext = record
-- -- --               { rel-ar = rel-ar
-- -- --               ; cmptb₀ = CA.epi-pf (~proof
-- -- --                        (imgB.r₁ 𝔹.∘ rel-ar) 𝔹.∘ imgA.C    ~[ assˢ ⊙ ∘e (CA.univ-eq rel-ar-pf) r ] /
-- -- --                        imgB.r₁ 𝔹.∘ imgB.C 𝔹.∘ F.ₐ f.hi    ~[ ass ⊙ ∘e r imgB.imgF%tr₁ ⊙ F.∘∘ f.cmptb₀ ] /
-- -- --                        F.ₐ f.lo 𝔹.∘ F.ₐ (ℙ.peq.%0 A)       ~[ ∘e (imgA.imgF%tr₁ ˢ) r ⊙ ass ]∎
-- -- --                        (F.ₐ f.lo 𝔹.∘ imgA.r₁) 𝔹.∘ imgA.C ∎)
-- -- --               ; cmptb₁ = CA.epi-pf (~proof
-- -- --                        (imgB.r₂ 𝔹.∘ rel-ar) 𝔹.∘ imgA.C    ~[ assˢ ⊙ ∘e (CA.univ-eq rel-ar-pf) r ] /
-- -- --                        imgB.r₂ 𝔹.∘ imgB.C 𝔹.∘ F.ₐ f.hi    ~[ ass ⊙ ∘e r imgB.imgF%tr₂ ⊙ F.∘∘ f.cmptb₁ ] /
-- -- --                        F.ₐ f.lo 𝔹.∘ F.ₐ (ℙ.peq.%1 A)       ~[ ∘e (imgA.imgF%tr₂ ˢ) r ⊙ ass ]∎
-- -- --                        (F.ₐ f.lo 𝔹.∘ imgA.r₂) 𝔹.∘ imgA.C ∎)
-- -- --               }
-- -- --       }
-- -- --       where module f = ℙ.peq-mor f
-- -- --             module imgA = img A
-- -- --             module imgB = img B
-- -- --             module CA = 𝔹.is-regular-epi imgA.C-is-repi
-- -- --             module MB = 𝔹.is-monic imgB.M-is-monic
-- -- --             module FAL² = 𝔹.product-of-not (ex𝔹.prd-of (F.ₒ (ℙ.peq.Lo A)) (F.ₒ (ℙ.peq.Lo A)))
-- -- --             module FBL² = 𝔹.product-of-not (ex𝔹.prd-of (F.ₒ (ℙ.peq.Lo B)) (F.ₒ (ℙ.peq.Lo B)))
-- -- --             open ecategory-aux-only 𝔹
-- -- --             rel-ar-pf : (imgB.C 𝔹.∘ F.ₐ f.hi) 𝔹.∘ CA.rel₁ 𝔹.~ (imgB.C 𝔹.∘ F.ₐ f.hi) 𝔹.∘ CA.rel₂
-- -- --             rel-ar-pf = MB.mono-pf (~proof
-- -- --               imgB.M 𝔹.∘ (imgB.C 𝔹.∘ F.ₐ f.hi) 𝔹.∘ CA.rel₁      ~[ ∘e assˢ r ⊙ ass ⊙ ∘e r imgB.tr ] /
-- -- --               imgB.F% 𝔹.∘ F.ₐ f.hi 𝔹.∘ CA.rel₁
-- -- --                       ~[ ass ⊙ ∘e r (FBL².<>ar~<>ar (F.∘ax f.cmptb₀ ⊙ F.∘ax-rfˢ ⊙ ∘e (FAL².×tr₁ ˢ) r ⊙ ass)
-- -- --                                                      (F.∘ax f.cmptb₁ ⊙ F.∘ax-rfˢ ⊙ ∘e (FAL².×tr₂ ˢ) r ⊙ ass)) ⊙ assˢ ] /
-- -- --               FBL².< F.ₐ f.lo 𝔹.∘ FAL².π₁ , F.ₐ f.lo 𝔹.∘ FAL².π₂ > 𝔹.∘ imgA.F% 𝔹.∘ CA.rel₁
-- -- --                                                 ~[ ∘e (∘e r (imgA.tr ˢ) ⊙ assˢ ⊙ ∘e CA.eq r ⊙ ass ⊙ ∘e r imgA.tr ) r ] /
-- -- --               FBL².< F.ₐ f.lo 𝔹.∘ FAL².π₁ , F.ₐ f.lo 𝔹.∘ FAL².π₂ > 𝔹.∘ imgA.F% 𝔹.∘ CA.rel₂
-- -- --                      ~[ ass ⊙ ∘e r (FBL².<>ar~<>ar (assˢ ⊙ ∘e FAL².×tr₁ r ⊙ F.∘ax-rf ⊙ F.∘axˢ f.cmptb₀)
-- -- --                                                     (assˢ ⊙ ∘e FAL².×tr₂ r ⊙ F.∘ax-rf ⊙ F.∘axˢ f.cmptb₁)) ⊙ assˢ ] /
-- -- --               imgB.F% 𝔹.∘ F.ₐ f.hi 𝔹.∘ CA.rel₂                  ~[ ∘e r (imgB.tr ˢ) ⊙ assˢ ⊙ ∘e ass r ]∎
-- -- --               imgB.M 𝔹.∘ (imgB.C 𝔹.∘ F.ₐ f.hi) 𝔹.∘ CA.rel₂ ∎)
-- -- --             rel-ar : || 𝔹.Hom imgA.Ob imgB.Ob ||
-- -- --             rel-ar = CA.univ (imgB.C 𝔹.∘ F.ₐ f.hi) rel-ar-pf

-- -- --     eqr-ar-ext : {A B : Exℙ.Obj} (f f' : || Exℙ.Hom A B ||)
-- -- --                     → f Exℙ.~ f' → 𝔹.eqrel-mor-eq (eqr-ar {A} {B} f) (eqr-ar {A} {B} f')
-- -- --     eqr-ar-ext {A} {B} f f' hty = record
-- -- --       { wit = imgB.C 𝔹.∘ F.ₐ f~f'.hty
-- -- --       ; wit₀ = ~proof imgB.r₁ 𝔹.∘ imgB.C 𝔹.∘ F.ₐ f~f'.hty    ~[ ass ⊙ ∘e r imgB.imgF%tr₁ ] /
-- -- --                       F.ₐ B.%0 𝔹.∘ F.ₐ f~f'.hty               ~[ F.∘ax f~f'.hty₀ ]∎
-- -- --                       F.ₐ f.lo ∎
-- -- --       ; wit₁ = ~proof imgB.r₂ 𝔹.∘ imgB.C 𝔹.∘ F.ₐ f~f'.hty    ~[ ass ⊙ ∘e r imgB.imgF%tr₂ ] /
-- -- --                       F.ₐ B.%1 𝔹.∘ F.ₐ f~f'.hty               ~[ F.∘ax f~f'.hty₁ ]∎
-- -- --                       F.ₐ f'.lo ∎
-- -- --       }
-- -- --       where module B = ℙ.peq B
-- -- --             module f = ℙ.peq-mor f
-- -- --             module f' = ℙ.peq-mor f'
-- -- --             module f~f' = ℙ.peq-mor-eq hty
-- -- --             module imgB = img B
-- -- --             open ecategory-aux-only 𝔹

-- -- -- {- problems with amount of time for typechecking in imgpeq 
-- -- --     eqr-ar-id : (A : Exℙ.Obj) → 𝔹.eqrel-mor-eq (eqr-ar {A} {A} (Exℙ.idar A)) (𝔹.eqrel-idar (eqr A))
-- -- --     --(eqr-ar {A} {A} (Exℙ.idar A)) ER𝔹.~ (ER𝔹.idar (eqr A))
-- -- --     eqr-ar-id A = record
-- -- --       { wit = erA.ρ
-- -- --       ; wit₀ = erA.ρ-ax₀ ⊙ F.idˢ
-- -- --       ; wit₁ = erA.ρ-ax₁
-- -- --       } --𝔹.eqrel-mor-eq-ext F.id
-- -- --       where --module A = ℙ.peq A
-- -- --             module erA = 𝔹.eqrel (eqr A)
-- -- --             open ecategory-aux-only 𝔹
    
-- -- --     eqr-ar-cmp : {A B C : Exℙ.Obj} (f : || Exℙ.Hom A B ||) (g : || Exℙ.Hom B C ||)
-- -- --                     → (eqr-ar {B} {C} g ER𝔹.∘ eqr-ar {A} {B} f) ER𝔹.~ (eqr-ar {A} {C} (g Exℙ.∘ f))
-- -- --     eqr-ar-cmp f g = 𝔹.eqrel-mor-eq-ext F.∘ax-rf --𝔹.eqrel-mor-eq-ext F.∘ax-rf
-- -- -- -}

-- -- --   -- end imgpeq-def
