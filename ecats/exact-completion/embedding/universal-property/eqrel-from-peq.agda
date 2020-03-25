
-- disable the K axiom:

{-# OPTIONS --without-K #-}

-- Agda version 2.5.4.1

module ecats.exact-completion.embedding.universal-property.eqrel-from-peq where

open import ecats.basic-defs.ecat-def&not
open import ecats.basic-defs.all-arrows
open import ecats.basic-props.epi&mono
open import ecats.basic-defs.regular-ecat
open import ecats.basic-props.regular-ecat
open import ecats.finite-limits.all
open import ecats.constructions.ecat-eqrel
open import ecats.functors.defs.efunctor-d&n
open import ecats.functors.defs.natural-transformation
open import ecats.functors.defs.left-covering
open import ecats.exact-completion.construction



-- Definition of the functor Ex ℂ [ hasfwl ] → 𝔼 induced by a left covering ℂ → 𝔼 into 𝔼 exact.

module eqrel-from-peq-funct {ℂ : ecategory} (hasfwl : has-fin-weak-limits ℂ) where
  private
    module ℂ where
      open ecategory ℂ public
      open pseudo-eq-rel-defs ℂ public
      open finite-weak-limits ℂ public
    module Exℂ = ecategory Ex ℂ [ hasfwl ]
    module Γex = efunctor-aux Γex ℂ [ hasfwl ]



  -- left covering functor from cat with weak fin limits into regular cat

  module eqrel-from-peq-via-left-covering {𝔼 : ecategory} (reg𝔼 : is-regular 𝔼)
                                          {F : efunctor ℂ 𝔼} (lcovF : is-left-covering F)
                                          where
    private
      module 𝔼 where
        open ecategory 𝔼 public
        open comm-shapes 𝔼 public
        open epis&monos-defs 𝔼 public
        open epis&monos-props 𝔼 public
        open eq-rel-defs 𝔼 public
        open finite-limits-d&p 𝔼 public
      module r𝔼 where
        open is-regular reg𝔼 public
        open has-bin-products hasprd using (prd-of) public
        open has-pullbacks haspb using (pb-of) public
        open regular-cat-props reg𝔼 public
      module F = efunctor-aux F
      module lcF = is-left-covering lcovF

    module eqrel-as-repi-mono-fact (A : ℂ.Peq) where
      private
        module A = ℂ.Peq A
        module FAL² = 𝔼.product-of-not (r𝔼.prd-of (F.ₒ A.Lo) (F.ₒ A.Lo))
      -- main definitions, to be used elsewhere
      F% : || 𝔼.Hom (F.ₒ A.Hi) FAL².O12 ||
      F% = FAL².< F.ₐ A.%0 , F.ₐ A.%1 >
      module rmfF% = r𝔼.rmf-of F% --𝔼.repi-mono-fact-of rmfF%
      module CF% = 𝔼.is-regular-epi rmfF%.C-is-repi
      CF%cov : 𝔼.reg-cover-of rmfF%.Ob
      CF%cov = record { Ob = F.ₒ A.Hi ; cov = record { ar = rmfF%.C ; is-repi = rmfF%.C-is-repi } }
      r₁ r₂ : || 𝔼.Hom rmfF%.Ob (F.ₒ A.Lo) ||    
      r₁ = FAL².π₁ 𝔼.∘ rmfF%.M
      r₂ = FAL².π₂ 𝔼.∘ rmfF%.M
      rmfF%tr₁ = ~proof r₁ 𝔼.∘ rmfF%.C            ~[ assˢ ⊙ ∘e rmfF%.tr r  ] /
                        FAL².π₁ 𝔼.∘ F%            ~[ FAL².×tr₁ ]∎
                        F.ₐ A.%0 ∎
               where open ecategory-aux-only 𝔼                     
      rmfF%tr₂ = ~proof r₂ 𝔼.∘ rmfF%.C           ~[ assˢ ⊙ ∘e rmfF%.tr r  ] /
                        FAL².π₂ 𝔼.∘ F%           ~[ FAL².×tr₂ ]∎
                        F.ₐ A.%1 ∎
               where open ecategory-aux-only 𝔼
      F%rel : F% 𝔼.∘ CF%.rel₁ 𝔼.~ F% 𝔼.∘ CF%.rel₂
      F%rel = ∘e r (rmfF%.tr ˢ) ⊙ assˢ ⊙ ∘e CF%.eq r ⊙ ass ⊙ ∘e r rmfF%.tr
            where open ecategory-aux-only 𝔼

      -- auxiliary definitions
      private
      -- jointly monic
        rjm : 𝔼.is-jointly-monic/ (𝔼.mkspan/ r₁ r₂)
        rjm = 𝔼.<>monic→isjm/-ar FAL².×of rmfF%.M-is-monic
      -- reflexive
        rρ : || 𝔼.Hom (F.ₒ A.Lo) rmfF%.Ob ||
        rρ  = rmfF%.C 𝔼.∘ F.ₐ A.ρ    
      -- symmetric
        module σrmfF% = r𝔼.rmf-of FAL².< F.ₐ A.%1 , F.ₐ A.%0 >
        rσ-monic : 𝔼.is-monic FAL².< r₂ , r₁ >
        rσ-monic = 𝔼.isjm/→<>monic (𝔼.jointly-monic-sym rjm) FAL².×of
        rσ-comm : FAL².< r₂ , r₁ > 𝔼.∘ rmfF%.C 𝔼.∘ F.ₐ A.σ 𝔼.~ F%
        rσ-comm = ~proof
          FAL².< r₂ , r₁ > 𝔼.∘ rmfF%.C 𝔼.∘ F.ₐ A.σ   ~[ ass ⊙ ∘e r (FAL².<>ar~<> rmfF%tr₂ rmfF%tr₁) ] /
          FAL².< F.ₐ A.%1 , F.ₐ A.%0 > 𝔼.∘ F.ₐ A.σ    ~[ FAL².<>ar~<> (F.∘ax A.σ-ax₁) (F.∘ax A.σ-ax₀) ]∎
          F% ∎
                    where open ecategory-aux-only 𝔼
        rσ-eq : (rmfF%.C 𝔼.∘ F.ₐ A.σ) 𝔼.∘ CF%.rel₁ 𝔼.~ (rmfF%.C 𝔼.∘ F.ₐ A.σ) 𝔼.∘ CF%.rel₂
        rσ-eq = mono-pf (~proof
          FAL².< r₂ , r₁ > 𝔼.∘ (rmfF%.C 𝔼.∘ F.ₐ A.σ) 𝔼.∘ CF%.rel₁   ~[ ass ⊙ ∘e r rσ-comm  ] /
          F% 𝔼.∘ CF%.rel₁                                            ~[ ∘e r (rmfF%.tr ˢ) ⊙ assˢ ] /
          rmfF%.M 𝔼.∘ rmfF%.C 𝔼.∘ CF%.rel₁                          ~[ ∘e CF%.eq r ] /
          rmfF%.M 𝔼.∘ rmfF%.C 𝔼.∘ CF%.rel₂                          ~[ ass ⊙ ∘e r rmfF%.tr ] /
          F% 𝔼.∘ CF%.rel₂                                            ~[ ∘e r (rσ-comm ˢ) ⊙ assˢ ]∎
          FAL².< r₂ , r₁ > 𝔼.∘ (rmfF%.C 𝔼.∘ F.ₐ A.σ) 𝔼.∘ CF%.rel₂ ∎)
                  where open ecategory-aux-only 𝔼
                        open 𝔼.is-monic rσ-monic
        rσ : || 𝔼.Hom rmfF%.Ob rmfF%.Ob ||
        rσ = CF%.univ (rmfF%.C 𝔼.∘ F.ₐ A.σ) rσ-eq
        rσ-ax₀ : r₁ 𝔼.∘ rσ 𝔼.~ r₂
        rσ-ax₀ = CF%.epi-pf (~proof
          (r₁ 𝔼.∘ rσ) 𝔼.∘ rmfF%.C        ~[ assˢ ⊙ ∘e (CF%.univ-eq rσ-eq) r ] /
          r₁ 𝔼.∘ rmfF%.C 𝔼.∘ F.ₐ A.σ     ~[ ass ⊙ ∘e r rmfF%tr₁ ⊙ F.∘ax A.σ-ax₀ ⊙ rmfF%tr₂ ˢ ]∎
          r₂ 𝔼.∘ rmfF%.C ∎)
               where open ecategory-aux-only 𝔼
        rσ-ax₁ : r₂ 𝔼.∘ rσ 𝔼.~ r₁
        rσ-ax₁ = CF%.epi-pf (~proof
          (r₂ 𝔼.∘ rσ) 𝔼.∘ rmfF%.C        ~[ assˢ ⊙ ∘e (CF%.univ-eq rσ-eq) r ] /
          r₂ 𝔼.∘ rmfF%.C 𝔼.∘ F.ₐ A.σ     ~[ ass ⊙ ∘e r rmfF%tr₂ ⊙ F.∘ax A.σ-ax₁ ⊙ rmfF%tr₁ ˢ ]∎
          r₁ 𝔼.∘ rmfF%.C ∎)
               where open ecategory-aux-only 𝔼
      -- transitive
        τrpb : 𝔼.pullback-of r₂ r₁
        τrpb = r𝔼.pb-of r₂ r₁
        module τrpb = 𝔼.pullback-of-not τrpb
        module τAwpb = ℂ.wpullback-of-not A.τwpb
        module C×C where
          open r𝔼.reg-covers-of-pb→reg-cover-of-pb τrpb CF%cov CF%cov public
          open 𝔼.is-regular-epi diagl-repi public
        τF%pb : 𝔼.pullback-of (F.ₐ A.%1) (F.ₐ A.%0)
        τF%pb = 𝔼.mkpb-of (𝔼.×/ext-dr C×C.outsq-pb rmfF%tr₂ rmfF%tr₁)
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
        τcov : || 𝔼.Hom (F.ₒ τAwpb.ul) τrpb.ul ||
        τcov = C×C.diagl 𝔼.∘ outcov 
        τcov-repi : 𝔼.is-regular-epi τcov
        τcov-repi = ∘c C×C.diagl-repi outcov-repi
                  where open is-ecat-congr r𝔼.regular-epi-is-congr
        private
          module τc = 𝔼.is-regular-epi τcov-repi
        rmfF%τ-pf-aux1 = ~proof
          r₁ 𝔼.∘ τrpb.π/₁ 𝔼.∘ τcov                     ~[ ∘e (ass ⊙ ∘e r C×C.trl₁) r ] /
          r₁ 𝔼.∘ (rmfF%.C 𝔼.∘ τF%pb.π/₁) 𝔼.∘ outcov   ~[ ass ⊙ ∘e r (ass ⊙ ∘e r rmfF%tr₁) ⊙ assˢ ] /
          F.ₐ A.%0 𝔼.∘ τF%pb.π/₁ 𝔼.∘ outcov            ~[  ∘e (τF%pb.×/tr₁ outcov-pf) r ⊙ F.∘ax-rf ]∎
          F.ₐ (A.%0 ℂ.∘ τAwpb.wπ/₁) ∎
                     where open ecategory-aux-only 𝔼
        rmfF%τ-pf-aux2 = ~proof
          r₂ 𝔼.∘ τrpb.π/₂ 𝔼.∘ τcov                     ~[ ∘e (ass ⊙ ∘e r C×C.trl₂) r ] /
          r₂ 𝔼.∘ (rmfF%.C 𝔼.∘ τF%pb.π/₂) 𝔼.∘ outcov   ~[ ass ⊙ ∘e r (ass ⊙ ∘e r rmfF%tr₂) ⊙ assˢ ] /
          F.ₐ A.%1 𝔼.∘ τF%pb.π/₂ 𝔼.∘ outcov            ~[  ∘e (τF%pb.×/tr₂ outcov-pf) r ⊙ F.∘ax-rf ]∎
          F.ₐ (A.%1 ℂ.∘ τAwpb.wπ/₂) ∎
                     where open ecategory-aux-only 𝔼
        rmfF%τ-pf-aux : FAL².< F.ₐ (A.%0 ℂ.∘ τAwpb.wπ/₁) , F.ₐ (A.%1 ℂ.∘ τAwpb.wπ/₂) >
                               𝔼.~ FAL².< r₁ 𝔼.∘ τrpb.π/₁ , r₂ 𝔼.∘ τrpb.π/₂ > 𝔼.∘ τcov
        rmfF%τ-pf-aux = FAL².<>ar~<>ˢ (assˢ ⊙ rmfF%τ-pf-aux1) (assˢ ⊙ rmfF%τ-pf-aux2)
                      where open ecategory-aux-only 𝔼
        rmfF%τ-pf : (rmfF%.C 𝔼.∘ F.ₐ A.τ) 𝔼.∘ τc.rel₁ 𝔼.~ (rmfF%.C 𝔼.∘ F.ₐ A.τ) 𝔼.∘ τc.rel₂
        rmfF%τ-pf = mono-pf (~proof
          rmfF%.M 𝔼.∘ (rmfF%.C 𝔼.∘ F.ₐ A.τ) 𝔼.∘ τc.rel₁                        ~[ ass ⊙ ∘e r (ass ⊙ ∘e r rmfF%.tr) ] /
          (F% 𝔼.∘ F.ₐ A.τ) 𝔼.∘ τc.rel₁                                                ~[ ∘e r F%τeq ] /
          FAL².< F.ₐ (A.%0 ℂ.∘ τAwpb.wπ/₁) , F.ₐ (A.%1 ℂ.∘ τAwpb.wπ/₂) > 𝔼.∘ τc.rel₁   ~[ ∘e r rmfF%τ-pf-aux ⊙ assˢ  ] /
          FAL².< r₁ 𝔼.∘ τrpb.π/₁ , r₂ 𝔼.∘ τrpb.π/₂ > 𝔼.∘ τcov 𝔼.∘ τc.rel₁            ~[ ∘e τc.eq r  ] /
          FAL².< r₁ 𝔼.∘ τrpb.π/₁ , r₂ 𝔼.∘ τrpb.π/₂ > 𝔼.∘ τcov 𝔼.∘ τc.rel₂         ~[  ass ⊙ ∘e r (rmfF%τ-pf-aux ˢ) ] /
          FAL².< F.ₐ (A.%0 ℂ.∘ τAwpb.wπ/₁) , F.ₐ (A.%1 ℂ.∘ τAwpb.wπ/₂) > 𝔼.∘ τc.rel₂   ~[ ∘e r (F%τeq ˢ) ] /
          (F% 𝔼.∘ F.ₐ A.τ) 𝔼.∘ τc.rel₂                                      ~[ ∘e r (∘e r (rmfF%.tr ˢ) ⊙ assˢ) ⊙ assˢ ]∎
          rmfF%.M 𝔼.∘ (rmfF%.C 𝔼.∘ F.ₐ A.τ) 𝔼.∘ τc.rel₂ ∎)
                where open ecategory-aux-only 𝔼
                      open 𝔼.is-monic rmfF%.M-is-monic
        rmfF%τ : || 𝔼.Hom τrpb.ul rmfF%.Ob ||
        rmfF%τ = τc.univ {rmfF%.Ob} (rmfF%.C 𝔼.∘ F.ₐ A.τ) rmfF%τ-pf
        rmfF%τ-tr : rmfF%τ 𝔼.∘ τcov 𝔼.~ rmfF%.C 𝔼.∘ F.ₐ A.τ
        rmfF%τ-tr = τc.univ-eq {rmfF%.Ob} {rmfF%.C 𝔼.∘ F.ₐ A.τ} rmfF%τ-pf
        rmfF%τ-ax₀ : r₁ 𝔼.∘ rmfF%τ 𝔼.~ r₁ 𝔼.∘ τrpb.π/₁
        rmfF%τ-ax₀ = τc.epi-pf (~proof
          (r₁ 𝔼.∘ rmfF%τ) 𝔼.∘ τcov            ~[ assˢ ⊙ ∘e rmfF%τ-tr r ⊙ ass ⊙ ∘e r rmfF%tr₁ ] /
          F.ₐ A.%0 𝔼.∘ F.ₐ A.τ                 ~[ F.∘ax A.τ-ax₀ ⊙ rmfF%τ-pf-aux1 ˢ ⊙ ass ]∎
          (r₁ 𝔼.∘ τrpb.π/₁) 𝔼.∘ τcov ∎)
                   where open ecategory-aux-only 𝔼
        rmfF%τ-ax₁ = τc.epi-pf (~proof
          (r₂ 𝔼.∘ rmfF%τ) 𝔼.∘ τcov            ~[ assˢ ⊙ ∘e rmfF%τ-tr r ⊙ ass ⊙ ∘e r rmfF%tr₂ ] / 
          F.ₐ A.%1 𝔼.∘ F.ₐ A.τ                 ~[ F.∘ax A.τ-ax₁ ⊙ (rmfF%τ-pf-aux2 ˢ) ⊙ ass ]∎
          (r₂ 𝔼.∘ τrpb.π/₂) 𝔼.∘ τcov ∎)
                   where open ecategory-aux-only 𝔼

      -- equivalece relation
        iseqr : 𝔼.is-eq-rel {rmfF%.Ob} {F.ₒ A.Lo} r₁ r₂
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
          where open ecategory-aux-only 𝔼
      -- end private

      eqrel/ : 𝔼.eqrel-over (F.ₒ A.Lo)
      eqrel/ = record
        { relOb = rmfF%.Ob
        ; r₁ = r₁
        ; r₂ = r₂
        ; iseqrel = iseqr
        }
    -- end eqrel-as-repi-mono-fact

    --eqr/ : (A : Exℂ.Obj) → 𝔼.eqrel-over (F.ₒ (ℂ.Peq.Lo A))
    --eqr/ A = F.eqrel-from-peq-via-left-covering.eqrel/ A

    private
      module CRF% (A : Exℂ.Obj) where
        open eqrel-as-repi-mono-fact A public -- hiding (eqrel/)
        open rmfF% public
        open CF% public

    eqr : Exℂ.Obj → 𝔼.eqrel
    eqr A = record { eqrelover = CRF%.eqrel/ A }
    {-module eqr where
      open 𝔼.eqrel-over public
      open 𝔼.eqrel-mor public-}

    eqr-ar : {A B : Exℂ.Obj} (f : || Exℂ.Hom A B ||) → 𝔼.eqrel-mor (eqr A) (eqr B)
    eqr-ar {A} {B} f = record
      { base-ar = F.ₐ f.lo
      ; isext = record
              { rel-ar = rel-ar
              ; cmptb₀ = CRA.epi-pf (~proof
                       (CRB.r₁ 𝔼.∘ rel-ar) 𝔼.∘ CRA.C      ~[ assˢ ⊙ ∘e rel-ar-tr r ] /
                       CRB.r₁ 𝔼.∘ CRB.C 𝔼.∘ F.ₐ f.hi      ~[ ass ⊙ ∘e r CRB.rmfF%tr₁ ⊙ F.∘∘ f.cmptb₀ ] /
                       F.ₐ f.lo 𝔼.∘ F.ₐ A.%0                ~[ ∘e (CRA.rmfF%tr₁ ˢ) r ⊙ ass ]∎
                       (F.ₐ f.lo 𝔼.∘ CRA.r₁) 𝔼.∘ CRA.C ∎)
              ; cmptb₁ = CRA.epi-pf (~proof
                       (CRB.r₂ 𝔼.∘ rel-ar) 𝔼.∘ CRA.C      ~[ assˢ ⊙ ∘e rel-ar-tr r ] /
                       CRB.r₂ 𝔼.∘ CRB.C 𝔼.∘ F.ₐ f.hi      ~[ ass ⊙ ∘e r CRB.rmfF%tr₂ ⊙ F.∘∘ f.cmptb₁ ] /
                       F.ₐ f.lo 𝔼.∘ F.ₐ A.%1                ~[ ∘e (CRA.rmfF%tr₂ ˢ) r ⊙ ass ]∎
                       (F.ₐ f.lo 𝔼.∘ CRA.r₂) 𝔼.∘ CRA.C ∎)
              }
      }
      where open ecategory-aux-only 𝔼
            module f = ℂ.Peq-mor f
            module A = ℂ.Peq A
            module FAL² = 𝔼.product-of-not (r𝔼.prd-of (F.ₒ A.Lo) (F.ₒ A.Lo))
            module B = ℂ.Peq B
            module FBL² = 𝔼.product-of-not (r𝔼.prd-of (F.ₒ B.Lo) (F.ₒ B.Lo))
            open 𝔼.×ₐdef FBL².prdsp FAL².prdsp
            Ffl×Ffl : || 𝔼.Hom FAL².O12 FBL².O12 ||
            Ffl×Ffl = F.ₐ f.lo ×ₐ F.ₐ f.lo
            module CRA = CRF% A
            module CRB = CRF% B
            cmptbF% : CRB.F% 𝔼.∘ F.ₐ f.hi 𝔼.~ Ffl×Ffl 𝔼.∘ CRA.F%
            cmptbF% = FBL².<>ar~<>ar (F.∘∘ f.cmptb₀ ⊙ ∘e (FAL².×tr₁ {g = F.ₐ A.%1} ˢ) r ⊙ ass)
                                     (F.∘∘ f.cmptb₁ ⊙ ∘e (FAL².×tr₂ {f = F.ₐ A.%0} ˢ) r ⊙ ass)
            rel-ar-pf : (CRB.C 𝔼.∘ F.ₐ f.hi) 𝔼.∘ CRA.rel₁ 𝔼.~ (CRB.C 𝔼.∘ F.ₐ f.hi) 𝔼.∘ CRA.rel₂
            rel-ar-pf = CRB.mono-pf (~proof
              CRB.M 𝔼.∘ (CRB.C 𝔼.∘ F.ₐ f.hi) 𝔼.∘ CRA.rel₁    ~[ ass ⊙ ∘e r (ass ⊙ ∘e r CRB.tr ⊙ cmptbF%) ⊙ assˢ ] /
              Ffl×Ffl 𝔼.∘ CRA.F% 𝔼.∘ CRA.rel₁                ~[ ∘e CRA.F%rel r ] /
              Ffl×Ffl 𝔼.∘ CRA.F% 𝔼.∘ CRA.rel₂            ~[ ass ⊙ ∘e r (cmptbF% ˢ ⊙ ∘e r (CRB.tr ˢ) ⊙ assˢ) ⊙ assˢ ]∎
              CRB.M 𝔼.∘ (CRB.C 𝔼.∘ F.ₐ f.hi) 𝔼.∘ CRA.rel₂ ∎)
            rel-ar : || 𝔼.Hom CRA.Ob CRB.Ob ||
            rel-ar = CRA.univ {CRB.Ob} (CRB.C 𝔼.∘ F.ₐ f.hi) rel-ar-pf
            rel-ar-tr : rel-ar 𝔼.∘ CRA.C 𝔼.~ CRB.C 𝔼.∘ F.ₐ f.hi
            rel-ar-tr = CRA.univ-eq {CRB.Ob} {CRB.C 𝔼.∘ F.ₐ f.hi} rel-ar-pf

    eqr-ar-ext : {A B : Exℂ.Obj} (f f' : || Exℂ.Hom A B ||)
                    → f Exℂ.~ f' → 𝔼.eqrel-mor-eq (eqr-ar {A} {B} f) (eqr-ar {A} {B} f')
    eqr-ar-ext {A} {B} f f' hty = record
      { wit = CRB.C 𝔼.∘ F.ₐ f~f'.hty
      ; wit₀ = ~proof CRB.r₁ 𝔼.∘ CRB.C 𝔼.∘ F.ₐ f~f'.hty      ~[ ass ⊙ ∘e r CRB.rmfF%tr₁ ] /
                      F.ₐ B.%0 𝔼.∘ F.ₐ f~f'.hty               ~[ F.∘ax f~f'.hty₀ ]∎
                      F.ₐ f.lo ∎
      ; wit₁ = ~proof CRB.r₂ 𝔼.∘ CRB.C 𝔼.∘ F.ₐ f~f'.hty      ~[ ass ⊙ ∘e r CRB.rmfF%tr₂ ] /
                      F.ₐ B.%1 𝔼.∘ F.ₐ f~f'.hty               ~[ F.∘ax f~f'.hty₁ ]∎
                      F.ₐ f'.lo ∎
      }
      where module B = ℂ.Peq B
            module f = ℂ.Peq-mor f
            module f' = ℂ.Peq-mor f'
            module f~f' = ℂ.Peq-mor-eq hty
            module CRB = CRF% B
            open ecategory-aux-only 𝔼
  -- end eqrel-from-peq-via-left-covering


  imgPeq :  {𝔼 : ecategory} (reg𝔼 : is-regular 𝔼) {F : efunctor ℂ 𝔼} (Flcov : is-left-covering F)
               → efunctor Ex ℂ [ hasfwl ] (EqRel 𝔼)
  imgPeq {𝔼} reg𝔼 {F} Flcov = record
    { FObj = eqr
    ; FHom = eqr-ar
    ; isF = record
          { ext = λ {A} {B} {f} {f'} pf → eqr-ar-ext f f' pf
          ; id = λ {A} → 𝔼.eqrel-mor-eq-ext F.id
          ; cmp = λ {A} {B} {C} f g → 𝔼.eqrel-mor-eq-ext F.∘ax-rf
          }
    }
    where open eqrel-from-peq-via-left-covering reg𝔼 Flcov
          module 𝔼 = eq-rel-defs 𝔼
          module F = efunctor-aux F


  module imgPeq-on-free  {𝔼 : ecategory} (reg𝔼 : is-regular 𝔼) {F : efunctor ℂ 𝔼} (Flcov : is-left-covering F) where
    private
      module 𝔼 = ecategory 𝔼
      module F = efunctor-aux F
      module I = efunctor-aux (imgPeq reg𝔼 Flcov)
      module ΔER = efunctor-aux (ΔER 𝔼)
    
    module CRF% (A : Exℂ.Obj) where
      open eqrel-from-peq-via-left-covering reg𝔼 Flcov
      open eqrel-as-repi-mono-fact A public
      open rmfF% public
      open CF% public

    module CRF%-is-iso {A : Exℂ.Obj} (isfree : ℂ.Peq.%0 A ℂ.~ ℂ.Peq.%1 A) where
      private
        module A = ℂ.Peq A
        module CRA = CRF% A

      r₁~r₂ : CRA.r₁ 𝔼.~ CRA.r₂
      r₁~r₂ = CRA.epi-pf (CRA.rmfF%tr₁ ⊙ F.ext isfree ⊙ CRA.rmfF%tr₂ ˢ)
            where open ecategory-aux-only 𝔼
{-
      inv : || 𝔼.Hom CRA.Ob (F.ₒ A.Hi) ||
      inv = F.ₐ A.ρ 𝔼.∘ CRA.r₁
      isop₁  : 𝔼.is-iso-pair CRA.ar inv
      isop₁ = record
        { iddom = {!!} --CRA.r₁tr ⊙ F.id
        ; idcod = {!!} --CRA.jm-pf (ass ⊙ ∘e r CRA.r₁tr ⊙ lidgg ridˢ F.id)
                      --      (ass ⊙ ∘e r₁~r₂ CRA.r₂tr ⊙ lidgg ridˢ F.id)
        }
        where open ecategory-aux-only 𝔼        
      isop₂  : 𝔼.is-iso-pair CRA.ar CRA.r₂
      isop₂ = record
        { iddom = CRA.r₂tr ⊙ F.id
        ; idcod = CRA.jm-pf (ass ⊙ ∘e (r₁~r₂ ˢ) CRA.r₁tr ⊙ lidgg ridˢ F.id)
                            (ass ⊙ ∘e r CRA.r₂tr ⊙ lidgg ridˢ F.id)
        }
        where open ecategory-aux-only 𝔼
      qF%iso₁ qF%iso₂ : 𝔼.is-iso CRA.ar
      qF%iso₁ = iso-defs.mkis-iso isop₁
      qF%iso₂ = iso-defs.mkis-iso isop₂
-}
    -- end CRF%-is-iso

    eqrelΔ2Δ : natural-transformation (imgPeq reg𝔼 Flcov ○ Γex ℂ [ hasfwl ]) (ΔER 𝔼 ○ F)
    eqrelΔ2Δ = record
        { fnc = λ {X} → record
              { base-ar = 𝔼.idar (F.ₒ X)
              ; isext = record
                      { rel-ar = CRF%.r₁ (ℂ.freePeq X)
                      ; cmptb₀ = r {f = 𝔼.idar (F.ₒ X) 𝔼.∘ CRF%.r₁ (ℂ.freePeq X)}
                      ; cmptb₁ = ∘e (CRF%-is-iso.r₁~r₂ {ℂ.freePeq X} rℂ) r
                      }
              }
        ; nat = λ {X} {Y} f → record
              { wit = F.ₐ f
              ; wit₀ = r
              ; wit₁ = lidgen (ridˢ {f = F.ₐ f})
              }
        }
        where open ecategory-aux-only 𝔼
              open ecategory-aux-only ℂ using () renaming (r to rℂ)

    Δ2eqrelΔ : natural-transformation (ΔER 𝔼 ○ F) (imgPeq reg𝔼 Flcov ○ Γex ℂ [ hasfwl ])
    Δ2eqrelΔ = record
        { fnc = λ {X} → record
              { base-ar = 𝔼.idar (F.ₒ  X)
              ; isext = record
                      { rel-ar = CRF%.C (ℂ.freePeq X)
                      ; cmptb₀ = CRF%.rmfF%tr₁ (ℂ.freePeq X) ⊙ lidgenˢ F.id
                      ; cmptb₁ = CRF%.rmfF%tr₂ (ℂ.freePeq X) ⊙ lidgenˢ F.id
                      }
              }
        ; nat = λ {X} {Y} f → record
              { wit = CRF%.C (ℂ.freePeq Y) 𝔼.∘ F.ₐ f
              ; wit₀ = ass ⊙ ∘e r (CRF%.rmfF%tr₁ (ℂ.freePeq Y) ⊙ F.id)
              ; wit₁ = ass ⊙ lidgg (ridˢ {f = F.ₐ f}) (CRF%.rmfF%tr₂ (ℂ.freePeq Y) ⊙ F.id) 
              }
        }
        where open ecategory-aux-only 𝔼
  -- end imgPeq-on-free


  imgPeq-sq : {𝔼 : ecategory} (reg𝔼 : is-regular 𝔼) {F : efunctor ℂ 𝔼} (Flcov : is-left-covering F)
                 → natural-iso (imgPeq reg𝔼 Flcov ○ Γex ℂ [ hasfwl ]) (ΔER 𝔼 ○ F)
  imgPeq-sq {𝔼} reg𝔼 {F} Flcov = record
    { natt = eqrelΔ2Δ
    ; natt⁻¹ = Δ2eqrelΔ
    ; isiso = λ {X} → record
            { iddom = record
                    { wit = CRF%.C (ℂ.freePeq X)
                    ; wit₀ = CRF%.rmfF%tr₁ (ℂ.freePeq X) ⊙ lidgenˢ F.id
                    ; wit₁ = CRF%.rmfF%tr₂ (ℂ.freePeq X) ⊙ F.id
                    }
            ; idcod = record
                    { wit = 𝔼.idar (F.ₒ X)
                    ; wit₀ = r
                    ; wit₁ = lid
                    }
            }
    }
    where open imgPeq-on-free reg𝔼 Flcov
          open ecategory-aux-only 𝔼
          module 𝔼 = ecategory 𝔼
          module F = efunctor-aux F

-- end eqrel-from-peq-funct



--   module imgPeq-def {𝔼 : ecategory} (𝔼isex : is-exact 𝔼) {F : efunctor ℂ 𝔼} (Flcov : is-left-covering F) where
--     private
--       module 𝔼 where
--         open ecategory 𝔼 public
--         --open comm-shapes 𝔼 public
--         --open iso-defs 𝔼 public
--         --open iso-transports 𝔼 public
--         open epis&monos-defs 𝔼 public
--         open epis&monos-props 𝔼 public
--         open kernel-pairs-defs 𝔼 public
--         open pseudo-eq-rel-defs 𝔼 public
--         open eq-rel-defs 𝔼 public
--         open image-fact-defs 𝔼 public
--         --open image-fact-props 𝔼 public
--         open binary-products 𝔼 public
--         --open pullback-squares 𝔼 public
--         --open pullback-props 𝔼 public
--         open projective-defs 𝔼 public
--         --open cat-of-equivalence-relations 𝔼 public
--         --open eqrel-mor-are-arrows public
--       module ex𝔼 where
--         open exact-cat-d&p 𝔼isex public
--         open has-bin-products hasprd using (prd-of) public
--       {-module ER𝔼 where
--         open ecategory (EqRel 𝔼) public-}
--       module F where
--         open efunctor-aux F public
--         open is-left-covering Flcov public
--         --open left-covering-into-exact-props hasfwl 𝔼isex Flcov public
--       open eqrel-from-peq-via-left-covering ex𝔼.exact-is-regular Flcov

--     --eqr/ : (A : Exℂ.Obj) → 𝔼.eqrel-over (F.ₒ (ℂ.Peq.Lo A))
--     --eqr/ A = F.eqrel-from-peq-via-left-covering.eqrel/ A
--     module qrF% (A : Exℂ.Obj) where
--       --open F.eqrel-from-peq-via-left-covering.imgF% A public
--       open F.eqrel-as-repi-mono-fact A public -- hiding (eqrel/) 
--       open qF% public
--       open 𝔼.is-eq-rel iseqr using (jm-pf) renaming (isjm/ to risjm/) public
--     eqr : Exℂ.Obj → 𝔼.eqrel
--     eqr A = record { eqrelover = qrF%.eqrel/ A }
--     {-module eqr where
--       open 𝔼.eqrel-over public
--       open 𝔼.eqrel-mor public-}


--     eqr-ar : {A B : Exℂ.Obj} (f : || Exℂ.Hom A B ||) → 𝔼.eqrel-mor (eqr A) (eqr B)
--     eqr-ar {A} {B} f = record
--       { base-ar = F.ₐ f.lo
--       ; isext = record
--               { rel-ar = rel-ar
--               ; cmptb₀ = qrA.epi-pf (~proof
--                        (qrB.r₁ 𝔼.∘ rel-ar) 𝔼.∘ qrA.ar      ~[ assˢ ⊙ ∘e rel-ar-tr r ] /
--                        qrB.r₁ 𝔼.∘ qrB.ar 𝔼.∘ F.ₐ f.hi      ~[ ass ⊙ ∘e r qrB.r₁tr ⊙ F.∘∘ f.cmptb₀ ] /
--                        F.ₐ f.lo 𝔼.∘ F.ₐ A.%0                ~[ ∘e (qrA.r₁tr ˢ) r ⊙ ass ]∎
--                        (F.ₐ f.lo 𝔼.∘ qrA.r₁) 𝔼.∘ qrA.ar ∎)
--               ; cmptb₁ = qrA.epi-pf (~proof
--                        (qrB.r₂ 𝔼.∘ rel-ar) 𝔼.∘ qrA.ar      ~[ assˢ ⊙ ∘e rel-ar-tr r ] /
--                        qrB.r₂ 𝔼.∘ qrB.ar 𝔼.∘ F.ₐ f.hi      ~[ ass ⊙ ∘e r qrB.r₂tr ⊙ F.∘∘ f.cmptb₁ ] /
--                        F.ₐ f.lo 𝔼.∘ F.ₐ A.%1                ~[ ∘e (qrA.r₂tr ˢ) r ⊙ ass ]∎
--                        (F.ₐ f.lo 𝔼.∘ qrA.r₂) 𝔼.∘ qrA.ar ∎)
--               }
--       }
--       where open ecategory-aux-only 𝔼
--             module f = ℂ.Peq-mor f
--             module A = ℂ.Peq A
--             module B = ℂ.Peq B
--             module qrA = qrF% A
--             module qrB = qrF% B
--             rel-ar-pf : (qrB.ar 𝔼.∘ F.ₐ f.hi) 𝔼.∘ qrA.kpF%.π//₁ 𝔼.~ (qrB.ar 𝔼.∘ F.ₐ f.hi) 𝔼.∘ qrA.kpF%.π//₂
--             rel-ar-pf = qrB.jm-pf (~proof
--               qrB.r₁ 𝔼.∘ (qrB.ar 𝔼.∘ F.ₐ f.hi) 𝔼.∘ qrA.kpF%.π//₁ ~[ ass ⊙ ∘e r (ass ⊙ ∘e r qrB.r₁tr ⊙ F.∘∘ f.cmptb₀) ] /
--               (F.ₐ f.lo 𝔼.∘ F.ₐ A.%0) 𝔼.∘ qrA.kpF%.π//₁               ~[ assˢ ⊙ ∘e qrA.kpF%.sqpf₁ r ⊙ ass ] /
--               (F.ₐ f.lo 𝔼.∘ F.ₐ A.%0) 𝔼.∘ qrA.kpF%.π//₂    ~[ ∘e r (F.∘∘ f.cmptb₀ ˢ ⊙ ∘e r (qrB.r₁tr ˢ) ⊙ assˢ) ⊙ assˢ ]∎
--               qrB.r₁ 𝔼.∘ (qrB.ar 𝔼.∘ F.ₐ f.hi) 𝔼.∘ qrA.kpF%.π//₂ ∎)
--                                  (~proof
--               qrB.r₂ 𝔼.∘ (qrB.ar 𝔼.∘ F.ₐ f.hi) 𝔼.∘ qrA.kpF%.π//₁ ~[ ass ⊙ ∘e r (ass ⊙ ∘e r qrB.r₂tr ⊙ F.∘∘ f.cmptb₁) ] /
--               (F.ₐ f.lo 𝔼.∘ F.ₐ A.%1) 𝔼.∘ qrA.kpF%.π//₁               ~[ assˢ ⊙ ∘e qrA.kpF%.sqpf₂ r ⊙ ass ] /
--               (F.ₐ f.lo 𝔼.∘ F.ₐ A.%1) 𝔼.∘ qrA.kpF%.π//₂    ~[ ∘e r (F.∘∘ f.cmptb₁ ˢ ⊙ ∘e r (qrB.r₂tr ˢ) ⊙ assˢ) ⊙ assˢ ]∎
--               qrB.r₂ 𝔼.∘ (qrB.ar 𝔼.∘ F.ₐ f.hi) 𝔼.∘ qrA.kpF%.π//₂ ∎)
--             rel-ar : || 𝔼.Hom qrA.Ob qrB.Ob ||
--             rel-ar = qrA.univ {qrB.Ob} (qrB.ar 𝔼.∘ F.ₐ f.hi) rel-ar-pf
--             rel-ar-tr : rel-ar 𝔼.∘ qrA.ar 𝔼.~ qrB.ar 𝔼.∘ F.ₐ f.hi
--             rel-ar-tr = qrA.univ-eq {qrB.Ob} {qrB.ar 𝔼.∘ F.ₐ f.hi} rel-ar-pf

--     eqr-ar-ext : {A B : Exℂ.Obj} (f f' : || Exℂ.Hom A B ||)
--                     → f Exℂ.~ f' → 𝔼.eqrel-mor-eq (eqr-ar {A} {B} f) (eqr-ar {A} {B} f')
--     eqr-ar-ext {A} {B} f f' hty = record
--       { wit = qrB.ar 𝔼.∘ F.ₐ f~f'.hty
--       ; wit₀ = ~proof qrB.r₁ 𝔼.∘ qrB.ar 𝔼.∘ F.ₐ f~f'.hty      ~[ ass ⊙ ∘e r qrB.r₁tr ] /
--                       F.ₐ B.%0 𝔼.∘ F.ₐ f~f'.hty               ~[ F.∘ax f~f'.hty₀ ]∎
--                       F.ₐ f.lo ∎
--       ; wit₁ = ~proof qrB.r₂ 𝔼.∘ qrB.ar 𝔼.∘ F.ₐ f~f'.hty      ~[ ass ⊙ ∘e r qrB.r₂tr ] /
--                       F.ₐ B.%1 𝔼.∘ F.ₐ f~f'.hty               ~[ F.∘ax f~f'.hty₁ ]∎
--                       F.ₐ f'.lo ∎
--       }
--       where module B = ℂ.Peq B
--             module f = ℂ.Peq-mor f
--             module f' = ℂ.Peq-mor f'
--             module f~f' = ℂ.Peq-mor-eq hty
--             module qrB = qrF% B
--             open ecategory-aux-only 𝔼
--   -- end imgPeq-def


--   imgPeq :  {𝔼 : ecategory} (𝔼isex : is-exact 𝔼) {F : efunctor ℂ 𝔼} (Flcov : is-left-covering F)
--                → efunctor Ex ℂ [ hasfwl ] (EqRel 𝔼)
--   imgPeq {𝔼} 𝔼isex {F} Flcov = record
--     { FObj = eqr
--     ; FHom = eqr-ar
--     ; isF = record
--           { ext = λ {A} {B} {f} {f'} pf → eqr-ar-ext f f' pf
--           ; id = λ {A} → 𝔼.eqrel-mor-eq-ext F.id
--           ; cmp = λ {A} {B} {C} f g → 𝔼.eqrel-mor-eq-ext F.∘ax-rf
--           }
--     }
--     where open imgPeq-def 𝔼isex Flcov
--           module 𝔼 = eq-rel-defs 𝔼
--           module F = efunctor-aux F

--   module imgPeq-on-free  {𝔼 : ecategory} (𝔼isex : is-exact 𝔼) {F : efunctor ℂ 𝔼} (Flcov : is-left-covering F) where
--     private
--       module 𝔼 where
--         open ecategory 𝔼 public
--         --open comm-shapes 𝔼 public
--         open iso-defs 𝔼 public
--         --open iso-transports 𝔼 public
--         open epis&monos-defs 𝔼 public
--         open epis&monos-props 𝔼 public
--         open kernel-pairs-defs 𝔼 public
--         open pseudo-eq-rel-defs 𝔼 public
--         open eq-rel-defs 𝔼 public
--         open image-fact-defs 𝔼 public
--         open image-fact-props 𝔼 public
--         open binary-products 𝔼 public
--         --open pullback-squares 𝔼 public
--         --open pullback-props 𝔼 public
--         open projective-defs 𝔼 public
--         --open cat-of-equivalence-relations 𝔼 public
--         --open eqrel-mor-are-arrows public
--       module ex𝔼 where
--         open exact-cat-d&p 𝔼isex public
--         open has-bin-products hasprd using (prd-of) public
--       {-module ER𝔼 where
--         open ecategory (EqRel 𝔼) public-}
--       module ER𝔼 where
--         open ecategory (EqRel 𝔼) public
--       module F where
--         open efunctor-aux F public
--         open is-left-covering Flcov public
--         open left-covering-into-exact-props hasfwl 𝔼isex Flcov public
--       module I = efunctor-aux (imgPeq 𝔼isex Flcov)
--       module ΔER = efunctor-aux (ΔER 𝔼)
      
--     module qrF% (A : Exℂ.Obj) where
--       open F.eqrel-from-peq-via-left-covering A public -- hiding (eqrel/) 
--       open qF% public
--       open 𝔼.is-eq-rel iseqr using (jm-pf) renaming (isjm/ to risjm/) public
--       eqr : 𝔼.eqrel
--       eqr = record { eqrelover = eqrel/ }
            
--     module qrF%-is-iso {A : Exℂ.Obj} (isfree : ℂ.Peq.%0 A ℂ.~ ℂ.Peq.%1 A) where
--       private
--         module A = ℂ.Peq A
--         module qrA = qrF% A

--       r₁~r₂ : qrA.r₁ 𝔼.~ qrA.r₂
--       r₁~r₂ = qrA.epi-pf (qrA.r₁tr ⊙ F.ext isfree ⊙ qrA.r₂tr ˢ)
--             where open ecategory-aux-only 𝔼

-- {-
--       inv : || 𝔼.Hom qrA.Ob (F.ₒ A.Hi) ||
--       inv = F.ₐ A.ρ 𝔼.∘ qrA.r₁
--       isop₁  : 𝔼.is-iso-pair qrA.ar inv
--       isop₁ = record
--         { iddom = {!!} --qrA.r₁tr ⊙ F.id
--         ; idcod = {!!} --qrA.jm-pf (ass ⊙ ∘e r qrA.r₁tr ⊙ lidgg ridˢ F.id)
--                       --      (ass ⊙ ∘e r₁~r₂ qrA.r₂tr ⊙ lidgg ridˢ F.id)
--         }
--         where open ecategory-aux-only 𝔼        
--       isop₂  : 𝔼.is-iso-pair qrA.ar qrA.r₂
--       isop₂ = record
--         { iddom = qrA.r₂tr ⊙ F.id
--         ; idcod = qrA.jm-pf (ass ⊙ ∘e (r₁~r₂ ˢ) qrA.r₁tr ⊙ lidgg ridˢ F.id)
--                             (ass ⊙ ∘e r qrA.r₂tr ⊙ lidgg ridˢ F.id)
--         }
--         where open ecategory-aux-only 𝔼
--       qF%iso₁ qF%iso₂ : 𝔼.is-iso qrA.ar
--       qF%iso₁ = iso-defs.mkis-iso isop₁
--       qF%iso₂ = iso-defs.mkis-iso isop₂
-- -}
--     -- end qrF%-is-iso

--     eqrelΔ2Δ : natural-transformation (imgPeq 𝔼isex Flcov ○ Γex ℂ [ hasfwl ]) (ΔER 𝔼 ○ F)
--     eqrelΔ2Δ = record
--         { fnc = λ {X} → record
--               { base-ar = 𝔼.idar (F.ₒ X)
--               ; isext = record
--                       { rel-ar = qrF%.r₁ (ℂ.freePeq X) --qrF%.r₁ (ℂ.freePeq X)
--                       ; cmptb₀ = r --r --{qrF%.Ob X} {F.ₒ X} {f = 𝔼.idar (F.ₒ X) 𝔼.∘ qrF%.r₁ X}
--                       ; cmptb₁ = ∘e (qrF%-is-iso.r₁~r₂ {ℂ.freePeq X} rℂ) r
--                       --∘e (qrF%-is-iso.r₁~r₂ rℂ) r --∘e (qrF%-is-iso.r₁~r₂ X) (r {f = 𝔼.idar (F.ₒ X)})
--                       }
--               }
--         ; nat = λ {X} {Y} f → record
--               { wit = F.ₐ f
--               ; wit₀ = r
--               ; wit₁ = lidgen (ridˢ {f = F.ₐ f})
--               }
--         }
--         where open ecategory-aux-only 𝔼
--               open ecategory-aux-only ℂ using () renaming (r to rℂ)

--     Δ2eqrelΔ : natural-transformation (ΔER 𝔼 ○ F) (imgPeq 𝔼isex Flcov ○ Γex ℂ [ hasfwl ])
--     Δ2eqrelΔ = record
--         { fnc = λ {X} → record
--               { base-ar = 𝔼.idar (F.ₒ  X)
--               ; isext = record
--                       { rel-ar = qrF%.ar (ℂ.freePeq X)
--                       ; cmptb₀ = qrF%.r₁tr (ℂ.freePeq X) ⊙ lidgenˢ F.id
--                       ; cmptb₁ = qrF%.r₂tr (ℂ.freePeq X) ⊙ lidgenˢ F.id
--                       }
--               }
--         ; nat = λ {X} {Y} f → record
--               { wit = qrF%.ar (ℂ.freePeq Y) 𝔼.∘ F.ₐ f
--               ; wit₀ = ass ⊙ ∘e r (qrF%.r₁tr (ℂ.freePeq Y) ⊙ F.id)
--               ; wit₁ = ass ⊙ lidgg (ridˢ {f = F.ₐ f}) (qrF%.r₂tr (ℂ.freePeq Y) ⊙ F.id) 
--               }
--         }
--         where open ecategory-aux-only 𝔼
--   -- end imgPeq-on-free



--   imgPeq-sq : {𝔼 : ecategory} (𝔼isex : is-exact 𝔼) {F : efunctor ℂ 𝔼} (Flcov : is-left-covering F)
--                  → natural-iso (imgPeq 𝔼isex Flcov ○ Γex ℂ [ hasfwl ]) (ΔER 𝔼 ○ F)
--   imgPeq-sq {𝔼} 𝔼isex {F} Flcov = record
--     { natt = eqrelΔ2Δ
--     ; natt⁻¹ = Δ2eqrelΔ
--     ; isiso = λ {X} → record
--             { iddom = record
--                     { wit = qrF%.ar (ℂ.freePeq X)
--                     ; wit₀ = qrF%.r₁tr (ℂ.freePeq X) ⊙ lidgenˢ F.id
--                     ; wit₁ = qrF%.r₂tr (ℂ.freePeq X) ⊙ F.id
--                     }
--             ; idcod = record
--                     { wit = 𝔼.idar (F.ₒ X)
--                     ; wit₀ = r
--                     ; wit₁ = lid
--                     }
--             }
--     }
--     where open imgPeq-on-free 𝔼isex Flcov
--           open ecategory-aux-only 𝔼
--           module 𝔼 = ecategory 𝔼
--           module F = efunctor-aux F

-- -- end eqrel-from-peq-funct

    
-- -- {-
-- --   module imgPeq-on-free  {𝔼 : ecategory} (𝔼isex : is-exact 𝔼) {F : efunctor ℂ 𝔼} (Flcov : is-left-covering F) where
-- --     private
-- --       module 𝔼 where
-- --         open ecategory 𝔼 public
-- --         --open comm-shapes 𝔼 public
-- --         open iso-defs 𝔼 public
-- --         --open iso-transports 𝔼 public
-- --         open epis&monos-defs 𝔼 public
-- --         open epis&monos-props 𝔼 public
-- --         open kernel-pairs-defs 𝔼 public
-- --         open pseudo-eq-rel-defs 𝔼 public
-- --         open eq-rel-defs 𝔼 public
-- --         open image-fact-defs 𝔼 public
-- --         open image-fact-props 𝔼 public
-- --         open binary-products 𝔼 public
-- --         --open pullback-squares 𝔼 public
-- --         --open pullback-props 𝔼 public
-- --         open projective-defs 𝔼 public
-- --         --open cat-of-equivalence-relations 𝔼 public
-- --         --open eqrel-mor-are-arrows public
-- --       module ex𝔼 where
-- --         open exact-cat-d&p 𝔼isex public
-- --         open has-bin-products hasprd using (prd-of) public
-- --       {-module ER𝔼 where
-- --         open ecategory (EqRel 𝔼) public-}
-- --       module ER𝔼 where
-- --         open ecategory (EqRel 𝔼) public
-- --       module F where
-- --         open efunctor-aux F public
-- --         open is-left-covering Flcov public
-- --         open left-covering-into-exact-props hasfwl 𝔼isex Flcov public
-- --       module I = efunctor-aux (imgPeq 𝔼isex Flcov)
-- --       module ΔER = efunctor-aux (ΔER 𝔼)
      
-- --     module qrF% (X : ℂ.Obj) where
-- --       open F.eqrel-from-peq-via-left-covering (ℂ.freePeq X) public -- hiding (eqrel/) 
-- --       open qF% public
-- --       open 𝔼.is-eq-rel iseqr using (jm-pf) renaming (isjm/ to risjm/) public
-- --       eqr : 𝔼.eqrel
-- --       eqr = record { eqrelover = eqrel/ }

-- --     {-F%check : (X : ℂ.Obj) → || 𝔼.Hom (F.ₒ X) (img.FX².O12 X) ||
-- --     F%check X = img.F% X
-- --     F%free-isΔ : (X : ℂ.Obj) → img.F% X 𝔼.~ img.FX².<_,_> X (𝔼.idar (F.ₒ X)) (𝔼.idar (F.ₒ X))
-- --     --(F.ₐ (ℂ.idar X)) (F.ₐ (ℂ.idar X))
-- --     F%free-isΔ X = img.FX².<>~<> X F.id F.id
-- --                  where open ecategory-aux-only 𝔼-}
-- --     {-F%free-monic : (X : ℂ.Obj) → 𝔼.is-monic (img.F% X)
-- --     F%free-monic X = record
-- --       { mono-pf = λ {_} {g} {g'} pf → ~proof
-- --                 g                                 ~[ lidggˢ r (imgX.FX².×tr₁ ⊙ F.id) ⊙ assˢ ] /
-- --                 imgX.FX².π₁ 𝔼.∘ imgX.F% 𝔼.∘ g    ~[ ∘e pf r ] /
-- --                 imgX.FX².π₁ 𝔼.∘ imgX.F% 𝔼.∘ g'   ~[ ass ⊙ lidgg r (imgX.FX².×tr₁ ⊙ F.id) ]∎
-- --                 g' ∎
-- --       }
-- --       where open ecategory-aux-only 𝔼
-- --             module imgX = img X-}
            
-- --     module qrF%-is-iso (X : ℂ.Obj) where
-- --       module qrX = qrF% X

-- --       r₁~r₂ : qrX.r₁ 𝔼.~ qrX.r₂
-- --       r₁~r₂ = qrX.epi-pf (qrX.r₁tr ⊙ qrX.r₂tr ˢ)
-- --             where open ecategory-aux-only 𝔼
-- --       isop₁  : 𝔼.is-iso-pair qrX.ar qrX.r₁
-- --       isop₁ = record
-- --         { iddom = qrX.r₁tr ⊙ F.id
-- --         ; idcod = qrX.jm-pf (ass ⊙ ∘e r qrX.r₁tr ⊙ lidgg ridˢ F.id)
-- --                             (ass ⊙ ∘e r₁~r₂ qrX.r₂tr ⊙ lidgg ridˢ F.id)
-- --         }
-- --         where open ecategory-aux-only 𝔼
-- --       isop₂  : 𝔼.is-iso-pair qrX.ar qrX.r₂
-- --       isop₂ = record
-- --         { iddom = qrX.r₂tr ⊙ F.id
-- --         ; idcod = qrX.jm-pf (ass ⊙ ∘e (r₁~r₂ ˢ) qrX.r₁tr ⊙ lidgg ridˢ F.id)
-- --                             (ass ⊙ ∘e r qrX.r₂tr ⊙ lidgg ridˢ F.id)
-- --         }
-- --         where open ecategory-aux-only 𝔼
-- --       qF%iso₁ qF%iso₂ : 𝔼.is-iso qrX.ar
-- --       qF%iso₁ = iso-defs.mkis-iso isop₁
-- --       qF%iso₂ = iso-defs.mkis-iso isop₂
-- --     -- end qrF%-is-iso
-- -- -}

-- -- {-
-- --     module eqrelΔ2Δ-ar (X : ℂ.Obj) where
-- --       private
-- --         module X = ℂ.Peq
-- --         module qrX = qrF% X
-- --         module qrXiso = qrF%-is-iso X

-- --       ar : || ER𝔼.Hom qrX.eqr (𝔼.free-eqrel (F.ₒ X)) ||
-- --       ar = record
-- --          { base-ar = 𝔼.idar (F.ₒ X)
-- --          ; isext = record
-- --                  { rel-ar = qrX.r₁
-- --                  ; cmptb₀ = r
-- --                  ; cmptb₁ = ∘e qrXiso.r₁~r₂ r
-- --                  }
-- --          }
-- --          where open ecategory-aux-only 𝔼
-- --     -- end eqrelΔ2Δ-ar
-- -- -}


-- --     eqrelΔ2Δ : natural-transformation (imgPeq 𝔼isex Flcov ○ Γex ℂ [ hasfwl ]) (ΔER 𝔼 ○ F)
-- --     eqrelΔ2Δ = record
-- --         { fnc = λ {X} → record
-- --               { base-ar = 𝔼.idar (F.ₒ X)
-- --               ; isext = record
-- --                       { rel-ar = qrF%.r₁ X
-- --                       ; cmptb₀ = r --{qrF%.Ob X} {F.ₒ X} {f = 𝔼.idar (F.ₒ X) 𝔼.∘ qrF%.r₁ X}
-- --                       ; cmptb₁ = ∘e (qrF%-is-iso.r₁~r₂ X) r --∘e (qrF%-is-iso.r₁~r₂ X) (r {f = 𝔼.idar (F.ₒ X)})
-- --                       }
-- --               }
-- --         ; nat = λ {X} {Y} f → record
-- --               { wit = F.ₐ f
-- --               ; wit₀ = r
-- --               ; wit₁ = lidgen (ridˢ {f = F.ₐ f})
-- --               }
-- --         }
-- --         where open ecategory-aux-only 𝔼

-- --     Δ2eqrelΔ : natural-transformation (ΔER 𝔼 ○ F) (imgPeq 𝔼isex Flcov ○ Γex ℂ [ hasfwl ])
-- --     Δ2eqrelΔ = record
-- --         { fnc = λ {X} → record
-- --               { base-ar = 𝔼.idar (F.ₒ X)
-- --               ; isext = record
-- --                       { rel-ar = qrF%.ar X
-- --                       ; cmptb₀ = qrF%.r₁tr X ⊙ lidgenˢ F.id
-- --                       ; cmptb₁ = qrF%.r₂tr X ⊙ lidgenˢ F.id
-- --                       }
-- --               }
-- --         ; nat = λ {X} {Y} f → record
-- --               { wit = qrF%.ar Y 𝔼.∘ F.ₐ f
-- --               ; wit₀ = ass ⊙ ∘e r (qrF%.r₁tr Y ⊙ F.id)
-- --               ; wit₁ = ass ⊙ lidgg (ridˢ {f = F.ₐ f}) (qrF%.r₂tr Y ⊙ F.id) 
-- --               }
-- --         }
-- --         where open ecategory-aux-only 𝔼


-- --   -- end imgPeq-on-free


-- --   imgPeq-sq : {𝔼 : ecategory} (𝔼isex : is-exact 𝔼) {F : efunctor ℂ 𝔼} (Flcov : is-left-covering F)
-- --                  → natural-iso (imgPeq 𝔼isex Flcov ○ Γex ℂ [ hasfwl ]) (ΔER 𝔼 ○ F)
-- --   imgPeq-sq {𝔼} 𝔼isex {F} Flcov = record
-- --     { natt = eqrelΔ2Δ
-- --     ; natt⁻¹ = Δ2eqrelΔ
-- --     ; isiso = λ {X} → record
-- --             { iddom = record
-- --                     { wit = qrF%.ar X
-- --                     ; wit₀ = qrF%.r₁tr X ⊙ lidgenˢ F.id
-- --                     ; wit₁ = qrF%.r₂tr X ⊙ F.id
-- --                     }
-- --             ; idcod = record
-- --                     { wit = 𝔼.idar (F.ₒ X)
-- --                     ; wit₀ = r
-- --                     ; wit₁ = lid
-- --                     }
-- --             }
-- --     }
-- --     where open imgPeq-on-free 𝔼isex Flcov
-- --           open ecategory-aux-only 𝔼
-- --           module 𝔼 = ecategory 𝔼
-- --           module F = efunctor-aux F

-- -- -- end eqrel-from-peq-funct



-- -- -- -- OLD
  
-- -- --   module imgPeq-def {𝔼 : ecategory} (𝔼isex : is-exact 𝔼) {F : efunctor ℂ 𝔼} (Flcov : is-left-covering F) where
-- -- --     private
-- -- --       module 𝔼 where
-- -- --         open ecategory 𝔼 public
-- -- --         --open comm-shapes 𝔼 public
-- -- --         --open iso-defs 𝔼 public
-- -- --         --open iso-transports 𝔼 public
-- -- --         open epis&monos-defs 𝔼 public
-- -- --         open epis&monos-props 𝔼 public
-- -- --         open kernel-pairs-defs 𝔼 public
-- -- --         open pseudo-eq-rel-defs 𝔼 public
-- -- --         open eq-rel-defs 𝔼 public
-- -- --         open image-fact-defs 𝔼 public
-- -- --         --open image-fact-props 𝔼 public
-- -- --         open binary-products 𝔼 public
-- -- --         --open pullback-squares 𝔼 public
-- -- --         --open pullback-props 𝔼 public
-- -- --         open projective-defs 𝔼 public
-- -- --         --open cat-of-equivalence-relations 𝔼 public
-- -- --         --open eqrel-mor-are-arrows public
-- -- --       module ex𝔼 where
-- -- --         open exact-cat-d&p 𝔼isex public
-- -- --         open has-bin-products hasprd using (prd-of) public
-- -- --       {-module ER𝔼 where
-- -- --         open ecategory (EqRel 𝔼) public-}
-- -- --       module F where
-- -- --         open efunctor-aux F public
-- -- --         open is-left-covering Flcov public
-- -- --         open left-covering-into-exact-props hasfwl 𝔼isex Flcov public

-- -- --     eqr/ : (A : Exℂ.Obj) → 𝔼.eqrel-over (F.ₒ (ℂ.Peq.Lo A))
-- -- --     eqr/ A = F.eqrel-from-peq-via-left-covering.eqrel/ A
-- -- --     module img (A : Exℂ.Obj) where
-- -- --       open F.eqrel-from-peq-via-left-covering.imgF% A public
-- -- --       open F.eqrel-from-peq-via-left-covering A hiding (eqrel/) public
-- -- --     eqr : Exℂ.Obj → 𝔼.eqrel
-- -- --     eqr A = record { eqrelover = eqr/ A }
-- -- --     module eqr where
-- -- --       open 𝔼.eqrel-over public
-- -- --       open 𝔼.eqrel-mor public


-- -- --     eqr-ar : {A B : Exℂ.Obj} (f : || Exℂ.Hom A B ||) → 𝔼.eqrel-mor (eqr A) (eqr B)
-- -- --     eqr-ar {A} {B} f = record
-- -- --       { base-ar = F.ₐ f.lo
-- -- --       ; isext = record
-- -- --               { rel-ar = rel-ar
-- -- --               ; cmptb₀ = CA.epi-pf (~proof
-- -- --                        (imgB.r₁ 𝔼.∘ rel-ar) 𝔼.∘ imgA.C    ~[ assˢ ⊙ ∘e (CA.univ-eq rel-ar-pf) r ] /
-- -- --                        imgB.r₁ 𝔼.∘ imgB.C 𝔼.∘ F.ₐ f.hi    ~[ ass ⊙ ∘e r imgB.imgF%tr₁ ⊙ F.∘∘ f.cmptb₀ ] /
-- -- --                        F.ₐ f.lo 𝔼.∘ F.ₐ (ℂ.Peq.%0 A)       ~[ ∘e (imgA.imgF%tr₁ ˢ) r ⊙ ass ]∎
-- -- --                        (F.ₐ f.lo 𝔼.∘ imgA.r₁) 𝔼.∘ imgA.C ∎)
-- -- --               ; cmptb₁ = CA.epi-pf (~proof
-- -- --                        (imgB.r₂ 𝔼.∘ rel-ar) 𝔼.∘ imgA.C    ~[ assˢ ⊙ ∘e (CA.univ-eq rel-ar-pf) r ] /
-- -- --                        imgB.r₂ 𝔼.∘ imgB.C 𝔼.∘ F.ₐ f.hi    ~[ ass ⊙ ∘e r imgB.imgF%tr₂ ⊙ F.∘∘ f.cmptb₁ ] /
-- -- --                        F.ₐ f.lo 𝔼.∘ F.ₐ (ℂ.Peq.%1 A)       ~[ ∘e (imgA.imgF%tr₂ ˢ) r ⊙ ass ]∎
-- -- --                        (F.ₐ f.lo 𝔼.∘ imgA.r₂) 𝔼.∘ imgA.C ∎)
-- -- --               }
-- -- --       }
-- -- --       where module f = ℂ.Peq-mor f
-- -- --             module imgA = img A
-- -- --             module imgB = img B
-- -- --             module CA = 𝔼.is-regular-epi imgA.C-is-repi
-- -- --             module MB = 𝔼.is-monic imgB.M-is-monic
-- -- --             module FAL² = 𝔼.product-of-not (ex𝔼.prd-of (F.ₒ (ℂ.Peq.Lo A)) (F.ₒ (ℂ.Peq.Lo A)))
-- -- --             module FBL² = 𝔼.product-of-not (ex𝔼.prd-of (F.ₒ (ℂ.Peq.Lo B)) (F.ₒ (ℂ.Peq.Lo B)))
-- -- --             open ecategory-aux-only 𝔼
-- -- --             rel-ar-pf : (imgB.C 𝔼.∘ F.ₐ f.hi) 𝔼.∘ CA.rel₁ 𝔼.~ (imgB.C 𝔼.∘ F.ₐ f.hi) 𝔼.∘ CA.rel₂
-- -- --             rel-ar-pf = MB.mono-pf (~proof
-- -- --               imgB.M 𝔼.∘ (imgB.C 𝔼.∘ F.ₐ f.hi) 𝔼.∘ CA.rel₁      ~[ ∘e assˢ r ⊙ ass ⊙ ∘e r imgB.tr ] /
-- -- --               imgB.F% 𝔼.∘ F.ₐ f.hi 𝔼.∘ CA.rel₁
-- -- --                       ~[ ass ⊙ ∘e r (FBL².<>ar~<>ar (F.∘ax f.cmptb₀ ⊙ F.∘ax-rfˢ ⊙ ∘e (FAL².×tr₁ ˢ) r ⊙ ass)
-- -- --                                                      (F.∘ax f.cmptb₁ ⊙ F.∘ax-rfˢ ⊙ ∘e (FAL².×tr₂ ˢ) r ⊙ ass)) ⊙ assˢ ] /
-- -- --               FBL².< F.ₐ f.lo 𝔼.∘ FAL².π₁ , F.ₐ f.lo 𝔼.∘ FAL².π₂ > 𝔼.∘ imgA.F% 𝔼.∘ CA.rel₁
-- -- --                                                 ~[ ∘e (∘e r (imgA.tr ˢ) ⊙ assˢ ⊙ ∘e CA.eq r ⊙ ass ⊙ ∘e r imgA.tr ) r ] /
-- -- --               FBL².< F.ₐ f.lo 𝔼.∘ FAL².π₁ , F.ₐ f.lo 𝔼.∘ FAL².π₂ > 𝔼.∘ imgA.F% 𝔼.∘ CA.rel₂
-- -- --                      ~[ ass ⊙ ∘e r (FBL².<>ar~<>ar (assˢ ⊙ ∘e FAL².×tr₁ r ⊙ F.∘ax-rf ⊙ F.∘axˢ f.cmptb₀)
-- -- --                                                     (assˢ ⊙ ∘e FAL².×tr₂ r ⊙ F.∘ax-rf ⊙ F.∘axˢ f.cmptb₁)) ⊙ assˢ ] /
-- -- --               imgB.F% 𝔼.∘ F.ₐ f.hi 𝔼.∘ CA.rel₂                  ~[ ∘e r (imgB.tr ˢ) ⊙ assˢ ⊙ ∘e ass r ]∎
-- -- --               imgB.M 𝔼.∘ (imgB.C 𝔼.∘ F.ₐ f.hi) 𝔼.∘ CA.rel₂ ∎)
-- -- --             rel-ar : || 𝔼.Hom imgA.Ob imgB.Ob ||
-- -- --             rel-ar = CA.univ (imgB.C 𝔼.∘ F.ₐ f.hi) rel-ar-pf

-- -- --     eqr-ar-ext : {A B : Exℂ.Obj} (f f' : || Exℂ.Hom A B ||)
-- -- --                     → f Exℂ.~ f' → 𝔼.eqrel-mor-eq (eqr-ar {A} {B} f) (eqr-ar {A} {B} f')
-- -- --     eqr-ar-ext {A} {B} f f' hty = record
-- -- --       { wit = imgB.C 𝔼.∘ F.ₐ f~f'.hty
-- -- --       ; wit₀ = ~proof imgB.r₁ 𝔼.∘ imgB.C 𝔼.∘ F.ₐ f~f'.hty    ~[ ass ⊙ ∘e r imgB.imgF%tr₁ ] /
-- -- --                       F.ₐ B.%0 𝔼.∘ F.ₐ f~f'.hty               ~[ F.∘ax f~f'.hty₀ ]∎
-- -- --                       F.ₐ f.lo ∎
-- -- --       ; wit₁ = ~proof imgB.r₂ 𝔼.∘ imgB.C 𝔼.∘ F.ₐ f~f'.hty    ~[ ass ⊙ ∘e r imgB.imgF%tr₂ ] /
-- -- --                       F.ₐ B.%1 𝔼.∘ F.ₐ f~f'.hty               ~[ F.∘ax f~f'.hty₁ ]∎
-- -- --                       F.ₐ f'.lo ∎
-- -- --       }
-- -- --       where module B = ℂ.Peq B
-- -- --             module f = ℂ.Peq-mor f
-- -- --             module f' = ℂ.Peq-mor f'
-- -- --             module f~f' = ℂ.Peq-mor-eq hty
-- -- --             module imgB = img B
-- -- --             open ecategory-aux-only 𝔼

-- -- -- {- problems with amount of time for typechecking in imgPeq 
-- -- --     eqr-ar-id : (A : Exℂ.Obj) → 𝔼.eqrel-mor-eq (eqr-ar {A} {A} (Exℂ.idar A)) (𝔼.eqrel-idar (eqr A))
-- -- --     --(eqr-ar {A} {A} (Exℂ.idar A)) ER𝔼.~ (ER𝔼.idar (eqr A))
-- -- --     eqr-ar-id A = record
-- -- --       { wit = erA.ρ
-- -- --       ; wit₀ = erA.ρ-ax₀ ⊙ F.idˢ
-- -- --       ; wit₁ = erA.ρ-ax₁
-- -- --       } --𝔼.eqrel-mor-eq-ext F.id
-- -- --       where --module A = ℂ.Peq A
-- -- --             module erA = 𝔼.eqrel (eqr A)
-- -- --             open ecategory-aux-only 𝔼
    
-- -- --     eqr-ar-cmp : {A B C : Exℂ.Obj} (f : || Exℂ.Hom A B ||) (g : || Exℂ.Hom B C ||)
-- -- --                     → (eqr-ar {B} {C} g ER𝔼.∘ eqr-ar {A} {B} f) ER𝔼.~ (eqr-ar {A} {C} (g Exℂ.∘ f))
-- -- --     eqr-ar-cmp f g = 𝔼.eqrel-mor-eq-ext F.∘ax-rf --𝔼.eqrel-mor-eq-ext F.∘ax-rf
-- -- -- -}

-- -- --   -- end imgPeq-def
