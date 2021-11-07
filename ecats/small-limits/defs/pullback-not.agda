
{-# OPTIONS --without-K #-}

module ecats.small-limits.defs.pullback-not where

open import tt-basics.basics
open import ecats.basic-defs.ecat-def&not
open import ecats.basic-defs.commut-shapes
open import ecats.functors.defs.efunctor-d&n
open import ecats.functors.defs.cone
open import ecats.functors.defs.natural-transformation
open import ecats.constructions.functor-ecat
open import ecats.constructions.slice-ecat
open import ecats.finite-limits.defs.terminal
open import ecats.small-limits.defs.small-limit
open import ecats.small-limits.defs.pullback
open import ecats.concr-ecats.finite-ecat


module pullback-diag-not {ℓ₁ ℓ₂ ℓ₃ : Level}(ℂ : ecategoryₗₑᵥ ℓ₁ ℓ₂ ℓ₃) where
  private
    module ℂ where
      open ecat ℂ public
      open small-limit-defs ℂ public
      open pullback-diag-defs ℂ public
    module Csp = Cospan-aux

  module cospan-dg-aux (cosp : Cospan diag-in ℂ) where
    open diagram cosp public
    crn v₁ v₂ : ℂ.Obj
    crn = ₒ Csp.crn
    v₁ = ₒ Csp.v₁
    v₂ = ₒ Csp.v₂
    a₁ : || ℂ.Hom v₁ crn ||
    a₁ = ₐ Csp.a₁
    a₂ : || ℂ.Hom v₂ crn ||
    a₂ = ₐ Csp.a₂     

  private module cspdg (cosp : Cospan diag-in ℂ) = cospan-dg-aux cosp
  sqpf2cone : (cosp : Cospan diag-in ℂ)
              {X : ℂ.Obj}{h : || ℂ.Hom X (cspdg.v₁ cosp) ||}{k : || ℂ.Hom X (cspdg.v₂ cosp) ||}
                  → (cspdg.a₁ cosp) ℂ.∘ h ℂ.~ (cspdg.a₂ cosp) ℂ.∘ k → Cone/.Obj cosp
  sqpf2cone cosp {X} {h} {k} pf = record
    { L = X
    ; ar = record
         { fnc = λ {A} → fnc A
         ; nat = nat
         }
    }
    where module csp = cspdg cosp
          fnc : (A : Cospan-aux.Obj) → || ℂ.Hom X (csp.ₒ A) ||
          fnc (inl 0₁) = csp.a₁ ℂ.∘ h
          fnc (inr (inl 0₁)) = h
          fnc (inr (inr 0₁)) = k
          nat : {A B : Cospan-aux.Obj}(f : || Cospan-aux.Hom A B ||)
                   → fnc B ℂ.∘ ℂ.idar X ℂ.~ csp.ₐ f ℂ.∘ fnc A
          nat {inl 0₁} {inl 0₁} 0₁ = ridgen (lidggˢ r csp.id)
                                       where open ecategory-aux-only ℂ using (ridgen; lidggˢ; r)
          nat {inr (inl 0₁)} {inl 0₁} 0₁ = rid
                                       where open ecategory-aux-only ℂ using (rid)
          nat {inr (inr 0₁)} {inl 0₁} 0₁ = ridgen pf
                                       where open ecategory-aux-only ℂ using (ridgen)
          nat {inr (inl 0₁)} {inr (inl 0₁)} 0₁ = ridgen (lidggˢ r csp.id)
                                       where open ecategory-aux-only ℂ using (ridgen; lidggˢ; r)
          nat {inr (inr 0₁)} {inr (inr 0₁)} 0₁ = ridgen (lidggˢ r csp.id)
                                       where open ecategory-aux-only ℂ using (ridgen; lidggˢ; r)


  module is-pullback-cone {cosp : Cospan diag-in ℂ}{sp : Cone/.Obj cosp}
                          (ispbcn : ℂ.is-pullback-cone sp)
                          where
    private
      module csp = cospan-dg-aux cosp
      module sp = Cone/.ₒ cosp sp
      module pbcn = ℂ.is-limit-cone ispbcn
    ⟨_,_⟩[_] : {X : ℂ.Obj}(h : || ℂ.Hom X (csp.ₒ Csp.v₁) ||)(k : || ℂ.Hom X csp.v₂ ||)
                  → csp.a₁ ℂ.∘ h ℂ.~ csp.a₂ ℂ.∘ k → || ℂ.Hom X sp.Vx ||
    ⟨ h , k ⟩[ pf ] = pbcn.unv.ar (sqpf2cone cosp pf)
    tr₁ : {X : ℂ.Obj}{h : || ℂ.Hom X csp.v₁ ||}{k : || ℂ.Hom X csp.v₂ ||}
          (pf : csp.a₁ ℂ.∘ h ℂ.~ csp.a₂ ℂ.∘ k) → sp.leg Csp.v₁ ℂ.∘ ⟨ h , k ⟩[ pf ] ℂ.~ h
    tr₁ {X} {h} {k} pf = pbcn.unv.tr (sqpf2cone cosp pf) Csp.v₁
    tr₂ : {X : ℂ.Obj}{h : || ℂ.Hom X csp.v₁ ||}{k : || ℂ.Hom X csp.v₂ ||}
          (pf : csp.a₁ ℂ.∘ h ℂ.~ csp.a₂ ℂ.∘ k) → sp.leg Csp.v₂ ℂ.∘ ⟨ h , k ⟩[ pf ] ℂ.~ k
    tr₂ {X} {h} {k} pf = pbcn.unv.tr (sqpf2cone cosp pf) Csp.v₂
    π-jm : {X : ℂ.Obj}{h h' : || ℂ.Hom X sp.Vx ||}
              → sp.leg Csp.v₁ ℂ.∘ h ℂ.~ sp.leg Csp.v₁ ℂ.∘ h'
              → sp.leg Csp.v₂ ℂ.∘ h ℂ.~ sp.leg Csp.v₂ ℂ.∘ h'
                → h ℂ.~ h'
    π-jm {X} {h} {h'} pf1 pf2 = pbcn.π-jm pf
                              where pf : (i : Csp.Obj) → sp.leg i ℂ.∘ h ℂ.~ sp.leg i ℂ.∘ h'
                                    pf (inl 0₁) = ~proof
                                      sp.leg (inl 0₁) ℂ.∘ h         ~[ ∘e r (sp.tr Csp.a₁ ˢ) ⊙ assˢ ] /
                                      csp.a₁ ℂ.∘ sp.leg Csp.v₁ ℂ.∘ h    ~[ ∘e pf1 r ] /
                                      csp.a₁ ℂ.∘ sp.leg Csp.v₁ ℂ.∘ h'   ~[ ass ⊙ ∘e r (sp.tr Csp.a₂) ]∎
                                      sp.leg (inl 0₁) ℂ.∘ h' ∎
                                                  where open ecategory-aux-only ℂ
                                    pf (inr (inl 0₁)) = pf1
                                    pf (inr (inr 0₁)) = pf2


  module pullback-cone-of {cosp : Cospan diag-in ℂ}(pbcnof : ℂ.pullback-cone-of cosp)
                          where
    private
      module csp = cospan-dg-aux cosp
      module pbcn = ℂ.limit-of pbcnof
    Vx : ℂ.Obj
    Vx = pbcn.Vx
    π₁ : || ℂ.Hom Vx csp.v₁ ||
    π₁ = pbcn.π Csp.v₁
    π₂ : || ℂ.Hom Vx csp.v₂ ||
    π₂ = pbcn.π Csp.v₂
    sqpf : csp.a₁ ℂ.∘ π₁ ℂ.~ csp.a₂ ℂ.∘ π₂
    sqpf = pbcn.tr Csp.a₁ ⊙ pbcn.tr Csp.a₂ ˢ
           where open ecategory-aux-only ℂ using (_⊙_; _ˢ)
    open is-pullback-cone pbcn.islim public 
-- end pullback-diag-not
