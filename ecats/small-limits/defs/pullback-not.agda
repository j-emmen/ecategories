
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
  private
    module cspdg (cosp : Cospan diag-in ℂ) = cospan-dg-aux cosp
    module spcn {cosp : Cospan diag-in ℂ}(sp : Cone/.Obj cosp) = Cone/.ₒ cosp sp

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
  -- end is-pullback-cone


  mk-is-pullback-cone : {cosp : Cospan diag-in ℂ}(sp : Cone/.Obj cosp)
                        (ar : {X : ℂ.Obj}(h : || ℂ.Hom X (cspdg.ₒ cosp Csp.v₁) ||)(k : || ℂ.Hom X (cspdg.v₂ cosp) ||)
                                 → cspdg.a₁ cosp ℂ.∘ h ℂ.~ cspdg.a₂ cosp ℂ.∘ k → || ℂ.Hom X (spcn.Vx sp) ||)
                        (tr₁ : {X : ℂ.Obj}{h : || ℂ.Hom X (cspdg.v₁ cosp) ||}{k : || ℂ.Hom X (cspdg.v₂ cosp) ||}(pf : cspdg.a₁ cosp ℂ.∘ h ℂ.~ cspdg.a₂ cosp ℂ.∘ k)
                                  → spcn.leg sp Csp.v₁ ℂ.∘ ar h k pf ℂ.~ h)
                        (tr₂ : {X : ℂ.Obj}{h : || ℂ.Hom X (cspdg.v₁ cosp) ||}{k : || ℂ.Hom X (cspdg.v₂ cosp) ||}(pf : cspdg.a₁ cosp ℂ.∘ h ℂ.~ cspdg.a₂ cosp ℂ.∘ k)
                                  → spcn.leg sp Csp.v₂ ℂ.∘ ar h k pf ℂ.~ k)
                        (π-jm : {X : ℂ.Obj}{h h' : || ℂ.Hom X (spcn.Vx sp) ||}
                                   → spcn.leg sp Csp.v₁ ℂ.∘ h ℂ.~ spcn.leg sp Csp.v₁ ℂ.∘ h'
                                   → spcn.leg sp Csp.v₂ ℂ.∘ h ℂ.~ spcn.leg sp Csp.v₂ ℂ.∘ h'
                                   → h ℂ.~ h')
                          → ℂ.is-pullback-cone sp
  mk-is-pullback-cone {cosp} sp ar tr₁ tr₂ π-jm = record
    { ! = mor
    ; !uniq = uq
    }
    where module csp = cspdg cosp
          module sp = spcn sp
          module Cn/csp = Cone/ cosp
          mor : (cn : Cn/csp.Obj) → || Cn/csp.Hom cn sp ||
          mor cn = record
            { arL = morar
            ; tr = mortr
            }
            where module cn = Cn/csp.ₒ cn
                  open ecategory-aux-only ℂ
                  morpf : csp.a₁ ℂ.∘ cn.leg Csp.v₁ ℂ.~ csp.a₂ ℂ.∘ cn.leg Csp.v₂
                  morpf = cn.tr Csp.a₁ ⊙ cn.tr Csp.a₂ ˢ
                  morar : || ℂ.Hom cn.Vx sp.Vx ||
                  morar = ar (cn.leg Csp.v₁) (cn.leg Csp.v₂) morpf
                  mortr : (A : Csp.Obj) → sp.leg A ℂ.∘ morar ℂ.~ cn.leg A
                  mortr (inl 0₁) = ~proof
                    sp.leg Csp.crn ℂ.∘ morar            ~[ ∘e r (sp.tr Csp.a₁ ˢ) ⊙ assˢ ] /
                    csp.a₁ ℂ.∘ sp.leg Csp.v₁ ℂ.∘ morar  ~[ ∘e (tr₁ morpf) r ] /
                    csp.a₁ ℂ.∘ cn.leg Csp.v₁            ~[ cn.tr Csp.a₁ ]∎
                    cn.leg Csp.crn ∎
                  mortr (inr (inl 0₁)) = tr₁ (cn.tr Csp.a₁ ⊙ cn.tr Csp.a₂ ˢ)
                  mortr (inr (inr 0₁)) = tr₂ (cn.tr Csp.a₁ ⊙ cn.tr Csp.a₂ ˢ)
          module mor (cn : Cn/csp.Obj) = Cn/csp.ₐ (mor cn)
          uq : {cn : Cn/csp.Obj} (f : || Cn/csp.Hom cn sp ||) → f Cn/csp.~ mor cn
          uq {cn} f = π-jm (f.tr Csp.v₁ ⊙ mor.tr cn Csp.v₁ ˢ)
                           (f.tr Csp.v₂ ⊙ mor.tr cn Csp.v₂ ˢ)
                    where module cn = Cn/csp.ₒ cn
                          module f = Cn/csp.ₐ f
                          open ecategory-aux-only ℂ using (_⊙_; _ˢ)



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
  -- end pullback-cone-of  
-- end pullback-diag-not
