
{-# OPTIONS --without-K #-}

module ecats.small-limits.props.small-limit where

open import tt-basics.basics
open import ecats.basic-defs.ecat-def&not
open import ecats.functors.defs.efunctor-d&n
open import ecats.functors.defs.natural-transformation
open import ecats.constructions.functor-ecat
open import ecats.constructions.slice-ecat
open import ecats.finite-limits.defs.terminal
open import ecats.finite-limits.defs.equaliser
open import ecats.small-limits.defs.small-limit

module small-limit-props (ℂ : ecategory) where
  private
    module ℂ where
      open ecategory ℂ public
      open equaliser-defs ℂ public
      open small-limit-defs ℂ public

  module limit-as-eql (hasprd : has-small-products ℂ){𝕀 : small-ecategory}(D : 𝕀 diag-in ℂ) where
    open has-small-products hasprd using (prd-of)
    private
      module 𝕀 where
        open ecategory-aux 𝕀 public
        Arr : Set
        Arr = Σ (prod Obj Obj) (λ z → || Hom (prj1 z) (prj2 z) ||)
        d c : Arr → Obj
        d u = prj1 (pj1 u)
        c u = prj2 (pj1 u)
      module D = diagram D
      module Cone/D = Cone/ D
      module Span/D = Span/ ℂ D.ₒ
      Span/Dc : ecategoryₗₑᵥ (ecat.ℓₙₒ~ ℂ) (ecat.ℓₕₒₘ ℂ) (ecat.ℓ~ ℂ)
      Span/Dc = Span/ {𝕀.Arr} ℂ (λ u → D.ₒ (𝕀.c u))
      module Span/Dc = Span/ {𝕀.Arr} ℂ (λ u → D.ₒ (𝕀.c u))
      module cn/D = Cone/D.ₒ
          
    cod-fam : 𝕀.Arr → ℂ.Obj
    cod-fam u = D.ₒ (𝕀.c u)
    module dom = prd-of D.ₒ
    module cod = prd-of cod-fam
    ar₁fam ar₂fam : Span/Dc.Obj
    ar₁fam = record
           { L = dom.Vx
           ; ar = λ u → dom.π (𝕀.c u)
           }
    ar₂fam = record
           { L = dom.Vx
           ; ar = λ u → D.ₐ (pj2 u) ℂ.∘ dom.π (𝕀.d u)
           }
    module ar₁fam = Span/Dc.ₒ ar₁fam
    module ar₂fam = Span/Dc.ₒ ar₂fam
    ar₁ ar₂ : || ℂ.Hom dom.Vx cod.Vx ||
    ar₁ = cod.unv.ar ar₁fam
    ar₂ = cod.unv.ar ar₂fam

    eqleq→cone : {E : ℂ.Obj}{e : || ℂ.Hom E dom.Vx ||}(eqleq : ar₁ ℂ.∘ e ℂ.~ ar₂ ℂ.∘ e)
                    → Cone/D.Obj
    eqleq→cone {E} {e} eqleq = record
      { L = E
      ; ar = record
           { fnc = λ {i} → dom.π i ℂ.∘ e
           ; nat = λ {i} {j} ij → ~proof
                 (dom.π j ℂ.∘ e) ℂ.∘ ℂ.idar E
                           ~[ assˢ ⊙ ∘e (ℂ.ridax e) (cod.unv.tr ar₁fam (pair i j , ij)  ˢ) ] /
                 (cod.π (pair i j , ij) ℂ.∘ ar₁) ℂ.∘ e         ~[ assˢ ⊙ ∘e eqleq r ⊙ ass ] /
                 (cod.π (pair i j , ij) ℂ.∘ ar₂) ℂ.∘ e
                                        ~[ ∘e r (cod.unv.tr ar₂fam (pair i j , ij)) ⊙ assˢ  ]∎
                 D.ₐ ij ℂ.∘ dom.π i ℂ.∘ e ∎
           }
      }
      where open ecategory-aux-only ℂ

    cone→eqlar : (cone : Cone/D.Obj) → || ℂ.Hom (cn/D.Vx cone) dom.Vx ||
    cone→eqlar cone = dom.unv.ar (cone→span cone)
    

    cone→eqleq : (cone : Cone/D.Obj) → ar₁ ℂ.∘ cone→eqlar cone ℂ.~ ar₂ ℂ.∘ cone→eqlar cone
    cone→eqleq cone = cod.π-jm sp/Arr
                               (λ u → ~proof
               cod.π u ℂ.∘ ar₁ ℂ.∘ cone→eqlar cone   ~[ ass ⊙ ∘e r (cod.unv.tr ar₁fam u) ] /
               ar₁fam.leg u ℂ.∘ cone→eqlar cone      ~[ dom.unv.tr (cone→span cone) (prj2 (pj1 u)) ]∎
               cone.leg (prj2 (pj1 u)) ∎)
                               (λ u → ~proof
               cod.π u ℂ.∘ ar₂ ℂ.∘ cone→eqlar cone   ~[ ass ⊙ ∘e r (cod.unv.tr ar₂fam u) ] /
               ar₂fam.leg u ℂ.∘ cone→eqlar cone      ~[ assˢ ⊙ ∘e (dom.unv.tr (cone→span cone) (prj1 (pj1 u))) r ] /
               D.ₐ (pj2 u) ℂ.∘ cone.leg (prj1 (pj1 u))  ~[ cone.tr (pj2 u) ]∎
               cone.leg (prj2 (pj1 u)) ∎)
                     where open ecategory-aux-only ℂ
                           module cone = cn/D cone
                           sp/Arr : Span/.Obj ℂ (λ (u : 𝕀.Arr) → D.ₒ (prj2 (pj1 u)))
                           sp/Arr = record
                                  { L = cone.Vx
                                  ; ar = λ u → cone.leg (prj2 (pj1 u))
                                  }
                           
    
    module is-eql→is-lim {E : ℂ.Obj}{e : || ℂ.Hom E dom.Vx ||}{eqleq : ar₁ ℂ.∘ e ℂ.~ ar₂ ℂ.∘ e}
                          (iseql : ℂ.is-equaliser eqleq)
                          where
      module eql = ℂ.is-equaliser iseql
      L : Cone/D.Obj
      L = eqleq→cone eqleq
      module L = Cone/D.ₒ L

      unv-ar : (C : Cone/D.Obj) → || Cone/D.Hom C L ||
      unv-ar C = record
        { arL = ar
        ; tr = λ I → ~proof
                L.leg I ℂ.∘ ar             ~[ assˢ ⊙ ∘e (eql.eqltr (cone→eqleq C)) r ] /
                dom.π I ℂ.∘ cone→eqlar C    ~[ dom.unv.tr (cone→span C) I ]∎
                C.leg I ∎
        }
        where open ecategory-aux-only ℂ
              module C = Cone/D.ₒ C
              ar : || ℂ.Hom C.Vx L.Vx ||
              ar = cone→eqlar C eql.|eql[ cone→eqleq C ]


      unv-uq : {C : Cone/D.Obj}(f : || Cone/D.Hom C L ||)
                  → f Cone/D.~ unv-ar C
      unv-uq {C} f = eql.eqluq (dom.π-jm (cone→span C)
                                         (λ I → ass ⊙ f.tr I)
                                         λ I → ass ⊙ unvar.tr I )
                   where open ecategory-aux-only ℂ using (ass; _⊙_)
                         module C = Cone/D.ₒ C
                         module f = Cone/D.ₐ f
                         module unvar = Cone/D.ₐ (unv-ar C)
    -- end is-eql→is-lim

    module is-lim→is-eql {L : Cone/D.Obj}(islim : ℂ.is-limit-cone L) where
      module L where
        open Cone/D.ₒ L renaming (leg to π) public
        open ℂ.is-limit-cone islim public

      unv-ar : {C : ℂ.Obj}(h : || ℂ.Hom C dom.Vx ||)
                  → ar₁ ℂ.∘ h ℂ.~ ar₂ ℂ.∘ h → || ℂ.Hom C L.Vx ||
      unv-ar _ eq = L.unv.ar (eqleq→cone eq)

      unv-tr : {C : ℂ.Obj} {h : || ℂ.Hom C dom.Vx ||}(eq : ar₁ ℂ.∘ h ℂ.~ ar₂ ℂ.∘ h)
                  → cone→eqlar L ℂ.∘ unv-ar h eq ℂ.~ h
      unv-tr {C} {h} eq = dom.π-jm (cone→span (eqleq→cone eq))
                                   (λ I → ~proof
                  dom.π I ℂ.∘ cone→eqlar L ℂ.∘ unv-ar h eq  ~[ ass ⊙ ∘e r (dom.unv.tr (cone→span L) I) ] /
                  L.π I ℂ.∘ unv-ar h eq                      ~[ L.unv.tr (eqleq→cone eq) I ]∎
                  dom.π I ℂ.∘ h ∎)
                                   (λ _ → r)
                where open ecategory-aux-only ℂ
      unv-uq : {C : ℂ.Obj} {h h' : || ℂ.Hom C L.Vx ||}
                  → cone→eqlar L ℂ.∘ h ℂ.~ cone→eqlar L ℂ.∘ h' → h ℂ.~ h'
      unv-uq {C} {h} {h'} eq = L.π-jm (λ I → ~proof
                 L.π I ℂ.∘ h                         ~[ ∘e r (dom.unv.tr (cone→span L) I ˢ) ] /
                 (dom.π I ℂ.∘ cone→eqlar L) ℂ.∘ h   ~[ assˢ ⊙ ∘e eq r ⊙ ass ] /
                 (dom.π I ℂ.∘ cone→eqlar L) ℂ.∘ h'  ~[ ∘e r (dom.unv.tr (cone→span L) I) ]∎
                             L.π I ℂ.∘ h' ∎)
                             where open ecategory-aux-only ℂ
    -- end is-lim→is-eql

    
    is-eql→is-lim : {E : ℂ.Obj}{e : || ℂ.Hom E dom.Vx ||}
                    {eqleq : ar₁ ℂ.∘ e ℂ.~ ar₂ ℂ.∘ e}(iseql : ℂ.is-equaliser eqleq)
                      → ℂ.is-limit-cone (eqleq→cone eqleq)
    is-eql→is-lim iseql = record
      { ! = unv-ar
      ; !uniq = unv-uq
      }
      where open is-eql→is-lim iseql

    is-lim→is-eql : {L : Cone/D.Obj} → ℂ.is-limit-cone L → ℂ.is-equaliser (cone→eqleq L)
    is-lim→is-eql {L} islim = record
        { _|eql[_] = unv-ar
        ; eqltr = unv-tr
        ; eqluq = unv-uq
        }
        where open is-lim→is-eql islim

    lim-of→eql-of : ℂ.limit-of D → ℂ.equaliser-of ar₁ ar₂
    lim-of→eql-of lim = record
      { eqlar = cone→eqlar lim.cone
      ; eqleq = cone→eqleq lim.cone
      ; iseql = is-lim→is-eql lim.islim
      }
      where module lim = ℂ.limit-of lim

    eql-of→lim-of : ℂ.equaliser-of ar₁ ar₂ → ℂ.limit-of D
    eql-of→lim-of eql = record
      { cone = eqleq→cone eql.eqleq
      ; islim = is-eql→is-lim eql.iseql
      }
      where module eql = ℂ.equaliser-of eql
  --- end limit-as-eql
  
-- end small-limit-props
