
{-# OPTIONS --without-K #-}

module ecats.small-limits.props.small-limit where

open import tt-basics.basics
open import ecats.basic-defs.ecat-def&not
open import ecats.basic-defs.isomorphism
open import ecats.functors.defs.efunctor-d&n
open import ecats.functors.defs.natural-transformation
open import ecats.functors.defs.natural-iso
open import ecats.functors.defs.cone
open import ecats.functors.defs.basic-defs
open import ecats.constructions.functor-ecat
open import ecats.constructions.slice-ecat
open import ecats.constructions.discrete-ecat
open import ecats.finite-limits.defs.terminal
open import ecats.finite-limits.props.terminal
open import ecats.finite-limits.defs.equaliser
open import ecats.small-limits.defs.small-limit

module small-limit-props {ℓₒ ℓₐ ℓ~ : Level}(ℂ : ecategoryₗₑᵥ ℓₒ ℓₐ ℓ~) where
  private
    module ℂ where
      open ecat ℂ public
      open equaliser-defs ℂ public
      open small-limit-defs ℂ public

  -- limit is invariant under iso of cones

  module limit-invariant-under-coneiso {𝕀 : small-ecategory}{D : 𝕀 diag-in ℂ}
                                       (cn₁ cn₂ : Cone/.Obj D)
                                       where
    private
      module 𝕀 = ecat 𝕀
      module D = efctr D
      module Cn/D where
        open Cone/ D public
        open iso-defs (Cone/ D) public
        open terminal-defs (Cone/ D) public
        open terminal-props (Cone/ D) public
      module cn₁ = Cn/D.ₒ cn₁
      module cn₂ = Cn/D.ₒ cn₂

  -- end limit-invariant-under-coneiso

  isolim-is-lim : {𝕀 : small-ecategory}{D : 𝕀 diag-in ℂ}{cn₁ cn₂ : Cone/.Obj D}
                     → iso-defs._≅ₒ_ (Cone/ D) cn₁ cn₂ → ℂ.is-limit-cone cn₁ → ℂ.is-limit-cone cn₂
  isolim-is-lim {𝕀} {D} = iso!-is!
                         where open terminal-props (Cone/ D)


  -- limit is invariant under natural iso of diagrams

  module limit-invariant-under-natiso {𝕀 : small-ecategory}{D D' : 𝕀 diag-in ℂ}(D≅D' : D ≅ₐ D') where
    private
      module 𝕀 = ecat 𝕀
      module D = efctr D
      module D' = efctr D'
      module D≅D' where
        open natural-iso D≅D' public
        open _≡ᶜᵃᵗ_ (cone-iso-trsp D≅D') renaming (a12 to trsp; a21 to trsp⁻¹) public
        module trsp = efctr trsp
        module trsp⁻¹ = efctr trsp⁻¹
      module Cn/D where
        open Cone/ D public
        open iso-defs (Cone/ D) public
      module Cn/D' where
        open Cone/ D' public
        open iso-defs (Cone/ D') public

    trsp-lim : {cn : Cn/D.Obj} → ℂ.is-limit-cone cn → ℂ.is-limit-cone (D≅D'.trsp.ₒ cn)
    trsp-lim {cn} islim = record
      { ! = λ cn' → record
          { arL = cn.unv.ar (D≅D'.trsp⁻¹.ₒ cn')
          ; tr = λ I → ~proof
               (D≅D'.fnc ℂ.∘ cn.leg I) ℂ.∘ cn.unv.ar (D≅D'.trsp⁻¹.ₒ cn')
                                                     ~[ assˢ ⊙ ∘e (cn.unv.tr (D≅D'.trsp⁻¹.ₒ cn') I) r ] /
               D≅D'.fnc ℂ.∘ D≅D'.fnc⁻¹ ℂ.∘ Cn/D'.ₒ.leg cn' I            ~[ ass ⊙ lidgg r D≅D'.idcod ]∎
               Cn/D'.ₒ.leg cn' I ∎
          }
      ; !uniq = λ {cn'} f → lidˢ ⊙ cn.unv.uq-cn (D≅D'.trsp⁻¹.ₒ cn')
                                                 (D≅D'.ι2.fnc {cn} Cn/D.∘ D≅D'.trsp⁻¹.ₐ f)
      }
      where open ecategory-aux-only ℂ
            module cn where
              open Cn/D.ₒ cn public
              open ℂ.is-limit-cone islim public

    trsp-lim-conv : {cn' : Cn/D'.Obj} → ℂ.is-limit-cone (D≅D'.trsp⁻¹.ₒ cn') → ℂ.is-limit-cone cn'
    trsp-lim-conv {cn'} islim = isolim-is-lim iso (trsp-lim islim)
                              where iso : D≅D'.trsp.ₒ (D≅D'.trsp⁻¹.ₒ cn') Cn/D'.≅ₒ cn'
                                    iso = record
                                      { a12 = D≅D'.ι1.fnc {cn'}
                                      ; a21 = D≅D'.ι1.fnc⁻¹ {cn'} 
                                      ; isop = D≅D'.ι1.isiso {cn'}
                                      }
  
    trsp⁻¹-lim : {cn' : Cn/D'.Obj} → ℂ.is-limit-cone cn' → ℂ.is-limit-cone (D≅D'.trsp⁻¹.ₒ cn')
    trsp⁻¹-lim {cn'} islim = record
      { ! = λ cn → record
          { arL = cn'.unv.ar (D≅D'.trsp.ₒ cn)
          ; tr = λ I → ~proof
               (D≅D'.fnc⁻¹ ℂ.∘ cn'.leg I) ℂ.∘ cn'.unv.ar (D≅D'.trsp.ₒ cn)
                                                     ~[ assˢ ⊙ ∘e (cn'.unv.tr (D≅D'.trsp.ₒ cn) I) r ] /
               D≅D'.fnc⁻¹ ℂ.∘ D≅D'.fnc ℂ.∘ Cn/D.ₒ.leg cn I            ~[ ass ⊙ lidgg r D≅D'.iddom ]∎
               Cn/D.ₒ.leg cn I ∎
          }
      ; !uniq = λ {cn} f → lidˢ ⊙ cn'.unv.uq-cn (D≅D'.trsp.ₒ cn)
                                                 (D≅D'.ι1.fnc {cn'} Cn/D'.∘ D≅D'.trsp.ₐ f)
      }
      where open ecategory-aux-only ℂ
            module cn' where
              open Cn/D'.ₒ cn' public
              open ℂ.is-limit-cone islim public
            
  -- end limit-invariant-under-natiso

  module small-prod-is-small-limit {I : Set}(D : I → ecat.Obj ℂ) where
    ↑I : small-ecategory
    ↑I = small-disc-ecat I    
    ↑Dg : efunctorₗₑᵥ ↑I ℂ
    ↑Dg = disc-ecat-lift-efctr ℂ D
    private
      module ↑I = ecat ↑I
      module ↑D = efctr ↑Dg

    is-prod→is-lim : {span : Span/.Obj ℂ D} → ℂ.is-product span
                           → ℂ.is-limit-cone (span→cone ℂ span)
    is-prod→is-lim isprd = record
      { ! = λ cn → record
          { arL = ×sp.unv.ar (cone→span cn)
          ; tr = ×sp.unv.tr (cone→span cn)
          }
      ; !uniq = λ {cn} f → ×sp.unv.uq (cone→span cn) (Cone/.ₐ.tr f)
      }
      where module ×sp = ℂ.is-product isprd

    is-lim→is-prod : {cone : Cone/.Obj ↑Dg} → ℂ.is-limit-cone cone
                           → ℂ.is-product (cone→span cone)
    is-lim→is-prod islim = record
      { ! = λ sp → record
          { arL = ×sp.unv.ar (span→cone ℂ sp)
          ; tr = ×sp.unv.tr (span→cone ℂ sp)
          }
      ; !uniq = λ {sp} f → ×sp.unv.uq (span→cone ℂ sp) (Span/.ₐ.tr f)
      }
      where module ×sp = ℂ.is-limit-cone islim
    prod-of→lim-of : ℂ.product-of D → ℂ.limit-of ↑Dg
    prod-of→lim-of prdof = record
      { cone = span→cone ℂ ×sp.span/
      ; islim = is-prod→is-lim ×sp.isprd
      }
      where module ×sp = ℂ.product-of prdof    
    lim-of→prod-of : ℂ.limit-of ↑Dg → ℂ.product-of D
    lim-of→prod-of limof = record
      { span/ = cone→span ×sp.cone
      ; isprd = is-lim→is-prod ×sp.islim
      }
      where module ×sp = ℂ.limit-of limof
  -- end small-prod-is-small-limit



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
                L.leg I ℂ.∘ ar             ~[ assˢ ⊙ ∘e (eql.tr (cone→eqleq C)) r ] /
                dom.π I ℂ.∘ cone→eqlar C    ~[ dom.unv.tr (cone→span C) I ]∎
                C.leg I ∎
        }
        where open ecategory-aux-only ℂ
              module C = Cone/D.ₒ C
              ar : || ℂ.Hom C.Vx L.Vx ||
              ar = cone→eqlar C eql.|[ cone→eqleq C ]


      unv-uq : {C : Cone/D.Obj}(f : || Cone/D.Hom C L ||)
                  → f Cone/D.~ unv-ar C
      unv-uq {C} f = eql.uq (dom.π-jm (cone→span C)
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
        { _|[_] = unv-ar
        ; tr = unv-tr
        ; uq = unv-uq
        }
        where open is-lim→is-eql islim

    lim-of→eql-of : ℂ.limit-of D → ℂ.equaliser-of ar₁ ar₂
    lim-of→eql-of lim = record
      { ar = cone→eqlar lim.cone
      ; eq = cone→eqleq lim.cone
      ; iseql = is-lim→is-eql lim.islim
      }
      where module lim = ℂ.limit-of lim

    eql-of→lim-of : ℂ.equaliser-of ar₁ ar₂ → ℂ.limit-of D
    eql-of→lim-of eql = record
      { cone = eqleq→cone eql.eq
      ; islim = is-eql→is-lim eql.iseql
      }
      where module eql = ℂ.equaliser-of eql
  --- end limit-as-eql
  
-- end small-limit-props


lim→prod :  {ℓₒ ℓₐ ℓ~ : Level}{ℂ : ecategoryₗₑᵥ ℓₒ ℓₐ ℓ~}
                → has-small-limits ℂ → has-small-products ℂ
lim→prod {ℂ = ℂ} limℂ = record
  { prd-of = λ {I} D → lim-of→prod-of D (lim-of (disc-ecat-lift-efctr ℂ D))
  }
  where open small-limit-defs ℂ
        open small-limit-props ℂ
        open small-prod-is-small-limit
        open has-small-limits limℂ using (lim-of)
        
