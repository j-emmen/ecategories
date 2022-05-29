 
-- disable the K axiom:

{-# OPTIONS --without-K #-}

-- Agda version 2.5.4.1

module ecats.basic-defs.eqv-rel where

open import ecats.basic-defs.ecat-def&not
open import ecats.basic-defs.commut-shapes
open import ecats.basic-defs.isomorphism
open import ecats.basic-defs.epi&mono
open import ecats.basic-defs.kernel-pair
open import ecats.finite-limits.d&n-pullback
open import ecats.finite-limits.d&n-weak-pullback
open import ecats.finite-limits.defs.pullback-is-weak
open import ecats.finite-limits.d&n-bin-weak-product
open import ecats.finite-limits.d&n-bin-product
open import ecats.finite-limits.defs.bow
open import ecats.finite-limits.props.pullback



-- Pseudo equivalence relations


module pseudo-eq-rel-defs (ℂ : ecategory) where
  open ecategory-aux ℂ
  open comm-shapes ℂ
  open weak-kernel-pairs-defs ℂ
  open wpullback-squares ℂ
  open pullback→weak-pullback ℂ
  open pullback-squares ℂ
  open pullback-props ℂ
  open binary-wproducts ℂ
  open binary-products ℂ

  record is-reflexive {Hi Lo : Obj} (psr₁ psr₂ : || Hom Hi Lo ||) : Set₁ where
    field
      ρ : || Hom Lo Hi ||
      ρ-ax₀ : psr₁ ∘ ρ  ~ idar Lo
      ρ-ax₁ : psr₂ ∘ ρ  ~ idar Lo
    ρ-ax₀g : {X : Obj} {f : || Hom X Lo ||} → psr₁ ∘ ρ ∘ f ~ f
    ρ-ax₀g = ass ⊙ lidgg r ρ-ax₀
    ρ-ax₁g : {X : Obj} {f : || Hom X Lo ||} → psr₂ ∘ ρ ∘ f ~ f
    ρ-ax₁g = ass ⊙ lidgg r ρ-ax₁

  record is-symmetric {Hi Lo : Obj} (psr₁ psr₂ : || Hom Hi Lo ||) : Set₁ where
    field
      σ : || Hom Hi Hi ||
      σ-ax₀ : psr₁ ∘ σ  ~ psr₂
      σ-ax₁ : psr₂ ∘ σ  ~ psr₁
    σ-ax₀g : {X : Obj} {f : || Hom X Hi ||} → psr₁ ∘ σ ∘ f ~ psr₂ ∘ f
    σ-ax₀g = ass ⊙ ∘e r σ-ax₀
    σ-ax₁g : {X : Obj} {f : || Hom X Hi ||} → psr₂ ∘ σ ∘ f ~ psr₁ ∘ f
    σ-ax₁g = ass ⊙ ∘e r σ-ax₁


  record is-transitive/wpb {Hi Lo : Obj} {psr₁ psr₂ : || Hom Hi Lo ||}
                           (τwpb : wpullback-of psr₂ psr₁) : Set₁
                           where
    private
      module τwpb = wpullback-of-not τwpb
    field
      τ : || Hom τwpb.ul Hi ||
      τ-ax₀ :  psr₁ ∘ τ ~ psr₁ ∘ τwpb.wπ/₁
      τ-ax₁ :  psr₂ ∘ τ ~ psr₂ ∘ τwpb.wπ/₂  
    τ-ax₀g : {X : Obj} {f g : || Hom X Hi ||} {pf : psr₂ ∘ f ~ psr₁ ∘ g}
                → psr₁ ∘ τ ∘ τwpb.w⟨ f , g ⟩[ pf ] ~ psr₁ ∘ f
    τ-ax₀g {pf = pf} = ass ⊙ ∘e r τ-ax₀ ⊙ assˢ ⊙ ∘e (τwpb.w×/tr₁ pf) r
    τ-ax₁g : {X : Obj} {f g : || Hom X Hi ||} {pf : psr₂ ∘ f ~ psr₁ ∘ g}
                → psr₂ ∘ τ ∘ τwpb.w⟨ f , g ⟩[ pf ] ~ psr₂ ∘ g
    τ-ax₁g {pf = pf} = ass ⊙ ∘e r τ-ax₁ ⊙ assˢ ⊙ ∘e (τwpb.w×/tr₂ pf) r


  trans-is-wpb-irrel : {Hi Lo : Obj} {psr₁ psr₂ : || Hom Hi Lo ||}
                       ({τwpb} τwpb' : wpullback-of psr₂ psr₁)
                         → is-transitive/wpb τwpb → is-transitive/wpb τwpb'
  trans-is-wpb-irrel {τwpb = τwpb} τwpb' isτ = record
    { τ = τ ∘ τwpb.w⟨ τwpb'.wπ/₁ , τwpb'.wπ/₂ ⟩[ τwpb'.w×/sqpf ]
    ; τ-ax₀ = τ-ax₀g 
    ; τ-ax₁ = τ-ax₁g
    }
    where open is-transitive/wpb isτ
          module τwpb = wpullback-of-not τwpb
          module τwpb' = wpullback-of-not τwpb'
                           

  record is-wtransitive {Hi Lo : Obj} (psr₁ psr₂ : || Hom Hi Lo ||) : Set₁ where
    field
      τwpb : wpullback-of psr₂ psr₁
      isτ : is-transitive/wpb τwpb
    open is-transitive/wpb isτ public


  record is-peq-rel {Hi Lo : Obj} (psr₁ psr₂ : || Hom Hi Lo ||) : Set₁ where
    -- constructor mkis-peqr
    field
      isρ : is-reflexive psr₁ psr₂
      isσ : is-symmetric psr₁ psr₂
      τwpb : wpullback-of psr₂ psr₁
      iswτ : is-transitive/wpb τwpb
    open is-reflexive isρ public
    open is-symmetric isσ public
    open is-transitive/wpb iswτ public
    

  record peqOver (Lo : Obj) : Set₁ where
    -- constructor mkpeq/
    field
       Hi : Obj
       %0 :  || Hom Hi Lo ||
       %1 :  || Hom Hi Lo ||
       ispeq : is-peq-rel %0 %1
    open is-peq-rel ispeq public
    sp/ : span/ Lo Lo
    sp/ = mkspan/ %0 %1


  record peq : Set₁ where
    constructor mkpeq-c
    field
      {Lo} : Obj
      peqover : peqOver Lo
    open peqOver peqover public


  mkpeq : {Lo Hi : Obj} {%0 %1 : || Hom Hi Lo ||} → is-peq-rel %0 %1 → peq
  mkpeq {Lo} {Hi} {%0} {%1} ispeq = record
    { Lo = Lo
    ; peqover = record
              { Hi = Hi
              ; %0 = %0
              ; %1 = %1
              ; ispeq = ispeq
              }
    }


  record is-extensional-ar (R S : peq) (lo : || Hom (peq.Lo R) (peq.Lo S) ||) : Set where
    open peq
    field
      hi : || Hom (Hi R)  (Hi S) ||
      cmptb₀ :  %0 S ∘ hi ~ lo ∘ %0 R
      cmptb₁ :  %1 S ∘ hi ~ lo ∘ %1 R
    cmptb₀g : {X : Obj} {k : || Hom X (Hi R) ||} → %0 S ∘ hi ∘ k ~ lo ∘ %0 R ∘ k
    cmptb₀g = ass ⊙ ∘e r cmptb₀ ⊙ assˢ
    cmptb₁g : {X : Obj} {k : || Hom X (Hi R) ||} → %1 S ∘ hi ∘ k ~ lo ∘ %1 R ∘ k
    cmptb₁g = ass ⊙ ∘e r cmptb₁ ⊙ assˢ


  record peq-mor (R S : peq) : Set where
    -- constructor mkpeq-mor
    open peq
    field
      lo : || Hom (Lo R)  (Lo S) ||
      isext : is-extensional-ar R S lo
    open is-extensional-ar isext public
      

  record peq-mor-eq {R S : peq} (f g : peq-mor R S) : Set where
    -- constructor mkper-mor-eq
    open peq
    open peq-mor
    field
      hty : || Hom (Lo R) (Hi S) ||
      hty₀ : %0 S ∘ hty ~ lo f
      hty₁ : %1 S ∘ hty ~ lo g
    hty₀g : {X : Obj} {k : || Hom X (Lo R) ||} → %0 S ∘ hty ∘ k ~ lo f ∘ k
    hty₀g = ass ⊙ ∘e r hty₀
    hty₁g : {X : Obj} {k : || Hom X (Lo R) ||} → %1 S ∘ hty ∘ k ~ lo g ∘ k
    hty₁g = ass ⊙ ∘e r hty₁


  peq-mor-eq-ext : {R S : peq} {f g : peq-mor R S}
                      → peq-mor.lo f ~ peq-mor.lo g →  peq-mor-eq f g
  peq-mor-eq-ext {R} {S} {f} {g} pf = record
    { hty = S.ρ ∘ f.lo
    ; hty₀ = ass ⊙ ∘e r S.ρ-ax₀ ⊙ lid
    ; hty₁ = ass ⊙ ∘e r S.ρ-ax₁ ⊙ lidgen pf
    }
    where module S = peq S
          module f = peq-mor f


  -- Some canonical peq
  
  module Canpeq where
    open peq
    open peq-mor

    freepeq : Obj → peq
    freepeq X = record
      { Lo = X
      ; peqover = record
        { Hi = X
        ; %0 = idar X
        ; %1 = idar X
        ; ispeq = record
          { isρ = record
                { ρ = idar X
                ; ρ-ax₀ = rid
                ; ρ-ax₁ = lid
                }
          ; isσ = record
                { σ = idar X
                ; σ-ax₀ = rid
                ; σ-ax₁ = lid
                }
          ; τwpb = τwpbX
          ; iswτ = record
                 { τ = idar X
                 ; τ-ax₀ = r
                 ; τ-ax₁ = r
                 }
          }
        }
      }
      where τwpbX : wpullback-of (idar X) (idar X)
            τwpbX = record
              { w×/sq/ = mksq/ (lidgen (ridˢ {f = idar X}))
              ; w×/iswpbsq = is-pb⇒is-wpb (triv-pbsq (idar X))
              }


    cofreepeq-from-wprd+wpb : has-bin-weak-products ℂ → has-weak-pullbacks ℂ
                                → Obj → peq
    cofreepeq-from-wprd+wpb haswprd haswpb X = record
      { Lo = X
      ; peqover = record
        { Hi = X×X.O12
        ; %0 = X×X.wπ₁
        ; %1 = X×X.wπ₂
        ; ispeq = record
                { isρ = record
                      { ρ = X×X.wΔ
                      ; ρ-ax₀ = X×X.w×tr₁
                      ; ρ-ax₁ = X×X.w×tr₂
                      }
                ; isσ = record
                      { σ = X×X.w< X×X.wπ₂ , X×X.wπ₁ >
                      ; σ-ax₀ = X×X.w×tr₁
                      ; σ-ax₁ = X×X.w×tr₂
                      }
                ; τwpb = τwpbX
                ; iswτ = record
                       { τ = X×X.w< X×X.wπ₁ ∘ τwpbX.wπ/₁ , X×X.wπ₂ ∘ τwpbX.wπ/₂ >
                       ; τ-ax₀ = X×X.w×tr₁
                       ; τ-ax₁ = X×X.w×tr₂
                       }
                }
        }
      }
      where open has-bin-weak-products haswprd using (wprd-of)
            open has-weak-pullbacks haswpb using (wpb-of)
            X×X : wproduct-of X X
            X×X = wprd-of X X
            module X×X where
              open wproduct-of X×X public
              open wprod-Δ X×X public
            τwpbX : wpullback-of X×X.wπ₂ X×X.wπ₁
            τwpbX = wpb-of X×X.wπ₂ X×X.wπ₁
            module τwpbX = wpullback-of τwpbX


    cofreepeq-from-prd : has-bin-products ℂ → Obj → peq
    cofreepeq-from-prd hasprd X = record
      { Lo = X
      ; peqover = record
        { Hi = X×X.O12
        ; %0 = X×X.π₁
        ; %1 = X×X.π₂
        ; ispeq = record
                { isρ = record
                      { ρ = X×X.Δ
                      ; ρ-ax₀ = X×X.×tr₁
                      ; ρ-ax₁ = X×X.×tr₂
                      }
                ; isσ = record
                      { σ = X×X.< X×X.π₂ , X×X.π₁ >
                      ; σ-ax₀ = X×X.×tr₁
                      ; σ-ax₁ = X×X.×tr₂
                      }
                ; τwpb = pbof⇒wpbof X×X×X.×/of
                ; iswτ = record
                       { τ = X×X.< X×X.π₁ ∘ X×X×X.π₁ , X×X×X.π₂ >
                       ; τ-ax₀ = X×X.×tr₁
                       ; τ-ax₁ = X×X.×tr₂ ⊙ lidˢ ⊙ X×X.×tr₂ˢ
                       }
                }
        }
      }
      where open has-bin-products hasprd
            X×X : product-of X X
            X×X = prd-of X X
            module X×X where
              open product-of-not X×X public
              open prod-Δ X×X public
            X×X×X : product-of X×X.O12 X
            X×X×X = prd-of X×X.O12 X
            module X×X×X where
              private
                module pbprd = pullback-sq-not (pb-alng-π₁ X×X.π₂ X×X×X X×X)
              open product-of-not X×X×X public
              open pullback-of-not pbprd.×/of public


    freepeq-is-min : {X : Obj} (R : peq) → || Hom X (Lo R) || → peq-mor (freepeq X) R
    freepeq-is-min R f = record
      { lo = f
      ; isext = record
        { hi = ρ R ∘ f
        ; cmptb₀ = ass ⊙ lidgg ridˢ (ρ-ax₀ R)
        ; cmptb₁ = ass ⊙ lidgg ridˢ (ρ-ax₁ R)
        }
      }

    freepeq-mor : {A B : Obj} → || Hom A B || → peq-mor (freepeq A) (freepeq B)
    freepeq-mor {A} {B} f = freepeq-is-min (freepeq B) f
    -- with this definition lo = idar B ∘ f, but more useful later on when dealing with canonical regular epis
{-
record { hi = f ; lo = f ; cmptb₀ = lid f ⊙ ridˢ f ; cmptb₁ = lid f ⊙ ridˢ f }
-}


    freepeq-min-eq : {X : Obj} (R : peq) {f f' : || Hom X (Lo R) ||} {h : || Hom X (Hi R) ||}
                        → %0 R ∘ h ~ f → %1 R ∘ h ~ f'
                          → peq-mor-eq (freepeq-is-min R f) (freepeq-is-min R f')
    freepeq-min-eq R {h = h} pf0 pf1 = record
      { hty = h
      ; hty₀ = pf0
      ; hty₁ = pf1
      }


    freepeq-min-min-eq : {X : Obj} (R : peq) {f f' : || Hom X (Lo R) ||} → f ~ f'
                          → peq-mor-eq (freepeq-is-min R f) (freepeq-is-min R f')
    freepeq-min-min-eq R {f} {f'} pf = freepeq-min-eq R {h = ρ R ∘ f} (ρ-ax₀g R) (ρ-ax₁g R ⊙ pf)


  --end module Canpeq
  open Canpeq public



  module peq&prods (prd : has-bin-products ℂ) where
    open bin-products-aux prd

    module peqOver-aux {Lo : Obj} (R : peqOver Lo) where
      open peqOver R public
      open wpullback-of τwpb
      %01 : || Hom Hi (Lo × Lo) ||
      %01 = < %0 , %1 >
      ρ-ax : %01 ∘ ρ ~ Δ Lo
      ρ-ax = <>ar~<> ρ-ax₀ ρ-ax₁
      σ-ax : %01 ∘ σ ~ < %1 , %0 >
      σ-ax = <>ar~<> σ-ax₀ σ-ax₁
      τ-ax : %01 ∘ τ ~ < %0 ∘ wπ/₁ , %1 ∘ wπ/₂ >
      τ-ax = <>ar~<> τ-ax₀ τ-ax₁


    module peq-aux (R : peq) where
      open peqOver-aux (peq.peqover R) public
      Lo : Obj
      Lo = peq.Lo R
      peqover : peqOver Lo
      peqover = peq.peqover R


    module peq-mor-aux {R S : peq} (f : peq-mor R S) where
      open peq-aux
      open peq-mor f public
      cmptb : %01 S ∘ hi ~ lo ×ₐ lo ∘ %01 R
      cmptb = <>ar~ar (ass ⊙ ∘e r ×tr₁ ⊙ assˢ ⊙ ∘e ×tr₁ r ⊙ cmptb₀ ˢ)
                        (ass ⊙ ∘e r ×tr₂ ⊙ assˢ ⊙ ∘e ×tr₂ r ⊙ cmptb₁ ˢ)


    module peq-mor-eq-aux {R  S : peq} {f g : peq-mor R S} (h : peq-mor-eq f g) where
      open peq-aux
      open peq-mor-aux
      open peq-mor-eq h public
      hty-ax : %01 S ∘ hty ~ < lo f , lo g >
      hty-ax = <>ar~<> hty₀ hty₁

  -- end peq&prods


  is-wkerp+τpb→is-peqr :  {A K : Obj} {wkp₁ wkp₂ : || Hom K A ||}
                             → is-wkernel-pair wkp₁ wkp₂ → wpullback-of wkp₂ wkp₁
                               → is-peq-rel wkp₁ wkp₂
  is-wkerp+τpb→is-peqr {A} {K} {wkp₁} {wkp₂} iswkp τwpb = record
    { isρ = record
          { ρ = wkp.w⟨ idar A , idar A ⟩[ r ]
          ; ρ-ax₀ = wkp.w×/tr₁ r
          ; ρ-ax₁ = wkp.w×/tr₂ r
          }
    ; isσ = record
          { σ = wkp.w⟨ wkp₂ , wkp₁ ⟩[ wkp.sqpf ˢ ]
          ; σ-ax₀ = wkp.w×/tr₁ (wkp.sqpf ˢ)
          ; σ-ax₁ = wkp.w×/tr₂ (wkp.sqpf ˢ)
          }
    ; τwpb = τwpb
    ; iswτ = record
           { τ = wkp.w⟨ wkp₁ ∘ τwpb.wπ/₁ , wkp₂ ∘ τwpb.wπ/₂ ⟩[ τpf ]
           ; τ-ax₀ = wkp.w×/tr₁ τpf
           ; τ-ax₁ = wkp.w×/tr₂ τpf
           }
    }
    where module wkp = is-wkernel-pair iswkp
          module τwpb = wpullback-of-not τwpb
          τpf = ~proof wkp.ar ∘ wkp₁ ∘ τwpb.wπ/₁ ~[ ass ⊙ ∘e r wkp.sqpf ⊙ assˢ ] /
                       wkp.ar ∘ wkp₂ ∘ τwpb.wπ/₁ ~[ ∘e τwpb.w×/sqpf r ] /
                       wkp.ar ∘ wkp₁ ∘ τwpb.wπ/₂ ~[ ass ⊙ ∘e r wkp.sqpf ⊙ assˢ ]∎
                       wkp.ar ∘ wkp₂ ∘ τwpb.wπ/₂ ∎

  is-wkerpsp+τpb→is-peqr :  {A K : Obj} {wkp₁ wkp₂ : || Hom K A ||}
                             → is-wkernel-pair-sp wkp₁ wkp₂ → wpullback-of wkp₂ wkp₁
                               → is-peq-rel wkp₁ wkp₂
  is-wkerpsp+τpb→is-peqr {A} {K} {wkp₁} {wkp₂} iswkpsp τwpb = record
    { isρ = record
          { ρ = wkp.⟨ idar A , idar A ⟩[ r , r ]
          ; ρ-ax₀ = wkp.tr₁ r r
          ; ρ-ax₁ = wkp.tr₂ r r
          }
    ; isσ = record
          { σ = wkp.⟨ wkp₂ , wkp₁ ⟩[ wkp.sqpf₁ ˢ , wkp.sqpf₂ ˢ ]
          ; σ-ax₀ = wkp.tr₁ (wkp.sqpf₁ ˢ) (wkp.sqpf₂ ˢ)
          ; σ-ax₁ = wkp.tr₂ (wkp.sqpf₁ ˢ) (wkp.sqpf₂ ˢ)
          }
    ; τwpb = τwpb
    ; iswτ = record
           { τ = wkp.⟨ wkp₁ ∘ τwpb.wπ/₁ , wkp₂ ∘ τwpb.wπ/₂ ⟩[ τpf₁ , τpf₂ ]
           ; τ-ax₀ = wkp.tr₁ τpf₁ τpf₂
           ; τ-ax₁ = wkp.tr₂ τpf₁ τpf₂
           }
    }
    where module wkp = is-wkernel-pair-sp iswkpsp
          module τwpb = wpullback-of-not τwpb
          τpf₁ = ~proof wkp.a1 ∘ wkp₁ ∘ τwpb.wπ/₁   ~[ ass ⊙ ∘e r wkp.sqpf₁ ⊙ assˢ ] /
                        wkp.a1 ∘ wkp₂ ∘ τwpb.wπ/₁   ~[ ∘e τwpb.w×/sqpf r ] /
                        wkp.a1 ∘ wkp₁ ∘ τwpb.wπ/₂   ~[ ass ⊙ ∘e r wkp.sqpf₁ ⊙ assˢ ]∎
                        wkp.a1 ∘ wkp₂ ∘ τwpb.wπ/₂ ∎
          τpf₂ = ~proof wkp.a2 ∘ wkp₁ ∘ τwpb.wπ/₁   ~[ ass ⊙ ∘e r wkp.sqpf₂ ⊙ assˢ ] /
                        wkp.a2 ∘ wkp₂ ∘ τwpb.wπ/₁   ~[ ∘e τwpb.w×/sqpf r ] /
                        wkp.a2 ∘ wkp₁ ∘ τwpb.wπ/₂   ~[ ass ⊙ ∘e r wkp.sqpf₂ ⊙ assˢ ]∎
                        wkp.a2 ∘ wkp₂ ∘ τwpb.wπ/₂ ∎


  module has-wpb→wker-are-peq (haswpb : has-weak-pullbacks ℂ) where
    open has-weak-pullbacks haswpb using (wpb-of)
    private
      module wpb {A B : Obj} (f : || Hom A B ||) = wpullback-of-not (wpb-of f f)
    open has-wpb→has-wkerpair haswpb
    
    wπ/-peq/ : {A B : Obj} (f : || Hom A B ||) → peqOver A
    wπ/-peq/ f = record
      { Hi = wpb.ul f
      ; %0 = wpb.wπ/₁ f
      ; %1 = wpb.wπ/₂ f
      ; ispeq = is-wkerp+τpb→is-peqr (wπ/iswkp f) (wpb-of (wpb.wπ/₂ f) (wpb.wπ/₁ f))
      }
                          
    wπ/-peq : {A B : Obj} (f : || Hom A B ||) → peq
    wπ/-peq f = mkpeq-c (wπ/-peq/ f)
  -- end has-wpb→wker-are-peq

-- end pseudo-eq-rel-defs






-- Equivalence relations

module eq-rel-defs (ℂ : ecategory) where
  open ecategory-aux ℂ
  open comm-shapes ℂ
  open kernel-pairs-defs ℂ
  open pullback-squares ℂ
  open pullback-props ℂ
  open bow-defs ℂ
  open binary-products ℂ
  open pseudo-eq-rel-defs ℂ
  open epis&monos-defs ℂ


  record is-transitive/pb {Hi Lo : Obj} {r₁ r₂ : || Hom Hi Lo ||} (τpb : pullback-of r₂ r₁) : Set₁
                          where
    private
      module τpb = pullback-of τpb
    field
      τ : || Hom τpb.ul Hi ||
      τ-ax₀ :  r₁ ∘ τ ~ r₁ ∘ τpb.π/₁
      τ-ax₁ :  r₂ ∘ τ ~ r₂ ∘ τpb.π/₂  
    τ-ax₀g : {X : Obj} {f g : || Hom X Hi ||} {pf : r₂ ∘ f ~ r₁ ∘ g}
                → r₁ ∘ τ ∘ τpb.⟨ f , g ⟩[ pf ] ~ r₁ ∘ f
    τ-ax₀g {pf = pf} = ass ⊙ ∘e r τ-ax₀ ⊙ assˢ ⊙ ∘e (τpb.×/tr₁ pf) r
    τ-ax₁g : {X : Obj} {f g : || Hom X Hi ||} {pf : r₂ ∘ f ~ r₁ ∘ g}
                → r₂ ∘ τ ∘ τpb.⟨ f , g ⟩[ pf ] ~ r₂ ∘ g
    τ-ax₁g {pf = pf} = ass ⊙ ∘e r τ-ax₁ ⊙ assˢ ⊙ ∘e (τpb.×/tr₂ pf) r


  trans-is-pb-irrel : {Hi Lo : Obj} {r₁ r₂ : || Hom Hi Lo ||}
                      ({τpb} τpb' : pullback-of r₂ r₁)
                         → is-transitive/pb τpb → is-transitive/pb τpb'
  trans-is-pb-irrel {τpb = τpb} τpb' isτ = record
    { τ = τ ∘ τpb.⟨ τpb'.π/₁ , τpb'.π/₂ ⟩[ τpb'.×/sqpf ]
    ; τ-ax₀ = τ-ax₀g 
    ; τ-ax₁ = τ-ax₁g
    }
    where open is-transitive/pb isτ
          module τpb = pullback-of-not τpb
          module τpb' = pullback-of-not τpb'
                           

  record is-transitive {Hi Lo : Obj} (r₁ r₂ : || Hom Hi Lo ||) : Set₁ where
    field
      τpb : pullback-of r₂ r₁
      isτ : is-transitive/pb τpb
    open is-transitive/pb isτ public


  record is-eq-rel {R A : Obj} (r₁ r₂ : || Hom R A ||) : Set₁ where
    -- constructor mkis-eqr
    field
      isjm/ : is-jointly-monic/ (mkspan/ r₁ r₂)
      isρ : is-reflexive r₁ r₂
      isσ : is-symmetric r₁ r₂
      τpb : pullback-of r₂ r₁
      isτ : is-transitive/pb τpb
    open is-jointly-monic/ isjm/ public
    open is-reflexive isρ public
    open is-symmetric isσ public
    open is-transitive/pb isτ public


  record eqrel-over (A : Obj)  : Set₁ where
    field
      {relOb} : Obj
      {r₁ r₂} : || Hom relOb A ||
      iseqrel : is-eq-rel r₁ r₂
    open is-eq-rel iseqrel public
    sp/ : span/ A A
    sp/ = mkspan/ r₁ r₂


  record eqrel : Set₁ where
    field
      {baseOb} : Obj
      eqrelover : eqrel-over baseOb
    open eqrel-over eqrelover public


  record is-eqrel-ext-ar (R S : eqrel)
                         (base-ar : || Hom (eqrel.baseOb R) (eqrel.baseOb S) ||) : Set
                         where
    open eqrel
    field
      rel-ar : || Hom (relOb R)  (relOb S) ||
      cmptb₀ :  r₁ S ∘ rel-ar ~ base-ar ∘ r₁ R
      cmptb₁ :  r₂ S ∘ rel-ar ~ base-ar ∘ r₂ R
    cmptb₀g : {X : Obj} {k : || Hom X (relOb R) ||} → r₁ S ∘ rel-ar ∘ k ~ base-ar ∘ r₁ R ∘ k
    cmptb₀g = ass ⊙ ∘e r cmptb₀ ⊙ assˢ
    cmptb₁g : {X : Obj} {k : || Hom X (relOb R) ||} → r₂ S ∘ rel-ar ∘ k ~ base-ar ∘ r₂ R ∘ k
    cmptb₁g = ass ⊙ ∘e r cmptb₁ ⊙ assˢ

  record eqrel-mor (R S : eqrel) : Set where
    -- constructor mkpeq-mor
    open eqrel
    field
      base-ar : || Hom (baseOb R)  (baseOb S) ||
      isext : is-eqrel-ext-ar R S base-ar
    open is-eqrel-ext-ar isext public


  record eqrel-mor-eq {R S : eqrel} (f g : eqrel-mor R S) : Set where
    -- constructor mkper-mor-eq
    open eqrel
    open eqrel-mor
    field
      wit : || Hom (baseOb R) (relOb S) ||
      wit₀ : r₁ S ∘ wit ~ base-ar f
      wit₁ : r₂ S ∘ wit ~ base-ar g
    wit₀g : {X : Obj} {k : || Hom X (baseOb R) ||} → r₁ S ∘ wit ∘ k ~ base-ar f ∘ k
    wit₀g = ass ⊙ ∘e r wit₀
    wit₁g : {X : Obj} {k : || Hom X (baseOb R) ||} → r₂ S ∘ wit ∘ k ~ base-ar g ∘ k
    wit₁g = ass ⊙ ∘e r wit₁


  eqrel-mor-eq-ext : {R S : eqrel} {f g : eqrel-mor R S}
                      → eqrel-mor.base-ar f ~ eqrel-mor.base-ar g →  eqrel-mor-eq f g
  eqrel-mor-eq-ext {R} {S} {f} {g} pf = record
    { wit = S.ρ ∘ f.base-ar
    ; wit₀ = ass ⊙ ∘e r S.ρ-ax₀ ⊙ lid
    ; wit₁ = ass ⊙ ∘e r S.ρ-ax₁ ⊙ lidgen pf
    }
    where module S = eqrel S
          module f = eqrel-mor f

  -- Some canonical eqrel
  
  module Can-eqrel where
    open eqrel
    open eqrel-mor

    free-eqrel : Obj → eqrel
    free-eqrel X = record
      { baseOb = X
      ; eqrelover = record
        { relOb = X
        ; r₁ = idar X
        ; r₂ = idar X
        ; iseqrel = record
          { isjm/ = record { jm-pf = λ x _ → lidˢ ⊙ x ⊙ lid }
          ; isρ = record
                { ρ = idar X
                ; ρ-ax₀ = rid
                ; ρ-ax₁ = lid
                }
          ; isσ = record
                { σ = idar X
                ; σ-ax₀ = rid
                ; σ-ax₁ = lid
                }
          ; τpb = τpbX
          ; isτ = record
                 { τ = idar X
                 ; τ-ax₀ = r
                 ; τ-ax₁ = r
                 }
          }
        }
      }
      where τpbX : pullback-of (idar X) (idar X)
            τpbX = record
              { ×/sq/ = mksq/ (lidgen (ridˢ {f = idar X}))
              ; ×/ispbsq = triv-pbsq (idar X)
              }

    free-eqrel-is-min : {X : Obj} (R : eqrel)
                           → || Hom X (baseOb R) || → eqrel-mor (free-eqrel X) R
    free-eqrel-is-min R f = record
      { base-ar = f
      ; isext = record
        { rel-ar = ρ R ∘ f
        ; cmptb₀ = ass ⊙ lidgg ridˢ (ρ-ax₀ R)
        ; cmptb₁ = ass ⊙ lidgg ridˢ (ρ-ax₁ R)
        }
      }

    free-eqrel-mor : {A B : Obj} → || Hom A B || → eqrel-mor (free-eqrel A) (free-eqrel B)
    free-eqrel-mor {A} {B} f = free-eqrel-is-min (free-eqrel B) f
    -- with this definition base-ar = idar B ∘ f, but more useful later on when dealing with canonical regular epis
{-
record { rel-ar = f ; base-ar = f ; cmptb₀ = lid f ⊙ ridˢ f ; cmptb₁ = lid f ⊙ ridˢ f }
-}

{-
    free-eqrel-min-eq : {X : Obj} (R : eqrel) {f f' : || Hom X (baseOb R) ||} {h : || Hom X (relOb R) ||}
                        → r₁ R ∘ h ~ f → r₂ R ∘ h ~ f'
                          → eqrel-mor.base-ar (free-eqrel-is-min R f) ~ eqrel-mor.base-ar (free-eqrel-is-min R f')
    free-eqrel-min-eq R {h = h} pf0 pf1 = {!jm-pf R !}
                                        --where open is-jointly-monic/ (isjm/ R)
    
    free-eqrel-min-min-eq : {X : Obj} (R : eqrel) {f f' : || Hom X (baseOb R) ||} → f ~ f'
                          → eqrel-mor.base-ar (free-eqrel-is-min R f) ~ eqrel-mor.base-ar (free-eqrel-is-min R f')
    free-eqrel-min-min-eq R {f} {f'} pf = free-eqrel-min-eq R {h = ρ R ∘ f} (ρ-ax₀g R) (ρ-ax₁g R ⊙ pf)
-}

{-
    cofree-eqrel-from-wprd+wpb : has-bin-products ℂ → has-pullbacks ℂ
                                → Obj → eqrel
    cofree-eqrel-from-wprd+wpb hasprd haspb X = record
      { baseOb = X
      ; eqrelover = record
        { relOb = X×X.O12
        ; r₁ = X×X.π₁
        ; r₂ = X×X.π₂
        ; iseqrel = record
                { isjm/ = record { jm-pf = X×X.×uq }
                ; isρ = record
                      { ρ = X×X.Δ
                      ; ρ-ax₀ = X×X.×tr₁
                      ; ρ-ax₁ = X×X.×tr₂
                      }
                ; isσ = record
                      { σ = X×X.< X×X.π₂ , X×X.π₁ >
                      ; σ-ax₀ = X×X.×tr₁
                      ; σ-ax₁ = X×X.×tr₂
                      }
                ; τpb = τpbX
                ; isτ = record
                       { τ = X×X.< X×X.π₁ ∘ τpbX.π/₁ , X×X.π₂ ∘ τpbX.π/₂ >
                       ; τ-ax₀ = X×X.×tr₁
                       ; τ-ax₁ = X×X.×tr₂
                       }
                }
        }
      }
      where open has-bin-products hasprd using (prd-of)
            open has-pullbacks haspb using (pb-of)
            X×X : product-of X X
            X×X = prd-of X X
            module X×X where
              open product-of X×X public
              open prod-Δ X×X public
            τpbX : pullback-of X×X.π₂ X×X.π₁
            τpbX = pb-of X×X.π₂ X×X.π₁
            module τpbX = pullback-of τpbX
-}

    cofree-eqrel-from-prd : has-bin-products ℂ → Obj → eqrel
    cofree-eqrel-from-prd hasprd X = record
      { baseOb = X
      ; eqrelover = record
        { relOb = X×X.O12
        ; r₁ = X×X.π₁
        ; r₂ = X×X.π₂
        ; iseqrel = record
                { isjm/ = record { jm-pf = X×X.×uq }
                ; isρ = record
                      { ρ = X×X.Δ
                      ; ρ-ax₀ = X×X.×tr₁
                      ; ρ-ax₁ = X×X.×tr₂
                      }
                ; isσ = record
                      { σ = X×X.< X×X.π₂ , X×X.π₁ >
                      ; σ-ax₀ = X×X.×tr₁
                      ; σ-ax₁ = X×X.×tr₂
                      }
                ; τpb = X×X×X.×/of
                ; isτ = record
                       { τ = X×X.< X×X.π₁ ∘ X×X×X.π₁ , X×X×X.π₂ >
                       ; τ-ax₀ = X×X.×tr₁
                       ; τ-ax₁ = X×X.×tr₂ ⊙ lidˢ ⊙ X×X.×tr₂ˢ
                       }
                }
        }
      }
      where open has-bin-products hasprd
            X×X : product-of X X
            X×X = prd-of X X
            module X×X where
              open product-of-not X×X public
              open prod-Δ X×X public
            X×X×X : product-of X×X.O12 X
            X×X×X = prd-of X×X.O12 X
            module X×X×X where
              private
                module pbprd = pullback-sq-not (pb-alng-π₁ X×X.π₂ X×X×X X×X)
              open product-of-not X×X×X public
              open pullback-of-not pbprd.×/of public
  --end module Can-eqrel
  open Can-eqrel public


  is-kerp+τpb→is-eqr : {A K : Obj} {kp₁ kp₂ : || Hom K A ||}
                            → is-kernel-pair kp₁ kp₂ → pullback-of kp₂ kp₁
                              → is-eq-rel kp₁ kp₂
  is-kerp+τpb→is-eqr {A} {kp₁ = kp₁} {kp₂} iskp pbof = record
    { isjm/ = record
            { jm-pf = kp.×/uq
            }
    ; isρ = record
          { ρ = kp.⟨ idar A , idar A ⟩[ r ]
          ; ρ-ax₀ = kp.×/tr₁ r
          ; ρ-ax₁ = kp.×/tr₂ r
          }
    ; isσ = record
          { σ = kp.⟨ kp₂ , kp₁ ⟩[ kp.×/sqpf ˢ ]
          ; σ-ax₀ = kp.×/tr₁ (kp.×/sqpf ˢ)
          ; σ-ax₁ = kp.×/tr₂ (kp.×/sqpf ˢ)
          }
    ; τpb = pbof
    ; isτ = record
          { τ = kp.⟨ kp₁ ∘ τpbkp.π/₁ , kp₂ ∘ τpbkp.π/₂ ⟩[ τpf ]
          ; τ-ax₀ = kp.×/tr₁ τpf
          ; τ-ax₁ = kp.×/tr₂ τpf
          }
    }
    where module kp = is-kernel-pair iskp
          module τpbkp = pullback-of-not pbof
          τpf = ~proof kp.ar ∘ kp₁ ∘ τpbkp.π/₁     ~[ ass ⊙ ∘e r kp.×/sqpf ⊙ assˢ ] /
                       kp.ar ∘ kp₂ ∘ τpbkp.π/₁     ~[ ∘e τpbkp.×/sqpf r ] /
                       kp.ar ∘ kp₁ ∘ τpbkp.π/₂     ~[ ass ⊙ ∘e r kp.×/sqpf ⊙ assˢ ]∎
                       kp.ar ∘ kp₂ ∘ τpbkp.π/₂ ∎


  module has-pb→ker-are-eqr (haspb : has-pullbacks ℂ) where
    open has-pullbacks haspb using (pb-of)
    open has-pb→has-kerpair haspb
    private
      module kpf {A B : Obj} (f : || Hom A B ||) = pullback-of-not (kp-of f)
      
    is-kp→is-eqr : {A K : Obj} {kp₁ kp₂ : || Hom K A ||}
                        → is-kernel-pair kp₁ kp₂ → is-eq-rel kp₁ kp₂
    is-kp→is-eqr {kp₁ = kp₁} {kp₂} iskp =
      is-kerp+τpb→is-eqr iskp (pb-of kp₂ kp₁)

    π/kp-eqr/ : {A B : Obj} (f : || Hom A B ||) → eqrel-over A
    π/kp-eqr/ f = record
      { iseqrel = is-kerp+τpb→is-eqr (π/iskp f) (pb-of (kpf.π/₂ f) (kpf.π/₁ f))
      }
    -- end has-pb→ker-are-eqr


  private
    module bw = bow-of
  is-kerp₂+τpb→is-eqr : {DL DR : Obj} {sp/ : span/ DL DR} (bwsp : bow-of sp/ sp/)
                            → pullback-of (bw.π//₂ bwsp) (bw.π//₁ bwsp)
                              → is-eq-rel (bw.π//₁ bwsp) (bw.π//₂ bwsp)
  is-kerp₂+τpb→is-eqr {DL} {DR} {sp/} bwsp pbof = record
    { isjm/ = record
            { jm-pf = kp₂.uq
            }
    ; isρ = record
          { ρ = kp₂.⟨ idar sp.O12 , idar sp.O12 ⟩[ r , r ]
          ; ρ-ax₀ = kp₂.tr₁ r r
          ; ρ-ax₁ = kp₂.tr₂ r r
          }
    ; isσ = record
          { σ = kp₂.⟨ kp₂.π//₂ , kp₂.π//₁ ⟩[ kp₂.sqpf₁ ˢ , kp₂.sqpf₂ ˢ ]
          ; σ-ax₀ = kp₂.tr₁ (kp₂.sqpf₁ ˢ) (kp₂.sqpf₂ ˢ)
          ; σ-ax₁ = kp₂.tr₂ (kp₂.sqpf₁ ˢ) (kp₂.sqpf₂ ˢ)
          }
    ; τpb = pbof
    ; isτ = record
          { τ = kp₂.⟨ kp₂.π//₁ ∘ τpbkp₂.π/₁ , kp₂.π//₂ ∘ τpbkp₂.π/₂ ⟩[ τpf₁ , τpf₂ ]
          ; τ-ax₀ = kp₂.tr₁ τpf₁ τpf₂
          ; τ-ax₁ = kp₂.tr₂ τpf₁ τpf₂
          }
    }
    where module sp = span/ sp/
          module kp₂ = bw bwsp
          module τpbkp₂ = pullback-of-not pbof
          τpf₁ = ~proof sp.a1 ∘ kp₂.π//₁ ∘ τpbkp₂.π/₁     ~[ ass ⊙ ∘e r kp₂.sqpf₁ ⊙ assˢ ] /
                        sp.a1 ∘ kp₂.π//₂ ∘ τpbkp₂.π/₁     ~[ ∘e τpbkp₂.×/sqpf r ] /
                        sp.a1 ∘ kp₂.π//₁ ∘ τpbkp₂.π/₂     ~[ ass ⊙ ∘e r kp₂.sqpf₁ ⊙ assˢ ]∎
                        sp.a1 ∘ kp₂.π//₂ ∘ τpbkp₂.π/₂ ∎
          τpf₂ = ~proof sp.a2 ∘ kp₂.π//₁ ∘ τpbkp₂.π/₁     ~[ ass ⊙ ∘e r kp₂.sqpf₂ ⊙ assˢ ] /
                        sp.a2 ∘ kp₂.π//₂ ∘ τpbkp₂.π/₁     ~[ ∘e τpbkp₂.×/sqpf r ] /
                        sp.a2 ∘ kp₂.π//₁ ∘ τpbkp₂.π/₂     ~[ ass ⊙ ∘e r kp₂.sqpf₂ ⊙ assˢ ]∎
                        sp.a2 ∘ kp₂.π//₂ ∘ τpbkp₂.π/₂ ∎

-- end eq-rels-defs
