
{-# OPTIONS --without-K #-}

module ecats.constructions.yoneda where

import tt-basics.setoids
open import ecats.basic-defs.ecat-def&not
open import ecats.functors.defs.efunctor-d&n
open import ecats.functors.defs.basic-defs
open import ecats.functors.defs.natural-transformation
open import ecats.constructions.opposite
open import ecats.constructions.functor-ecat
open import ecats.concr-ecats.Std
open import ecats.constructions.presheaf


Yo : (ℂ : ecategory) → efunctorₗₑᵥ ℂ (PSh ℂ)
Yo ℂ = record
  { FObj = repr-presheaf
  ; FHom = precmp-nat
  ; isF = record
        { ext = λ f~f' X x → ∘e r f~f'
        ; id = λ X x → lid
        ; cmp = λ f g X x → ass
        }
  }
  where open representable-presheaf ℂ
        open ecategory-aux ℂ
module Yo {ℂ : ecategory} = efunctorₗₑᵥ {ℂ = ℂ} {PSh ℂ} (Yo ℂ)

module yoneda-props (ℂ : ecategory) where
  open ecategory ℂ
  open representable-presheaf ℂ
  private module Std = ecategory-aux Std
  
  Yo-faith : is-faithful (Yo ℂ)
  Yo-faith = record
    { faith-pf = λ {X} {Y} {f} {g} eq → ridˢ ⊙ eq X (idar X) ⊙ rid
    }
    where open ecategory-aux-only ℂ

  module nat-tranf-into-repr {X : Obj}{F : presheaf ℂ}(μ : [─, X ] ⇒ F) where
    private
      module X = presheaf [─, X ]
      module F = presheaf F
      module μ = psheaf-mor μ
      module Nat = tt-basics.setoids.setoid-aux (Nat [─, X ] F)

    yoneda-el : || F.ₒ X ||
    yoneda-el = μ.ap {X} (idar X)

    yoneda-el-nat : natural-transformation [─, X ] F
    yoneda-el-nat = record
      { fnc =  fnc
      ; nat = λ f a → F.ₐ.ap (a ∘ f) yoneda-el      ~[ F.∘ax-rfˢ yoneda-el ]
                       F.ₐ.ap f (F.ₐ.ap a yoneda-el)  ∎
      }
      where module tmp {Z : Obj} = tt-basics.setoids.setoid-aux (F.ₒ Z)
            open tmp using (endpoints)
            fnc : {Z : Obj} → || Std.Hom (Hom Z X) (F.ₒ Z) ||
            fnc {Z} = record
              { op = λ z → F.ₐ.ap z yoneda-el
              ; ext = λ pf → F.ext pf yoneda-el
              }
    private module yn = psheaf-mor yoneda-el-nat
            
    yoneda-eq-aux : {Z : Obj} → μ.fnc {Z} Std.~ yn.fnc {Z}
    yoneda-eq-aux {Z} = λ z → ~proof
      μ.ap z                      ~[ μ.ext lidˢ ] /
      μ.ap (X.ₐ.ap z (idar X))    ~[ μ.nat z (idar X) ]∎
      F.ₐ.ap z (μ.ap (idar X)) ∎
                      where open tt-basics.setoids.setoid-aux (F.ₒ Z)
                            open ecategory-aux-only ℂ using (lidˢ)
    
    yoneda-eq : yoneda-el-nat Nat.~ μ
    yoneda-eq = λ Z → Std._ˢ {_} {_} {μ.fnc {Z}} {yn.fnc {Z}} (yoneda-eq-aux {Z})
  -- end nat-tranf-into-repr

  Yo-full : is-full (Yo ℂ)
  Yo-full = record
    { full-ar = yoneda-el
    ; full-pf = λ {X} {Y} {μ} → yoneda-eq μ
    }
    where open nat-tranf-into-repr
-- end yoneda-props
