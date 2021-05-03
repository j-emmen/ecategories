
{-# OPTIONS --without-K #-}

module ecats.constructions.yoneda where

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
private module Yo {ℂ : ecategory} = efunctorₗₑᵥ {ℂ = ℂ} {PSh ℂ} (Yo ℂ)

module yoneda-props (ℂ : ecategory) where
  open ecategory ℂ
  open representable-presheaf ℂ
  private module Std = ecategory-aux Std
  
  Yo-faith : is-faithful (Yo ℂ)
  Yo-faith = record
    { faith-pf = λ {X} {Y} {f} {g} eq → ridˢ ⊙ eq X (idar X) ⊙ rid
    }
    where open ecategory-aux-only ℂ

  module Lemma (F : presheaf ℂ)(X : Obj) where
      open import tt-basics.setoids using (setoid; setoidmap; std-id; std-cmp; ptw~)
      private
        module [─,X] = presheaf [─, X ]
        module F = presheaf F
        module FX = F.ₒ X

      yo-el : [─, X ] ⇒ F → || F.ₒ X ||
      yo-el μ = μ.ap {X} (idar X)
                  where module μ = psheaf-mor μ

      yo-fnc : (x : || F.ₒ X ||){A : Obj} → || Std.Hom (Hom A X) (F.ₒ A) ||
      yo-fnc x {A} = record
                   { op = λ a → F.ₐ.ap a x
                   ; ext = λ {a} {a'} pfeq → F.ext pfeq x
                   }
                         
      yo-natt : || F.ₒ X || → [─, X ] ⇒ F
      yo-natt x = record
                { fnc = yo-fnc x
                ; nat =  λ f a → F.cmpˢ a f x
                }

      -- Note that (NatTr [─, X ] F) : Set 1ₗₑᵥ, so setoidmap below cannot be replaced by Std.Hom
      natt2el : setoidmap (NatTr [─, X ] F) (F.ₒ X)
      natt2el = record
              { op = yo-el
              ; ext = λ pfeq → pfeq X (idar X)
              }

      el2natt : setoidmap (F.ₒ X) (NatTr [─, X ] F)
      el2natt = record
              { op = yo-natt
              ; ext = λ pfeq A a → F.ₐ.ext a pfeq
              }

      id-el : ptw~ (std-cmp natt2el el2natt) (std-id {A = F.ₒ X})
      id-el x = F.ₐ.ap (idar X) x  ~[ F.id x ]  x ∎
              where open FX using (endpoints)

      id-natt : ptw~ (std-cmp el2natt natt2el) (std-id {A = NatTr [─, X ] F})
      id-natt μ A a = ~proof
                    F.ₐ.ap a (μ.ap (idar X))       ~[ μ.nat a (idar X) ˢ ] /
                    μ.ap (idar X ∘ a)              ~[ μ.ext ℂ.lid ]∎
                    μ.ap {A} a ∎
                    where module μ = psheaf-mor μ
                          module FA = F.ₒ A
                          open FA using (_ˢ; ~proof_~[_]_; eqreasend; /_~[_]_)
                          module ℂ = ecategory-aux-only ℂ                                    
  -- end Lemma

  Yo-full : is-full (Yo ℂ)
  Yo-full = record
    { full-ar = λ {X} {Y} → yo-el [─, Y ] X
    ; full-pf = λ {X} {Y} {μ} → id-natt [─, Y ] X μ
    }
    where open Lemma

  Yo-conserv : is-conservative (Yo ℂ)
  Yo-conserv = f&f-is-conservative Yo-full Yo-faith

-- end yoneda-props
