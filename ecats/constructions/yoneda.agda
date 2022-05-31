
{-# OPTIONS --without-K #-}

module ecats.constructions.yoneda where

open import ecats.basic-defs.ecat-def&not
open import ecats.basic-defs.isomorphism
open import ecats.functors.defs.efunctor-d&n
open import ecats.functors.defs.basic-defs
open import ecats.functors.defs.natural-transformation
open import ecats.functors.defs.presheaf
open import ecats.functors.defs.representable
open import ecats.constructions.opposite
open import ecats.constructions.functor-ecat
open import ecats.concr-ecats.Std-lev hiding (Std)


Yo : {ℓₒ ℓₐ ℓ~ : Level}(ℂ : ecategoryₗₑᵥ ℓₒ ℓₐ ℓ~) → efunctorₗₑᵥ ℂ (PShₗₑᵥ ℂ)
Yo ℂ = record
  { FObj = ℂ [─,_ₒ]
  ; FHom = ℂ [─,_ₐ]
  ; isF = record
        { ext = λ f~f' X x → ∘e r f~f'
        ; id = λ X x → lid
        ; cmp = λ f g X x → ass
        }
  }
  where open ecategory-aux ℂ

coYo : {ℓₒ ℓₐ ℓ~ : Level}(ℂ : ecategoryₗₑᵥ ℓₒ ℓₐ ℓ~) → efunctorₗₑᵥ (ℂ ᵒᵖ) (coPShₗₑᵥ ℂ)
coYo ℂ = record
  { FObj = ℂ [ₒ_,─]
  ; FHom = ℂ [ₐ_,─]
  ; isF = record
        { ext = λ f~f' X x → ∘e f~f' r
        ; id = λ X x → rid
        ; cmp = λ f g X x → assˢ
        }
  }
  where open ecategory-aux ℂ


module yoneda-props {ℓₒ ℓₐ ℓ~ : Level}(ℂ : ecategoryₗₑᵥ ℓₒ ℓₐ ℓ~) where
  private
    module ℂ where
      open ecat ℂ public
      open iso-defs ℂ public
    Std : ecategoryₗₑᵥ (Stdₗₑᵥ.ℓₒ ℂ.ℓₐᵣᵣ ℂ.ℓ~) (Stdₗₑᵥ.ℓₐᵣᵣ ℂ.ℓₐᵣᵣ ℂ.ℓ~) (Stdₗₑᵥ.ℓ~ ℂ.ℓₐᵣᵣ ℂ.ℓ~)
    Std = Stdₗₑᵥ ℂ.ℓₐᵣᵣ ℂ.ℓ~
    module Std = ecategory-aux Std
    module PShℂ where
      open ecat (PShₗₑᵥ ℂ) public
      open iso-defs (PShₗₑᵥ ℂ) public
    infix 70 ℂ[─,_]
    ℂ[─,_] : ℂ.Obj → presheafₗₑᵥ ℂ
    ℂ[─, X ] = efctr.ₒ (Yo ℂ) X --ℂ [─, X ]
    
  
  Yo-faith : is-faithful (Yo ℂ)
  Yo-faith = record
    { faith-pf = λ {X} {Y} {f} {g} eq → ridˢ ⊙ eq X (ℂ.idar X) ⊙ rid
    }
    where open ecategory-aux-only ℂ

  module Lemma (F : presheafₗₑᵥ ℂ)(X : ℂ.Obj) where
      open import tt-basics.setoids using (setoid; setoidmap; std-id; std-cmp; ptw~)
      private
        module [─,X] = presheafₗₑᵥ ℂ[─, X ]
        module F = presheafₗₑᵥ F
        module FX = F.ₒ X
        yo-el : ℂ[─, X ] ⇒ F → || F.ₒ X ||
        yo-el μ = μ.ap {X} (ℂ.idar X)
                    where module μ = psheaf-morₗₑᵥ μ
        yo-fnc : (x : || F.ₒ X ||){A : ℂ.Obj} → || Std.Hom (ℂ.Hom A X) (F.ₒ A) ||
        yo-fnc x {A} = record
                     { op = λ a → F.ₐ.ap a x
                     ; ext = λ {a} {a'} pfeq → F.ext pfeq x
                     }
        yo-natt : || F.ₒ X || → ℂ[─, X ] ⇒ F
        yo-natt x = record
                  { fnc = yo-fnc x
                  ; nat =  λ f a → F.cmpˢ a f x
                  }
      -- end private
      
      -- Note that 'NatTr [─, X ] F) : setoid (ℂ.ℓₙₒ~ ⊔ Std.ℓₕₒₘ) (ℂ.ℓₒ ⊔ Std.ℓ~)'
      -- i.e. 'NatTr [─, X ] F) : setoid ℂ.ℓₐₗₗ ℂ.ℓₐₗₗ', while 'F.ₒ : setoid ℂ.ℓₐᵣᵣ ℂ.ℓ~'.
      -- So setoidmap below cannot be replaced by Stdₗₑᵥ.Hom in general (and at any level),
      -- not even when ℂ is locally small.
      natt2el : setoidmap (NatTr ℂ[─, X ] F) (F.ₒ X)
      natt2el = record
              { op = yo-el
              ; ext = λ pfeq → pfeq X (ℂ.idar X)
              }
      module natt2el = setoidmap natt2el renaming (op to ap)

      el2natt : setoidmap (F.ₒ X) (NatTr ℂ[─, X ] F)
      el2natt = record
              { op = yo-natt
              ; ext = λ pfeq A a → F.ₐ.ext a pfeq
              }
      module el2natt = setoidmap el2natt renaming (op to ap)

      id-el : ptw~ (std-cmp natt2el el2natt) (std-id {A = F.ₒ X})
      id-el x = F.ₐ.ap (ℂ.idar X) x  ~[ F.id x ]  x ∎
              where open FX using (endpoints)

      id-natt : ptw~ (std-cmp el2natt natt2el) (std-id {A = NatTr ℂ[─, X ] F})
      id-natt μ A a = ~proof
                    F.ₐ.ap a (μ.ap (ℂ.idar X))       ~[ μ.nat a (ℂ.idar X) ˢ ] /
                    μ.ap (ℂ.idar X ℂ.∘ a)              ~[ μ.ext lid ]∎
                    μ.ap {A} a ∎
                    where module μ = psheaf-morₗₑᵥ μ
                          module FA = F.ₒ A
                          open FA using (_ˢ; ~proof_~[_]_; eqreasend; /_~[_]_)
                          open ecategory-aux-only ℂ using (lid)
  -- end Lemma

  Yo-full : is-full (Yo ℂ)
  Yo-full = record
    { ar = λ {X} {Y} → natt2el.ap ℂ[─, Y ] X
    ; pf = λ {X} {Y} {μ} → id-natt ℂ[─, Y ] X μ
    }
    where open Lemma

  Yo-conserv : is-conservative (Yo ℂ)
  Yo-conserv = f&f-is-conservative Yo-full Yo-faith

  Yo-creates-iso : {X Y : ℂ.Obj} → ℂ[─, X ] PShℂ.≅ₒ ℂ[─, Y ] → X ℂ.≅ₒ Y
  Yo-creates-iso = f&f-creates-isos Yo-full Yo-faith

-- end yoneda-props
