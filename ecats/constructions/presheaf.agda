
{-# OPTIONS --without-K #-}

module ecats.constructions.presheaf where

import tt-basics.setoids using (setoid; setoidmap)
open import ecats.basic-defs.ecat-def&not
open import ecats.functors.defs.efunctor-d&n
open import ecats.functors.defs.natural-transformation
open import ecats.constructions.opposite
open import ecats.constructions.functor-ecat
open import ecats.concr-ecats.Std

presheaf : (ℂ : ecategory) → Set₁
presheaf ℂ = efunctor (ℂ ᵒᵖ) Std
module presheaf {ℂ : ecategory}(F : presheaf ℂ) where
  open ecategory ℂ using (Obj; Hom)
  open efunctor-aux F public
  module ₒ (X : Obj) = tt-basics.setoids.setoid (ₒ X)
  _ₒ~_ : {X : Obj}(x x' : || ₒ X ||) → Set
  _ₒ~_ {X} x x' = ₒ._∼_ X x x'
  module ₐ {Z Z' : Obj}(g : || Hom Z Z' ||) where
    open tt-basics.setoids.setoidmap (ₐ g) renaming (op to ap) public
module psheaf-mor {ℂ : ecategory}{F G : presheaf ℂ}(μ : F ⇒ G) where
  open ecategory ℂ using (Obj)
  open natural-transformation μ public
  private module ar {Z : Obj} = tt-basics.setoids.setoidmap (fnc {Z})
  open ar renaming (op to ap) public

PSh : (ℂ : ecategory) → large-ecategory
PSh ℂ = Fctr (ℂ ᵒᵖ) Std


module representable-presheaf (ℂ : ecategory) where
  open ecategory-aux ℂ
  repr-presheaf : (X : Obj) → presheaf ℂ
  repr-presheaf X = record
    { FObj = λ Y → Hom Y X
    ; FHom = λ f → record
           { op = λ a → a ∘ f
           ; ext = ∘e r
           }
    ; isF = record
          { ext = λ f~f' a → ∘e f~f' r 
          ; id = λ a → rid
          ; cmp = λ f g a → assˢ
          }
    }

  infix 7 [─,_]
  [─,_] : (X : Obj) → presheaf ℂ
  [─, X ] = repr-presheaf X
  
  precmp-nat : {X Y : Obj}(f : || Hom X Y ||)
                  → || Nat (repr-presheaf X) (repr-presheaf Y) ||
  precmp-nat f = record
    { fnc = record
          { op = λ a → f ∘ a
          ; ext = λ pf → ∘e pf r
          }
    ; nat = λ g a → ass
    }
-- end representable-presheaf
