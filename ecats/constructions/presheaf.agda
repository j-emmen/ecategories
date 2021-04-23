
{-# OPTIONS --without-K #-}

module ecats.constructions.presheaf where

open import ecats.basic-defs.ecat-def&not
open import ecats.functors.defs.efunctor-d&n
open import ecats.functors.defs.natural-transformation
open import ecats.constructions.opposite
open import ecats.constructions.functor-ecat
open import ecats.concr-ecats.Std

presheaf : (ℂ : ecategory) → Set₁
presheaf ℂ = efunctor (ℂ ᵒᵖ) Std
module presheaf {ℂ : ecategory}(F : presheaf ℂ) = efunctor F

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

PSh : (ℂ : ecategory) → large-ecategory
PSh ℂ = Fctr (ℂ ᵒᵖ) Std

Y : (ℂ : ecategory) → efunctorₗₑᵥ ℂ (PSh ℂ)
Y ℂ = record
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
