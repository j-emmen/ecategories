
{-# OPTIONS --without-K #-}

module ecats.functors.defs.representable where

open import tt-basics.setoids using (setoidmap)
open import ecats.basic-defs.ecat-def&not
open import ecats.functors.defs.efunctor-d&n
open import ecats.functors.defs.natural-iso
open import ecats.functors.defs.presheaf
open import ecats.constructions.opposite
open import ecats.concr-ecats.Std-lev


repres-copsh-atₒ : {ℓₒ ℓₐ ℓ~ : Level}(ℂ : ecategoryₗₑᵥ ℓₒ ℓₐ ℓ~)(X : ecat.Obj ℂ)
                     → copresheafₗₑᵥ ℂ
repres-copsh-atₒ ℂ X =  record
  { FObj = λ Y → Hom X Y
  ; FHom = λ f → record
         { op = λ a → f ∘ a
         ; ext = λ pf → ∘e pf r
         }
  ; isF = record
        { ext = λ f~f' a → ∘e r f~f'
        ; id = λ a → lid
        ; cmp = λ f g a → ass
        }
  }
  where open ecategory-aux ℂ

infix 90 _[ₒ_,─] _[─,_ₒ]
_[ₒ_,─] : {ℓₒ ℓₐ ℓ~ : Level}(ℂ : ecategoryₗₑᵥ ℓₒ ℓₐ ℓ~)(X : ecat.Obj ℂ) → copresheafₗₑᵥ ℂ
ℂ [ₒ X ,─] = repres-copsh-atₒ ℂ X  
_[─,_ₒ] : {ℓₒ ℓₐ ℓ~ : Level}(ℂ : ecategoryₗₑᵥ ℓₒ ℓₐ ℓ~)(X : ecat.Obj ℂ) → presheafₗₑᵥ ℂ
ℂ [─, X ₒ] = (ℂ ᵒᵖ) [ₒ X ,─]


record is-represble-copsheaf {ℓₒ ℓₐ ℓ~ : Level}{ℂ : ecategoryₗₑᵥ ℓₒ ℓₐ ℓ~}(F : copresheafₗₑᵥ ℂ)
                          : Set (ℓₒ ⊔ ℓₐ ⊔ ℓ~) where
  open ecat ℂ using (Obj)
  field
    Rob : Obj
    natiso : F ≅ₐ ℂ [ₒ Rob ,─]
  module natiso where
    open natural-iso natiso public
    module fnc (A : Obj) = StdHom (fnc {A})
    module fnc⁻¹ (A : Obj) = StdHom (fnc⁻¹ {A})


is-represble-psheaf : {ℓₒ ℓₐ ℓ~ : Level}{ℂ : ecategoryₗₑᵥ ℓₒ ℓₐ ℓ~}(F : presheafₗₑᵥ ℂ)
                           → Set (ℓₒ ⊔ ℓₐ ⊔ ℓ~)
is-represble-psheaf {ℂ = ℂ} F = is-represble-copsheaf {ℂ = ℂ ᵒᵖ} F

module is-represble-psheaf {ℓₒ ℓₐ ℓ~ : Level}{ℂ : ecategoryₗₑᵥ ℓₒ ℓₐ ℓ~}
                           {F : efunctorₗₑᵥ (ℂ ᵒᵖ) (Stdₗₑᵥ ℓₐ ℓ~)}(isrepr : is-represble-psheaf F)
                           where
  open is-represble-copsheaf isrepr using (Rob) public
  open is-represble-copsheaf isrepr using () renaming (natiso to conatiso)
  natiso : F ≅ₐ ℂ [─, Rob ₒ]
  natiso = conatiso
  module natiso where
    open ecat ℂ using (Obj)
    open natural-iso natiso public
    module fnc (A : Obj) = StdHom (fnc {A})
    module fnc⁻¹ (A : Obj) = StdHom (fnc⁻¹ {A})


-- Action on arrows

repres-psh-atₐ : {ℓₒ ℓₐ ℓ~ : Level}(ℂ : ecategoryₗₑᵥ ℓₒ ℓₐ ℓ~){A A' : ecat.Obj ℂ}
                       → || ecat.Hom ℂ A A' ||
                         → || ecat.Hom (PShₗₑᵥ ℂ) (ℂ [─, A ₒ]) (ℂ [─, A' ₒ]) ||
repres-psh-atₐ ℂ {A} {A'} f = record
  { fnc = λ {B} → record
        { op = f ℂ.∘_
        ; ext = λ pf → ℂ.∘e pf ℂ.r 
        }
  ; nat = λ {B'} {B} b a → ℂ.ass
  }
  where module ℂ = ecategory-aux ℂ

repres-copsh-atₐ : {ℓₒ ℓₐ ℓ~ : Level}(ℂ : ecategoryₗₑᵥ ℓₒ ℓₐ ℓ~){A' A : ecat.Obj ℂ}
                       → || ecat.Hom ℂ A' A ||
                         → || ecat.Hom (coPShₗₑᵥ ℂ) (ℂ [ₒ A ,─]) (ℂ [ₒ A' ,─]) ||
repres-copsh-atₐ ℂ {A'} {A} f = record
  { fnc = λ {B} → record
        { op = λ a → a ℂ.∘ f
        ; ext = ℂ.∘e ℂ.r 
        }
  ; nat = λ {B'} {B} b a → ℂ.assˢ
  }
  where module ℂ = ecategory-aux ℂ

infix 90 _[ₐ_,─] _[─,_ₐ]
_[ₐ_,─] : {ℓₒ ℓₐ ℓ~ : Level}(ℂ : ecategoryₗₑᵥ ℓₒ ℓₐ ℓ~){Y X : ecat.Obj ℂ}
             → || ecat.Hom ℂ Y X ||
               → || ecat.Hom (coPShₗₑᵥ ℂ) (ℂ [ₒ X ,─]) (ℂ [ₒ Y ,─]) ||
ℂ [ₐ f ,─] = repres-copsh-atₐ ℂ f
_[─,_ₐ] : {ℓₒ ℓₐ ℓ~ : Level}(ℂ : ecategoryₗₑᵥ ℓₒ ℓₐ ℓ~){X Y : ecat.Obj ℂ}
             → || ecat.Hom ℂ X Y ||
                  → || ecat.Hom (PShₗₑᵥ ℂ) (ℂ [─, X ₒ]) (ℂ [─, Y ₒ]) ||
ℂ [─, f ₐ] = repres-psh-atₐ ℂ f

{-
-- N.B. If we define a representable presheaf as

repres-psheaf : {ℓₒ ℓₐ ℓ~ : Level}(ℂ : ecategoryₗₑᵥ ℓₒ ℓₐ ℓ~)(X : ecat.Obj ℂ)
                     → efunctorₗₑᵥ (ℂ ᵒᵖ) (Stdₗₑᵥ ℓₐ ℓ~) 
repres-psheaf ℂ X =  record
  { FObj = λ Y → Hom Y X
  ; FHom = λ f → record
         { op = λ a → a ∘ f
         ; ext = λ pf → ∘e r pf
         }
  ; isF = record
        { ext = λ f~f' a → ∘e f~f' r
        ; id = λ a → rid
        ; cmp = λ f g a → assˢ
        }
  }
  where open ecategory-aux ℂ

-- Then

open import tt-basics.id-type
ck : {ℓₒ ℓₐ ℓ~ : Level}(ℂ : ecategoryₗₑᵥ ℓₒ ℓₐ ℓ~)(X : ecat.Obj ℂ)
         → repres-psheaf ℂ X == ℂ [─, X ₒ]
ck ℂ X = =rf
-}
