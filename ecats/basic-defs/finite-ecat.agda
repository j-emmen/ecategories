
{-# OPTIONS --without-K #-}

module ecats.basic-defs.finite-ecat where

open import tt-basics.basics
open import tt-basics.setoids
open import ecats.basic-defs.ecategory
open import ecats.basic-defs.ecategory-not




record std-finite-ecategory : Set where
  field
    obj : N
    hom : Fin obj → Fin obj → N
  Obj = Fin obj
  Hom = λ i j → Freestd (Fin (hom i j))
  field
    isecat : is-ecategory Obj Hom
  open is-ecategory isecat public


std-finite-ecat-is-small sfcat2scat : std-finite-ecategory → small-ecategory
std-finite-ecat-is-small 𝕀 = record { Obj = Obj
                                     ; Hom = Hom
                                     ; isecat = isecat
                                     }
                                     where open std-finite-ecategory 𝕀
sfcat2scat = std-finite-ecat-is-small



module std-finite-ecategory-aux-only (𝕀 : std-finite-ecategory) where
  open ecategory-aux-only (sfcat2scat 𝕀) public
-- end module ecategory-aux-only


module finite-ecategory-aux (𝕀 : std-finite-ecategory) where
  open std-finite-ecategory 𝕀 public
  open std-finite-ecategory-aux-only 𝕀 public
-- end module ecategory-aux
