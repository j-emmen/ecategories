 
-- disable the K axiom:

{-# OPTIONS --without-K #-}

-- Agda version 2.5.4.1

module ecats.basic-defs.finite-ecat where

open import tt-basics.basics
open import tt-basics.setoids
open import ecats.basic-defs.ecategory
open import ecats.basic-defs.ecategory-not




record finite-ecategory : Set where
  field
    obj : N
    hom : Fin obj → Fin obj → N
  Obj = Fin obj
  Hom = λ i j → Freestd (Fin (hom i j))
  field
    isecat : is-ecategory Obj Hom
  open is-ecategory isecat public



finite-ecat-is-small : finite-ecategory → small-ecategory
finite-ecat-is-small 𝕀 = record { Obj = Obj
                                 ; Hom = Hom
                                 ; isecat = isecat
                                 }
                                 where open finite-ecategory 𝕀




module finite-ecategory-aux-only (𝕀 : finite-ecategory) where
  open small-ecategory-aux-only (finite-ecat-is-small 𝕀) public
-- end module ecategory-aux-only


module finite-ecategory-aux (𝕀 : finite-ecategory) where
  open finite-ecategory 𝕀 public
  open finite-ecategory-aux-only 𝕀 public
-- end module ecategory-aux
