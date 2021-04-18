 
{-# OPTIONS --without-K #-}

module ecats.basic-defs.isomorphism where

open import ecats.basic-defs.ecat-def&not

module iso-defs (ℂ : ecategory) where
  open ecategory ℂ

  record is-iso-pair {a b : Obj} (f : || Hom a b ||) (invf : || Hom b a ||) : Set where
    field
      iddom : invf ∘ f ~ idar a
      idcod : f ∘ invf ~ idar b

  record is-iso {a b : Obj} (f : || Hom a b ||) : Set where
    constructor mkis-iso
    field
      {invf} : || Hom b a ||
      isisopair : is-iso-pair f invf
    open is-iso-pair isisopair public
    ⁻¹ : || Hom b a ||
    ⁻¹ = invf

  infix 0 _≅ₒ_ 
  record _≅ₒ_ (a b : Obj) : Set where
    constructor mk≅
    field
      {a12} : || Hom a b ||
      {a21} : || Hom b a ||
      isop : is-iso-pair a12 a21
    open is-iso-pair isop public

-- end module iso-defs
