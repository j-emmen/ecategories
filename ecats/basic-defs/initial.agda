
{-# OPTIONS --without-K #-}

module ecats.basic-defs.initial where

open import ecats.basic-defs.ecat-def&not


module initial-defs {ℓ₁ ℓ₂ ℓ₃ : Level}(ℂ : ecategoryₗₑᵥ ℓ₁ ℓ₂ ℓ₃) where
  open ecategory-aux ℂ

  record is-initial (I : Obj) : Set ℓₐₗₗ where
    field
      ø : (A : Obj) → || Hom I A ||
      øuq : {A : Obj}(f : || Hom I A ||) → f ~ ø A
    øuqg : {A : Obj} {f g : || Hom I A ||}
              → f ~ g
    øuqg {f = f} {g} = øuq f ⊙ øuq g ˢ

--end initial-defs


record has-initial {ℓ₁ ℓ₂ ℓ₃ : Level}(ℂ : ecategoryₗₑᵥ ℓ₁ ℓ₂ ℓ₃) : Set (ecat.ℓₐₗₗ ℂ) where
  open ecategory-aux ℂ
  open initial-defs ℂ
  field
    {initOb} : Obj
    isinit : is-initial initOb
  open is-initial isinit public
