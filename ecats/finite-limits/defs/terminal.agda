
{-# OPTIONS --without-K #-}

module ecats.finite-limits.defs.terminal where

open import Agda.Primitive
open import ecats.basic-defs.ecat-def&not



-- Terminal

module terminal-defs {ℓ₁ ℓ₂ ℓ₃ : Level}(ℂ : ecategoryₗₑᵥ ℓ₁ ℓ₂ ℓ₃) where
  open ecategory-aux ℂ

  record is-terminal (T : Obj) : Set ℓₐₗₗ where
    --constructor mkistrm
    field
      ! : (A : Obj) → || Hom A T ||
      !uniq : {A : Obj} → (f : || Hom A T ||) → f ~ ! A
    !uqg : {A : Obj} {f g : || Hom A T ||}
              → f ~ g
    !uqg {f = f} {g} = !uniq f ⊙ !uniq g ˢ

--end terminal-defs


record has-terminal {ℓ₁ ℓ₂ ℓ₃ : Level}(ℂ : ecategoryₗₑᵥ ℓ₁ ℓ₂ ℓ₃) : Set (ecat.ℓₐₗₗ ℂ) where
  --constructor mkhas-trm
  open ecategory-aux ℂ
  open terminal-defs ℂ
  field
    trmOb : Obj
    istrm : is-terminal trmOb
  open is-terminal istrm public
