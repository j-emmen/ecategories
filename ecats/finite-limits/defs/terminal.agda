 
-- disable the K axiom:

{-# OPTIONS --without-K #-}

-- Agda version 2.5.4.1

module ecats.finite-limits.defs.terminal where

open import ecats.basic-defs.ecat-def&not



-- Terminal

module terminal-defs (ℂ : ecategory) where
  open ecategory-aux ℂ

  record is-terminal (T : Obj) : Set₁ where
    constructor mkistrm
    field
      { ! } : (A : Obj) → || Hom A T ||
      !uniq : {A : Obj} → (f : || Hom A T ||) → f ~ ! A
    !uqg : {A : Obj} {f g : || Hom A T ||}
              → f ~ g
    !uqg {f = f} {g} = !uniq f ⊙ !uniq g ˢ

--end terminal-defs


record has-terminal (ℂ : ecategory) : Set₁ where
  constructor mkhas-trm
  open ecategory-aux ℂ
  open terminal-defs ℂ
  field
    {trmOb} : Obj
    istrm : is-terminal trmOb
  open is-terminal istrm public
