 
-- disable the K axiom:

{-# OPTIONS --without-K #-}

-- Agda version 2.5.4.1

module ecats.finite-limits.defs.weak-terminal where

open import ecats.basic-defs.ecat-def&not



-- Weak terminal

module wterminal-defs (ℂ : ecategory) where
  open ecategory-aux ℂ

  record is-wterminal (T : Obj) : Set₁ where
    constructor mkiswtrm
    field
      w! : (A : Obj) → || Hom A T ||


--end wterminal-defs


record has-weak-terminal (ℂ : ecategory) : Set₁ where
  constructor mkhas-trm
  open ecategory-aux ℂ
  open wterminal-defs ℂ
  field
    {wtrmOb} : Obj
    iswtrm : is-wterminal wtrmOb
  open is-wterminal iswtrm public
