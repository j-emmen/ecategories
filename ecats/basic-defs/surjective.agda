
{-# OPTIONS --without-K #-}

module ecats.basic-defs.surjective where

open import ecats.basic-defs.ecat-def&not
open import ecats.basic-defs.commut-shapes
open import ecats.basic-defs.isomorphism
open import ecats.finite-limits.defs.terminal

module surjective-defs {ℂ : ecategory} (hastrm : has-terminal ℂ) where
  open ecategory ℂ
  open has-terminal hastrm

  record is-surjective {A B : Obj} (f : || Hom A B ||) : Set where
    field
      cntimg : || Hom trmOb B || → || Hom trmOb A ||
      cntimg-pf : {b : || Hom trmOb B ||} → f ∘ cntimg b ~ b
-- end surjective-defs
