
{-# OPTIONS --without-K #-}

module ecats.basic-defs.generator where

open import ecats.basic-defs.ecat-def&not
open import ecats.finite-limits.defs.terminal

module generator-defs (ℂ : ecategory) where
  open ecategory ℂ
  record is-generating-obj-rec (A : Obj) : Set₁ where
    field
      pf : {B C : Obj}{f g : || Hom B C ||}
           (H : (h : || Hom A B ||) → f ∘ h ~ g ∘ h)
             → f ~ g
  is-generating-obj : (A : Obj) → Set₁
  is-generating-obj A = {B C : Obj}{f g : || Hom B C ||}
                        (H : (h : || Hom A B ||) → f ∘ h ~ g ∘ h)
                          → f ~ g
-- end generating-object

record terminal-is-generator {ℂ : ecategory}(trm : has-terminal ℂ) : Set₁ where
  open ecategory ℂ
  open generator-defs ℂ
  open has-terminal trm
  field
    isgen : is-generating-obj trmOb

