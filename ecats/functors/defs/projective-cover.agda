
{-# OPTIONS --without-K #-}

module ecats.functors.defs.projective-cover where

open import ecats.basic-defs.ecat-def&not
open import ecats.basic-defs.epi&mono
open import ecats.functors.defs.efunctor-d&n
open import ecats.functors.defs.basic-defs



module projective-defs (ℂ : ecategory) where
  open ecategory ℂ
  open epi&mono-defs ℂ

  record is-reg-projective (X : Obj) : Set₁ where
    --open ecategory-aux-only ℂ
    field
      lift : {A B : Obj} {f : || Hom A B ||} (repi : is-regular-epi f)
                → || Hom X B || → || Hom X A ||
      lift-tr :  {A B : Obj} {f : || Hom A B ||} {repi : is-regular-epi f} {g : || Hom X B ||}
                    → f ∘ lift repi g ~ g

{-
  record _covers_ (X Y : Obj) : Set₁ where
    field
      ar : || Hom X Y ||
      is-repi : is-regular-epi ar

  record reg-cover-of (X : Obj) : Set₁ where
    field
      Ob : Obj
      cov : Ob covers X
      {-ar : || Hom Ob X ||
      is-repi : is-regular-epi ar-}
    open _covers_ cov public
-}

-- end projective-defs

private
  module prj-aux (𝕏 : ecategory) where
    open ecategory 𝕏 public
    open projective-defs 𝕏 public
    open epi&mono-defs 𝕏 public
record is-projective-cover {ℂ ℙ : ecategory} (PC : efunctor ℙ ℂ) : Set₁ where
  private
    module ℂ = prj-aux ℂ
    module ℙ = ecategory ℙ
    module PC = efunctor PC
  field
    isfull : is-full PC
    isfaith : is-faithful PC
    img-proj : (X : ℙ.Obj) → ℂ.is-reg-projective (PC.ₒ X)
    reg-cov-obj : ℂ.Obj → ℙ.Obj
    is-reg-cov : (A : ℂ.Obj) → (PC.ₒ (reg-cov-obj A)) ℂ.covers A
    --reg-cover-ar : (A : ℂ.Obj) → || ℂ.Hom (PC.ₒ (reg-cover-obj A)) A ||
    --reg-cover-is-repi : (A : ℂ.Obj) → ℂ.is-regular-epi (reg-cover-ar A)
  open is-faithful isfaith public
  module full = is-full isfull
  module rprj (X : ℙ.Obj) = ℂ.is-reg-projective (img-proj X)
  module rcov-of (A : ℂ.Obj) where
    open ℂ._covers_ (is-reg-cov A) public
    Ob : ℙ.Obj
    Ob = reg-cov-obj A
    PCOb : ℂ.Obj
    PCOb = PC.ₒ Ob
  {-rC : ℂ.Obj → ℙ.Obj
  rC = reg-cover-obj
  covers : (A : ℂ.Obj) → (PC.ₒ (rC A)) ℂ.covers A
  covers A = record
    { ar = reg-cover-ar A
    ; is-repi = reg-cover-is-repi A
    }
  reg-cov : (A : ℂ.Obj) → ℂ.reg-cover-of A
  reg-cov A = record
    { Ob = PC.ₒ (rC A)
    ; cov = covers A
    }-}

{-    
  rC : ℂ.Obj → ℙ.Obj
  rC = reg-cover-obj
  rc : (A : ℂ.Obj) → || ℂ.Hom (PC.ₒ (rC A)) A ||
  rc = reg-cover-ar
  rc-repi : (A : ℂ.Obj) → is-regular-epi (reg-cover-ar A)
  rc-repi = reg-cover-is-repi
-}
