
-- disable the K axiom:

{-# OPTIONS --without-K #-}

-- Agda version 2.5.4.1

module ecats.finite-limits.defs.bin-weak-product where

open import ecats.basic-defs.ecat-def&not
open import ecats.basic-defs.commut-shapes



-- Weak binary products

module bin-wproduct-defs (ℂ : ecategory) where
  open ecategory-aux ℂ
  open comm-shapes ℂ

  record is-wproduct (sp : span) : Set₁ where
    --constructor mkis-prd
    open span sp renaming (a1 to wπ₁; a2 to wπ₂)
    field
      w<_,_> : {A : Obj} → || Hom A O1 || → || Hom A O2 || → || Hom A O12 ||
      w×tr₁ : {A : Obj} {f : || Hom A O1 ||} {g : || Hom A O2 ||} → wπ₁ ∘ w< f , g > ~ f
      w×tr₂ : {A : Obj} {f : || Hom A O1 ||} {g : || Hom A O2 ||} → wπ₂ ∘ w< f , g > ~ g


  record bin-wproduct : Set₁ where
    constructor mkw×
    field
      {w×sp} : span
      iswprd : is-wproduct w×sp
    open span w×sp renaming (a1 to wπ₁; a2 to wπ₂) public
    open is-wproduct iswprd public
    

  record wproduct-of (O1 O2 : Obj) : Set₁ where
    constructor mkw×of
    --open commut-shapes ℂ
    field
      {w×sp/} : span/ O1 O2
      iswprd : is-wproduct (mkspan-c w×sp/)
    open span/ w×sp/ renaming (a1 to wπ₁; a2 to wπ₂) public
    open is-wproduct iswprd public
    wprdsp : bin-wproduct
    wprdsp = mkw× iswprd
    
-- end bin-wproduct-defs


record has-bin-weak-products (ℂ : ecategory) : Set₁ where
  --constructor mkhas-prds
  open ecategory ℂ
  open comm-shapes ℂ
  open bin-wproduct-defs ℂ
  field
    wprd-of : (A B : Obj) → wproduct-of A B
  module wprd-of {A B : Obj}  = wproduct-of (wprd-of A B)
  open wprd-of public
  w×of : {A B : Obj} → wproduct-of A B
  w×of {A} {B} = wprd-of A B
  infix 10 _w×_
  _w×_ : Obj → Obj → Obj
  A w× B = wprd-of.O12 {A} {B}
