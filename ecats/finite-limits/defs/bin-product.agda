
{-# OPTIONS --without-K #-}

module ecats.finite-limits.defs.bin-product where

open import ecats.basic-defs.ecat-def&not
open import ecats.basic-defs.commut-shapes





-- Binary products

module bin-product-defs (ℂ : ecategory) where
  open ecategory-aux ℂ
  open comm-shapes ℂ

  record is-product (sp : span) : Set₁ where
    --constructor mkis-prd
    open span sp renaming (a1 to π₁; a2 to π₂)
    field
      <_,_> : {A : Obj} → || Hom A O1 || → || Hom A O2 || → || Hom A O12 ||
      ×tr₁ : {A : Obj} {f : || Hom A O1 ||} {g : || Hom A O2 ||} → π₁ ∘ < f , g > ~ f
      ×tr₂ : {A : Obj} {f : || Hom A O1 ||} {g : || Hom A O2 ||} → π₂ ∘ < f , g > ~ g
      ×uq : {A : Obj} {h h' : || Hom A O12 ||}
               → π₁ ∘ h ~ π₁ ∘ h' → π₂ ∘ h ~ π₂ ∘ h' → h ~ h'


  record bin-product : Set₁ where
    constructor mk×
    field
      {×sp} : span
      ×isprd : is-product ×sp
    open span ×sp renaming (a1 to π₁; a2 to π₂) public
    open is-product ×isprd public


  record product-of (O1 O2 : Obj) : Set₁ where
    constructor mk×of
    --open commut-shapes ℂ
    field
      {×sp/} : span/ O1 O2
      ×isprd : is-product (mkspan-c ×sp/)
    open span/ ×sp/ renaming (a1 to π₁; a2 to π₂) public
    open is-product ×isprd public
    prdsp : bin-product
    prdsp = mk× ×isprd


-- end bin-products-defs


record has-bin-products (ℂ : ecategory) : Set₁ where
  --constructor mkhas-prds
  open ecategory ℂ
  open comm-shapes ℂ
  open bin-product-defs ℂ
  field
    prd-of : (A B : Obj) → product-of A B
  module prd-of {A B : Obj}  = product-of (prd-of A B)
  open prd-of public
  ×of : {A B : Obj} → product-of A B
  ×of {A} {B} = prd-of A B
  infix 10 _×_
  _×_ : Obj → Obj → Obj
  A × B = prd-of.O12 {A} {B}
