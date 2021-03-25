 
{-# OPTIONS --without-K #-}

module ecats.basic-defs.groupoid where

open import ecats.basic-defs.ecat-def&not
open import ecats.basic-defs.isomorphism

record is-groupoid (𝔾 : ecategory) : Set₁ where
  open ecategory 𝔾
  open iso-defs 𝔾
  field
    inv : {X Y : Obj} → || Hom X Y || → || Hom Y X ||
    isisopair : {X Y : Obj}(f : || Hom X Y ||) → is-iso-pair f (inv f)


-- Very bad definition of groupoid
record groupoid : Set₂ where
  field
    𝔾 : ecategory
    isgpd : is-groupoid 𝔾
