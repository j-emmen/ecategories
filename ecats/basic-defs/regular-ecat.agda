
-- disable the K axiom:

{-# OPTIONS --without-K #-}

-- Agda version 2.5.4.1

module ecats.basic-defs.regular-ecat where

open import ecats.basic-defs.ecat-def&not
open import ecats.basic-defs.epi&mono
open import ecats.basic-defs.image-fact
open import ecats.finite-limits.defs.collective



record is-regular//has-connlim {ℂ : ecategory}(hascl : has-conn-limits ℂ) : Set₁ where
  open ecategory ℂ
  open epis&monos-defs ℂ
  field
    pb-stb-imgfact₂ : has-pb-stable-img-fact₂ ℂ
  open has-pb-stable-img-fact₂ pb-stb-imgfact₂ public
  -- the following is derivable (see Borceux), but useful to assume it for now
  --field
    --imgQ-is-repi : {A B : Obj} (f : || Hom A B ||) → is-regular-epi (img-of.Q f)



record is-locally-regular (ℂ : ecategory) : Set₁ where
  field
    hascl : has-conn-limits ℂ
    isreg/ : is-regular//has-connlim hascl
  open has-conn-limits hascl public
  open is-regular//has-connlim isreg/ public
  


record is-regular//has-finlim {ℂ : ecategory}(hasfl : has-fin-limits ℂ) : Set₁ where
  open ecategory ℂ
  open epis&monos-defs ℂ
  field
    pb-stb-imgfact : has-pb-stable-img-fact ℂ
  open has-pb-stable-img-fact pb-stb-imgfact public
  -- the following is derivable (see Borceux), but useful to assume it for now
  --field
    --imgQ-is-repi : {A B : Obj} (f : || Hom A B ||) → is-regular-epi (img-of.Q f)


record is-regular (ℂ : ecategory) : Set₁ where
  field
    hasfl : has-fin-limits ℂ
    isreg/fl : is-regular//has-finlim hasfl
  open has-fin-limits hasfl public
  open is-regular//has-finlim isreg/fl public
  
