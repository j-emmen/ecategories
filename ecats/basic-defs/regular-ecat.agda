
-- disable the K axiom:

{-# OPTIONS --without-K #-}

-- Agda version 2.5.4.1

module ecats.basic-defs.regular-ecat where

open import ecats.basic-defs.ecat-def&not
open import ecats.basic-defs.epi&mono
open import ecats.basic-defs.image-fact
open import ecats.finite-limits.defs.collective
open import ecats.finite-limits.d&n-pullback
open import ecats.finite-limits.props.pullback


{-
record is-regular//has-connlim {ℂ : ecategory}(hascl : has-conn-limits ℂ) : Set₁ where
  open ecategory ℂ
  open epis&monos-defs ℂ
  field
    pb-stb-imgfact₂ : has-pb-stable-img-fact₂ ℂ
  open has-pb-stable-img-fact₂ pb-stb-imgfact₂ public
  -- the following is derivable (see Borceux), but useful to assume it for now
  --field
    --imgQ-is-repi : {A B : Obj} (f : || Hom A B ||) → is-regular-epi (img-of.Q f)
-}


record is-locally-regular-img (ℂ : ecategory) : Set₁ where
  field
    hascl : has-conn-limits ℂ
    pb-stb-imgfact₂ : has-pb-stable-img-fact₂ ℂ
  open has-conn-limits hascl public
  open has-pb-stable-img-fact₂ pb-stb-imgfact₂ public
  

{-
record is-regular//has-finlim {ℂ : ecategory}(hasfl : has-fin-limits ℂ) : Set₁ where
  open ecategory ℂ
  open epis&monos-defs ℂ
  field
    pb-stb-imgfact : has-pb-stable-img-fact ℂ
  open has-pb-stable-img-fact pb-stb-imgfact public
  -- the following is derivable (see Borceux), but useful to assume it for now
  --field
    --imgQ-is-repi : {A B : Obj} (f : || Hom A B ||) → is-regular-epi (img-of.Q f)
-}

record is-regular-img (ℂ : ecategory) : Set₁ where
  field
    hasfl : has-fin-limits ℂ
    pb-stb-imgfact : has-pb-stable-img-fact ℂ
  open has-fin-limits hasfl public
  open has-pb-stable-img-fact pb-stb-imgfact public


record is-regular (ℂ : ecategory) : Set₁ where
  open ecategory ℂ
  open epis&monos-defs ℂ
  open pullback-props ℂ
  field
    hasfl : has-fin-limits ℂ
    hasrmf : has-repi-mono-fact ℂ
    repi-pbof-stable : is-pbof-stable is-regular-epi
  repi-pbsq-stable : is-pbsq-stable is-regular-epi
  repi-pbsq-stable = pbof-stb→pbsq-stb repi-pbof-stable
  open has-fin-limits hasfl public
  open has-repi-mono-fact hasrmf public


record is-regular-kp (ℂ : ecategory) : Set₁ where
  open ecategory ℂ
  open epis&monos-defs ℂ
  open pullback-defs ℂ
  open pullback-props ℂ
  private
    module pb = pullback-of
  field
    hasfl : has-fin-limits ℂ
    quot-kp : {A B : Obj} {f : || Hom A B ||} (kp : pullback-of f f)
                 → coeq-of (pb.π/₁ kp) (pb.π/₂ kp)
    repi-pbof-stable : is-pbof-stable is-regular-epi
  repi-pbsq-stable : is-pbsq-stable is-regular-epi
  repi-pbsq-stable = pbof-stb→pbsq-stb repi-pbof-stable
  open has-fin-limits hasfl public
