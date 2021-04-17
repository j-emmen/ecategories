
-- disable the K axiom:

{-# OPTIONS --without-K #-}

-- Agda version 2.5.4.1

module ecats.basic-defs.exact-ecat where

open import ecats.basic-defs.ecat-def&not
open import ecats.basic-defs.epi&mono
open import ecats.basic-defs.eqv-rel
open import ecats.basic-defs.kernel-pair
open import ecats.finite-limits.defs.collective
open import ecats.finite-limits.d&n-pullback
open import ecats.finite-limits.props.pullback


 
record is-exact//has-conn-lim {ℂ : ecategory} (hascl : has-conn-limits ℂ) : Set₁ where
  open ecategory ℂ
  open epis&monos-defs ℂ
  open kernel-pairs-defs ℂ
  open pullback-props ℂ
  open eq-rel-defs ℂ
  open eqrel-over
  field
    repi-pbof-stable : is-pbof-stable is-regular-epi
    eqr-has-coeq : {A : Obj} (eqr : eqrel-over A)
                        → coeq-of (r₁ eqr) (r₂ eqr)
    eqr-is-eff : {A : Obj} (eqr : eqrel-over A)
                      → is-kernel-pair (r₁ eqr) (r₂ eqr)
  repi-pbsq-stable : is-pbsq-stable is-regular-epi
  repi-pbsq-stable = pbof-stb→pbsq-stb repi-pbof-stable


record is-locally-exact (ℂ : ecategory) : Set₁ where
  field
    hascl : has-conn-limits ℂ
    isex/cl : is-exact//has-conn-lim hascl
  open is-exact//has-conn-lim isex/cl public
  open has-conn-limits hascl public


mklocexact : {ℂ : ecategory} {hascl : has-conn-limits ℂ} → is-exact//has-conn-lim hascl
                → is-locally-exact ℂ
mklocexact {ℂ} {hascl} isex/cl = record { hascl = hascl ; isex/cl = isex/cl }



record is-exact//has-fin-lim {ℂ : ecategory} (hascl : has-fin-limits ℂ) : Set₁ where
  open ecategory ℂ
  open epis&monos-defs ℂ
  open kernel-pairs-defs ℂ
  open pullback-props ℂ
  open eq-rel-defs ℂ
  open eqrel-over using (r₁; r₂)
  field
    repi-pbof-stable : is-pbof-stable is-regular-epi
    eqr-has-coeq : {A : Obj} (eqr : eqrel-over A)
                        → coeq-of (r₁ eqr) (r₂ eqr)
    eqr-is-eff : {A : Obj} (eqr : eqrel-over A)
                      → is-kernel-pair (r₁ eqr) (r₂ eqr)
  repi-pbsq-stable : is-pbsq-stable is-regular-epi
  repi-pbsq-stable = pbof-stb→pbsq-stb repi-pbof-stable


record is-exact (ℂ : ecategory) : Set₁ where
  field
    hasfl : has-fin-limits ℂ
    isex/fl : is-exact//has-fin-lim hasfl
  open is-exact//has-fin-lim isex/fl public
  open has-fin-limits hasfl public


mkexact : {ℂ : ecategory} {hasfl : has-fin-limits ℂ} → is-exact//has-fin-lim hasfl → is-exact ℂ
mkexact {ℂ} {hasfl} isex/fl = record { hasfl = hasfl ; isex/fl = isex/fl }
