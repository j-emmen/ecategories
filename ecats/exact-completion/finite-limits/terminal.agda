
-- disable the K axiom:

{-# OPTIONS --without-K #-}

-- Agda version 2.5.4.1

module ecats.exact-completion.finite-limits.terminal where

open import ecats.basic-defs.ecat-def&not
open import ecats.basic-defs.eqv-rel
open import ecats.finite-limits.defs.collective
open import ecats.finite-limits.defs.terminal
open import ecats.finite-limits.d&n-bin-weak-product
open import ecats.exact-completion.construction



-- Terminal object

module exact-compl-has-terminal {ℂ : ecategory} (hasfwl : has-fin-weak-limits ℂ) where
  open ecategory-aux ℂ
  open pseudo-eq-rel-defs ℂ
  open has-fin-weak-limits hasfwl
  open has-weak-terminal haswtrm
  open has-bin-weak-products haswprd using (wprd-of)
  open binary-wproducts ℂ
  private
    module Exℂ = ecategory Ex ℂ [ hasfwl ]
    module trmHi = wproduct-of-not (wprd-of wtrmOb wtrmOb)


  Peq-term : Exℂ.Obj
  Peq-term = cofreePeq-from-wprd+wpb haswprd haswpb wtrmOb

  Peq-! : (R : Exℂ.Obj) → || Exℂ.Hom R Peq-term ||
  Peq-! R = record { lo = lo!
                   ; isext = record
                     { hi = trmHi.w< lo! ∘ R.%0 , lo! ∘ R.%1 >
                     ; cmptb₀ = trmHi.w×tr₁
                     ; cmptb₁ = trmHi.w×tr₂
                     }
                   }
                   where module R = Peq R
                         lo! : || Hom R.Lo wtrmOb ||
                         lo! = w! R.Lo
  
  ex-cmpl-term : has-terminal Ex ℂ [ hasfwl ]
  ex-cmpl-term = record { trmOb = Peq-term
                        ; istrm = record
                                { ! = Peq-!
                                ; !uniq = λ {R} f → record
                                        { hty = trmHi.w< lo f , w! (Lo R) >
                                        ; hty₀ = trmHi.w×tr₁
                                        ; hty₁ = trmHi.w×tr₂
                                        }
                                }
                        }
               where open Peq using (Lo)
                     open Peq-mor using (lo)

-- end exact-compl-has-terminal


exact-compl-has-terminal : {ℂ : ecategory} (hasfwl : has-fin-weak-limits ℂ) → has-terminal Ex ℂ [ hasfwl ]
exact-compl-has-terminal hasfwl = ex-cmpl-term
                                where open exact-compl-has-terminal hasfwl using (ex-cmpl-term)

exact-compl-qcart-has-terminal : {ℂ : ecategory} (qcart : is-quasi-cartesian ℂ) → has-terminal Ex ℂ qc[ qcart ]
exact-compl-qcart-has-terminal qcart = exact-compl-has-terminal (qcart→has-fwl qcart)
--ex-cmpl-term
  --                                   where open exact-compl-has-terminal (qcart→has-fwl qcart) using (ex-cmpl-term)