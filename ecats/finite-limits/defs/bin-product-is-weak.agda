
-- disable the K axiom:

{-# OPTIONS --without-K #-}

-- Agda version 2.5.4.1

module ecats.finite-limits.defs.bin-product-is-weak where

open import ecats.basic-defs.ecat-def&not
open import ecats.basic-defs.commut-shapes
open import ecats.finite-limits.defs.bin-weak-product
open import ecats.finite-limits.defs.bin-product


module bin-product→bin-weak-product (ℂ : ecategory) where
  open ecategory-aux ℂ
  open comm-shapes ℂ
  open bin-wproduct-defs ℂ
  open bin-product-defs ℂ

  is-prd⇒is-wprd : {sp : span} → is-product sp → is-wproduct sp
  is-prd⇒is-wprd is× = record
    { w<_,_> = <_,_>
    ; w×tr₁ = ×tr₁
    ; w×tr₂ = ×tr₂
    }
    where open is-product is×


  prdsp⇒wprdsp : bin-product → bin-wproduct
  prdsp⇒wprdsp prdsp = mkw× {w×sp = ×sp} (is-prd⇒is-wprd ×isprd)
                    where open bin-product prdsp


  prd-of⇒wprd-of : {O1 O2 : Obj} → product-of O1 O2 → wproduct-of O1 O2
  prd-of⇒wprd-of prdof = mkw×of {w×sp/ = ×sp/} (is-prd⇒is-wprd ×isprd)
                      where open product-of prdof

-- end bin-product→bin-weak-product


has-prd⇒has-wprd : {ℂ : ecategory} → has-bin-products ℂ → has-bin-weak-products ℂ
has-prd⇒has-wprd {ℂ} has-prd = record
  { wprd-of = λ A B → prd-of⇒wprd-of (prd-of A B)
  }
  where open bin-product→bin-weak-product ℂ
        open has-bin-products has-prd
