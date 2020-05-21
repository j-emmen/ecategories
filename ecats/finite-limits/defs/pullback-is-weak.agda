 
-- disable the K axiom:

{-# OPTIONS --without-K #-}

-- Agda version 2.5.4.1

module ecats.finite-limits.defs.pullback-is-weak where

open import ecats.basic-defs.ecat-def&not
open import ecats.basic-defs.commut-shapes
open import ecats.finite-limits.defs.weak-pullback
open import ecats.finite-limits.defs.pullback


module pullback→weak-pullback (ℂ : ecategory) where
  open ecategory-aux ℂ
  open comm-shapes ℂ
  open pullback-defs ℂ
  open wpullback-defs ℂ


  is-pb⇒is-wpb : {sq : comm-square} → is-pb-square sq → is-wpb-square sq
  is-pb⇒is-wpb ispb = record
    { w⟨_,_⟩[_] = ⟨_,_⟩[_]
    ; w×/tr₁ = ×/tr₁
    ; w×/tr₂ = ×/tr₂
    }
    where open is-pb-square ispb


  pbsq⇒wpbsq : pb-square → wpullback-sq
  pbsq⇒wpbsq pbsq = mkwpb-sq (is-pb⇒is-wpb ×/ispbsq)
                  where open pb-square pbsq


  pbof⇒wpbof : {I A B : Obj} {a : || Hom A I ||} {b : || Hom B I ||}
                  → pullback-of a b → wpullback-of a b
  pbof⇒wpbof pbof = mkwpb-of (is-pb⇒is-wpb ×/ispbsq)
                  where open pullback-of pbof

-- end pullback→weak-pullback


has-pb⇒has-wpb : {ℂ : ecategory} → has-pullbacks ℂ → has-weak-pullbacks ℂ
has-pb⇒has-wpb {ℂ} haspb = mkhas-wpb λ a b → pbof⇒wpbof (pb-of a b)
                          where open pullback→weak-pullback ℂ
                                open has-pullbacks haspb
