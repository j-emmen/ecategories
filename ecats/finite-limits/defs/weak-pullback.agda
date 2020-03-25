 
-- disable the K axiom:

{-# OPTIONS --without-K #-}

-- Agda version 2.5.4.1

module ecats.finite-limits.defs.weak-pullback where

open import ecats.basic-defs.ecat-def&not
open import ecats.basic-defs.commut-shapes





-- Weak Pullbacks

module wpullback-defs (ℂ : ecategory) where
  open ecategory-aux ℂ
  open comm-shapes ℂ


  record is-wpb-square (sq : comm-square) : Set₁ where
    --constructor mkis-wpb
    open comm-square sq {-public renaming (ul to ul-w/; ur to ur-w/; dl to dl-w/; dr to dr-w/;
                                        left to left-w/; down to down-w/; up to up-w/; right to right-w/;
                                        sq-pf to wpbpfsq)-}
    field
      w⟨_,_⟩[_] : {C : Obj} (h : || Hom C dl ||) (k : || Hom C ur ||) → down ∘ h ~ right ∘ k
                     → || Hom C ul ||
      w×/tr₁ : {C : Obj} {h : || Hom C dl ||} {k : || Hom C ur ||} (pf : down ∘ h ~ right ∘ k)
                  → left ∘ w⟨ h , k ⟩[ pf ] ~ h
      w×/tr₂ : {C : Obj} {h : || Hom C dl ||} {k : || Hom C ur ||} (pf : down ∘ h ~ right ∘ k)
                  → up ∘ w⟨ h , k ⟩[ pf ] ~ k


  record wpullback-sq : Set₁ where
    constructor mkwpb-sq
    field
      {w×/sq} : comm-square
      w×/iswpbsq : is-wpb-square w×/sq
    open comm-square w×/sq renaming (left to wπ/₁; up to wπ/₂; sq-pf to w×/sqpf) public
    open is-wpb-square w×/iswpbsq public


  record wpullback-of {I A B} (a : || Hom A I ||) (b : || Hom B I ||) : Set₁ where
    constructor mkwpb-of
    field
      {w×/sq/} : square/cosp a b
      w×/iswpbsq : is-wpb-square (mksq w×/sq/)
    open square/cosp w×/sq/ renaming (left to wπ/₁; up to wπ/₂; sq-pf to w×/sqpf) public
    open is-wpb-square w×/iswpbsq public
    wpbsq : wpullback-sq
    wpbsq = mkwpb-sq w×/iswpbsq

-- end wpullback-defs


record has-weak-pullbacks (ℂ : ecategory) : Set₁ where
  constructor mkhas-wpb
  open ecategory-aux ℂ
  open comm-shapes ℂ
  open wpullback-defs ℂ
  field
    wpb-of : {I A B : Obj} → (a : || Hom A I ||) → (b : || Hom B I ||) → wpullback-of a b
  module wpb-of {I A B : Obj} {a : || Hom A I ||} {b : || Hom B I ||} = wpullback-of (wpb-of a b)
  open wpb-of public
  _w×/ₒ_ : {I A B : Obj} → (a : || Hom A I ||) → (b : || Hom B I ||) → Obj
  a w×/ₒ b = ul {a = a} {b}
