 
{-# OPTIONS --without-K #-}

module ecats.finite-limits.defs.pullback where

open import ecats.basic-defs.ecat-def&not
open import ecats.basic-defs.commut-shapes




-- Pullbacks

module pullback-defs (ℂ : ecategory) where
  open ecategory-aux ℂ
  open comm-shapes ℂ
  --open wpbsquare-defs ℂ
  
  record is-pb-square (sq : comm-square) : Set₁ where
    open comm-square sq
    field
      ⟨_,_⟩[_] : {C : Obj} (h : || Hom C dl ||) (k : || Hom C ur ||)
                    → down ∘ h ~ right ∘ k → || Hom C ul ||
      ×/tr₁ : {C : Obj} {h : || Hom C dl ||} {k : || Hom C ur ||} (pf : down ∘ h ~ right ∘ k)
                  → left ∘ ⟨ h , k ⟩[ pf ] ~ h
      ×/tr₂ : {C : Obj} {h : || Hom C dl ||} {k : || Hom C ur ||} (pf : down ∘ h ~ right ∘ k)
                  → up ∘ ⟨ h , k ⟩[ pf ] ~ k
      ×/uq : {C : Obj} → {h h' : || Hom C ul ||} → left ∘ h ~ left ∘ h' → up ∘ h ~ up ∘ h'
                    → h ~ h'           
{-    field
      wpbsq : is-wpb-square sq
    open is-wpb-square wpbsq public renaming (ul-w/ to ul/; ur-w/ to ur/; dl-w/ to dl/; dr-w/ to dr/;
                                             left-w/ to left/; down-w/ to down/; up-w/ to up/; right-w/ to right/;
                                             wpbpfsq to pbpfsq;
                                             wpbuniv to pbuniv; wpbaxcommuniv1 to pbaxcommuniv1;
                                             wpbaxcommuniv2 to pbaxcommuniv2)
    field
      pbaxuniq : {A : Obj} → (h h' : || Hom A ul/ ||) → left/ ∘ h ~ left/ ∘ h' → up/ ∘ h ~ up/ ∘ h'
                    → h ~ h'
-}



  record pb-square : Set₁ where
    constructor mkpb-sq
    field
      {×/sq} : comm-square
      ×/ispbsq : is-pb-square ×/sq
    open comm-square ×/sq renaming (left to π/₁; up to π/₂; sq-pf to ×/sqpf) public
    open is-pb-square ×/ispbsq public
{-
    open comm-square sq
    dr/ = dr
    dl/ = dl
    ur/ = ur
    ul/ = ul
    down/ = down
    left/ = left
    up/ = up
    right/ = right

  mkpbsq : {sq : comm-square} → is-pb-square sq → pb-square
  mkpbsq {sq} sqispb  = record { sq = sq
                               ; sq-is-pb = sqispb }
-}


  record pullback-of {I A B : Obj} (a : || Hom A I ||) (b : || Hom B I ||) : Set₁ where
    constructor mkpb-of
    field
      {×/sq/} : square/cosp a b
      ×/ispbsq : is-pb-square (mksq ×/sq/)
    open square/cosp ×/sq/ renaming (left to π/₁; up to π/₂; sq-pf to ×/sqpf) public
    open is-pb-square ×/ispbsq public
    

{-
  -- preservation of property under pullback

  record is-pbsq-stable (Prop : {X Y : Obj} → || Hom X Y || → Set₁) : Set₁ where
    open pb-square
    field
      pres-rl : (pbsq : pb-square) → Prop (right pbsq) → Prop (π/₁ pbsq)
    pres-du : (pbsq : pb-square) → Prop (down pbsq) → Prop (π/₂ pbsq)
    pres-du pbsq pf = pres-rl (mkpb-sq (diag-sym-pb-sq (×/ispbsq pbsq))) pf
-}

-- end pullback-defs


record has-pullbacks (ℂ : ecategory) : Set₁ where
  constructor mkhas-pb
  open ecategory-aux ℂ
  open comm-shapes ℂ
  open pullback-defs ℂ
  field
    pb-of : {I A B : Obj} → (a : || Hom A I ||) → (b : || Hom B I ||) → pullback-of a b
  module pb-of {I A B : Obj} {a : || Hom A I ||} {b : || Hom B I ||} = pullback-of (pb-of a b)
  open pb-of public
  _×/ₒ_ : {I A B : Obj} → (a : || Hom A I ||) → (b : || Hom B I ||) → Obj
  a ×/ₒ b = ul {a = a} {b}
