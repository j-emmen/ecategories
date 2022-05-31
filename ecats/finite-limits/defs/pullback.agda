
{-# OPTIONS --without-K #-}

module ecats.finite-limits.defs.pullback where

open import ecats.basic-defs.ecat-def&not
open import ecats.basic-defs.commut-shapes




-- Pullbacks

module pullback-defs (ℂ : ecategory) where
  open ecategory-aux ℂ
  open comm-shapes ℂ

  record is-pullback {I A B : Obj}{a : || Hom A I ||}{b : || Hom B I ||}
                     {P : Obj}{p : || Hom P A ||}{q : || Hom P B ||}
                     (sqpf : a ∘ p ~ b ∘ q) : Set₁ where
    field
      ⟨_,_⟩[_] : {C : Obj}(h : || Hom C A ||)(k : || Hom C B ||)
                    → a ∘ h ~ b ∘ k → || Hom C P ||
      ×/tr₁ : {C : Obj}{h : || Hom C A ||}{k : || Hom C B ||}(pf : a ∘ h ~ b ∘ k)
                  → p ∘ ⟨ h , k ⟩[ pf ] ~ h
      ×/tr₂ : {C : Obj}{h : || Hom C A ||}{k : || Hom C B ||}(pf : a ∘ h ~ b ∘ k)
                  → q ∘ ⟨ h , k ⟩[ pf ] ~ k
      ×/uq : {C : Obj}{h h' : || Hom C P ||}
                → p ∘ h ~ p ∘ h' → q ∘ h ~ q ∘ h' → h ~ h'


  record is-pullback-of {I A B : Obj}{a : || Hom A I ||}{b : || Hom B I ||}
                        (sq/ : square/cosp a b) : Set₁ where
    constructor mkis-pb-of
    open square/cosp sq/
    field
      ispb : is-pullback sq-pf
    open is-pullback ispb public


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

  pb-sq2is : {sq : comm-square} → is-pb-square sq → is-pullback (comm-square.sq-pf sq)
  pb-sq2is ispbsq = record
    { ⟨_,_⟩[_] = ⟨_,_⟩[_]
    ; ×/tr₁ = ×/tr₁
    ; ×/tr₂ = ×/tr₂
    ; ×/uq = ×/uq
    }
    where open is-pb-square ispbsq

  pb-is2sq : {I A B : Obj}{a : || Hom A I ||}{b : || Hom B I ||}
             {P : Obj}{p : || Hom P A ||}{q : || Hom P B ||}{sqpf : a ∘ p ~ b ∘ q}
               → is-pullback sqpf → is-pb-square (mksq (mksq/ sqpf))
  pb-is2sq ispb = record
    { ⟨_,_⟩[_] = ⟨_,_⟩[_]
    ; ×/tr₁ = ×/tr₁
    ; ×/tr₂ = ×/tr₂
    ; ×/uq = ×/uq
    }
    where open is-pullback ispb


  record pb-square : Set₁ where
    constructor mkpb-sq
    field
      {×/sq} : comm-square
      ×/ispbsq : is-pb-square ×/sq
    open comm-square ×/sq renaming (left to π/₁; up to π/₂; sq-pf to ×/sqpf) public
    open is-pb-square ×/ispbsq public


  record pullback-of {I A B : Obj}(a : || Hom A I ||)(b : || Hom B I ||) : Set₁ where
    constructor mkpb-of
    field
      {×/sq/} : square/cosp a b
      ×/ispbsq : is-pb-square (mksq ×/sq/)
    open square/cosp ×/sq/ renaming (left to π/₁; up to π/₂; sq-pf to ×/sqpf) public
    open is-pb-square ×/ispbsq public

  pbof-sq2is : {I A B : Obj}{a : || Hom A I ||}{b : || Hom B I ||}
               (pbof : pullback-of a b) → is-pullback-of (pullback-of.×/sq/ pbof)
  pbof-sq2is pbof = record
    { ispb = pb-sq2is ×/ispbsq
    }
    where open pullback-of pbof using (×/ispbsq)

  pbof-is2sq : {I A B : Obj}{a : || Hom A I ||}{b : || Hom B I ||}{sq/ : square/cosp a b}
                  → is-pullback-of sq/ → pullback-of a b
  pbof-is2sq {sq/ = sq/} ispbof = record
    { ×/sq/ = sq/
    ; ×/ispbsq = pb-is2sq ispb
    }
    where open is-pullback-of ispbof using (ispb)
    

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
