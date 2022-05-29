
{-# OPTIONS --without-K #-}

module ecats.basic-defs.commut-shapes where

open import ecats.basic-defs.ecat-def&not

module comm-shapes (ℂ : ecategory) where
  open ecategory-aux ℂ

  record span/ (O1 O2 : Obj) : Set₁ where
    constructor mkspan/
    field
      {O12} : Obj
      a1 : || Hom O12 O1 ||
      a2 : || Hom O12 O2 ||

  record span/-mor {O1 O2 : Obj} (spD spC : span/ O1 O2) : Set₀ where
    private
      module spD = span/ spD
      module spC = span/ spC
    field
      ar : || Hom spD.O12 spC.O12 ||
      tr₁ : spC.a1 ∘ ar ~ spD.a1
      tr₂ : spC.a2 ∘ ar ~ spD.a2


  record span : Set₁ where
    constructor mkspan-c
    field
      {O1} {O2} : Obj
      sp/ : span/ O1 O2
    open span/ sp/ public

  mkspan : {O1 O2 O12 : Obj} → || Hom O12 O1 || → || Hom O12 O2 || → span
  mkspan a1 a2 = mkspan-c (mkspan/ a1 a2)

  _²¹ : {O1 O2 : Obj} → span/ O1 O2 → span/ O2 O1
  _²¹ sp/ = mkspan/ a2 a1
          where open span/ sp/


  record cospan/ (O1 O2 : Obj) : Set₁ where
    constructor mkcospan/
    field
      {O12} : Obj
      a1 : || Hom O1 O12 ||
      a2 : || Hom O2 O12 ||

  record cospan : Set₁ where
    constructor mkcospan
    field
      {O1} {O2} : Obj
      cosp/ : cospan/ O1 O2
    open cospan/ cosp/ public


  record comm-triang : Set₁ where
    constructor mktriang
    field
      {O1} {O2} {O3} : Obj
      {a13} : || Hom O1 O3 ||
      {a12} : || Hom O1 O2 ||
      {a23} : || Hom O2 O3 ||
      pftr : a23 ∘ a12 ~ a13


  record square/cosp {dl dr ur : Obj}
                     (down : || Hom dl dr ||) (right : || Hom ur dr ||) : Set₁
                     where
    constructor mksq/
    field
      {upleft} : span/ dl ur
    open span/ upleft renaming (O12 to ul; a1 to left; a2 to up) public
    field
      sq-pf : down ∘ left ~ right ∘ up

  record comm-square : Set₁ where
    constructor mksq
    field
      {dl} {ur} {dr} : Obj
      {down} : || Hom dl dr ||
      {right} : || Hom ur dr ||
      sq/ : square/cosp down right
    open square/cosp sq/ public
    {-
      {ul} {dl} {ur} {dr} : Obj
      {left} : || Hom ul dl ||
      {up} : || Hom ul ur ||
      {down} : || Hom dl dr ||
      {right} : || Hom ur dr ||
      pfsq : down ∘ left ~ right ∘ up
    -}

{-
  sq/cosp2sq : {dl dr ur : Obj} {down : || Hom dl dr ||} {right : || Hom ur dr ||} → square/cosp down right → comm-square
  sq/cosp2sq sq/cosp = mksq sq-pf
                       where open square/cosp sq/cosp
-}

  sq-ext : {dl dr ur : Obj} {down down' : || Hom dl dr ||}{right right' : || Hom ur dr ||}
              → square/cosp down right → down ~ down' → right ~ right'
                → square/cosp down' right'
  sq-ext sq/ pfd pfr = mksq/ (∘e r (pfd ˢ) ⊙ sq-pf ⊙ ∘e r pfr)
                     where open square/cosp sq/


  diag-sym-square : comm-square → comm-square
  diag-sym-square sq = mksq (mksq/ (sq-pf ˢ))
                     where open comm-square sq

-- end comm-shapes
