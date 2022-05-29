
{-# OPTIONS --without-K #-}

module ecats.finite-limits.defs.weak-Wlimit where

open import ecats.basic-defs.ecat-def&not
open import ecats.basic-defs.commut-shapes


-- weak limits of diagras shaped like W ( a span and two arrows).



module wWlim-defs (ℂ : ecategory) where
  open ecategory ℂ
  open comm-shapes ℂ
  --open span/
  private
    module sp = span/
  
  record is-wWlim {DL DR UL UR : Obj} {al : || Hom UL DL ||} {spc : span/ DL DR} {ar : || Hom UR DR ||}
                  {wW : Obj} {πl : || Hom wW UL ||} {πc : || Hom wW (sp.O12 spc) ||} {πr : || Hom wW UR ||}
                  (sqpfl : al ∘ πl ~ (sp.a1 spc) ∘ πc) (sqpfr : ar ∘ πr ~ (sp.a2 spc) ∘ πc) : Set₁
                  where
    open span/ spc renaming (O12 to UC; a1 to acl; a2 to acr)
    field
      ⟨_,_,_⟩[_,_] : {X : Obj} (gl : || Hom X UL ||) (gc : || Hom X UC ||) (gr : || Hom X UR ||)
                          → al ∘ gl ~ acl ∘ gc → ar ∘ gr ~ acr ∘ gc
                            → || Hom X wW ||
      trl : {X : Obj} {gl : || Hom X UL ||} {gc : || Hom X UC ||} {gr : || Hom X UR ||}
              (pfl : al ∘ gl ~ acl ∘ gc) (pfr : ar ∘ gr ~ acr ∘ gc)
                → πl ∘ ⟨ gl , gc , gr ⟩[ pfl , pfr ] ~ gl
      trc : {X : Obj} {gl : || Hom X UL ||} {gc : || Hom X UC ||} {gr : || Hom X UR ||}
              (pfl : al ∘ gl ~ acl ∘ gc) (pfr : ar ∘ gr ~ acr ∘ gc)
                → πc ∘ ⟨ gl , gc , gr ⟩[ pfl , pfr ] ~ gc
      trr : {X : Obj} {gl : || Hom X UL ||} {gc : || Hom X UC ||} {gr : || Hom X UR ||}
              (pfl : al ∘ gl ~ acl ∘ gc) (pfr : ar ∘ gr ~ acr ∘ gc)
                → πr ∘ ⟨ gl , gc , gr ⟩[ pfl , pfr ] ~ gr


  record wWlim-of {DL DR UL UR : Obj} (al : || Hom UL DL ||)
                  (spc : span/ DL DR) (ar : || Hom UR DR ||) : Set₁
                  where
    open span/ spc renaming (O12 to UC; a1 to acl; a2 to acr)
    open comm-shapes ℂ
    field
      wWOb : Obj
      πl : || Hom wWOb UL ||
      πc : || Hom wWOb UC ||
      πr : || Hom wWOb UR ||
      sqpfl : al ∘ πl ~ acl ∘ πc
      sqpfr : ar ∘ πr ~ acr ∘ πc
      iswWlim : is-wWlim sqpfl sqpfr
    open is-wWlim iswWlim public
-- end wWlim-defs

record has-weak-Wlimits (ℂ : ecategory) : Set₁ where
  open ecategory ℂ
  open comm-shapes ℂ
  open wWlim-defs ℂ
  field
    wW-of : {DL DR UL UR : Obj} (al : || Hom UL DL ||) (spc : span/ DL DR) (ar : || Hom UR DR ||)
              → wWlim-of al spc ar
  module wW-of {DL DR UL UR : Obj} (al : || Hom UL DL ||) (spc : span/ DL DR) (ar : || Hom UR DR ||) = wWlim-of (wW-of al spc ar)
