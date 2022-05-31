
{-# OPTIONS --without-K #-}

module ecats.finite-limits.defs.weak-equaliser where

open import ecats.basic-defs.ecat-def&not
open import ecats.basic-defs.commut-shapes




-- Weak Equalisers

module wequaliser-defs (ℂ : ecategory) where
  open ecategory-aux ℂ

  record is-wequaliser {A B E : Obj} {f f' : || Hom A B ||} {e : || Hom E A ||}
                       (pfeq : f ∘ e ~ f' ∘ e) : Set₁ where
    --constructor mkis-weql
    field
      _|w[_] : {C : Obj} (h : || Hom C A ||) → f ∘ h ~ f' ∘ h → || Hom C E ||
      wtr : {C : Obj} {h : || Hom C A ||} (pf : f ∘ h ~ f' ∘ h)
               → e ∘ h |w[ pf ] ~ h

  record wequaliser-of {A B} (f f' : || Hom A B ||) : Set₁ where
    constructor mkweql-of
    field
      {wOb} : Obj
      {war} : || Hom wOb A ||
      {weq} : f ∘ war ~ f' ∘ war
      isweql : is-wequaliser weq
    open is-wequaliser isweql public
    
-- end wequaliser-defs


record has-weak-equalisers (ℂ : ecategory) : Set₁ where
  open ecategory-aux ℂ
  open wequaliser-defs ℂ
  field
    weql-of : {A B : Obj} (f f' : || Hom A B ||) → wequaliser-of f f'
  module weql-of {A B : Obj} {f f' : || Hom A B ||} = wequaliser-of (weql-of f f')
  open weql-of public
  w[_~_] : {A B : Obj} (f f' : || Hom A B ||) → Obj
  w[ f ~ f' ] = wOb {f = f} {f'}

{-
    weqob : {A B : Obj} → (f g : || Hom A B  ||) → Obj
    weqar : {A B : Obj} → (f g : || Hom A B  ||) → || Hom (weqob f g) A ||
    wequniv : {A B C : Obj} → (f g : || Hom A B  ||) → (h : || Hom C A ||) → < Hom C B > (f ∘ h) ~ (g ∘ h)
              → || Hom C (weqob f g) ||
    weqaxcommar : {A B : Obj} → (f g : || Hom A B  ||)
                  → < Hom (weqob f g) B > (f ∘ (weqar f g)) ~ (g ∘ (weqar f g))
    weqaxcommuniv : {A B C : Obj} → (f g : || Hom A B  ||)
                    → (h : || Hom C A ||) → (pf : < Hom C B > (f ∘ h) ~ (g ∘ h))
                      → < Hom C A > ((weqar f g) ∘ (wequniv f g h pf)) ~ h
-}
