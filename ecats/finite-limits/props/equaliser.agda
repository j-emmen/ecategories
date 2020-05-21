 
-- disable the K axiom:

{-# OPTIONS --without-K #-}

-- Agda version 2.5.4.1

module ecats.finite-limits.props.equaliser where

open import ecats.basic-defs.ecat-def&not
open import ecats.basic-defs.commut-shapes
open import ecats.basic-defs.isomorphism
open import ecats.basic-defs.epi&mono
open import ecats.finite-limits.defs.equaliser





module equaliser-props (ℂ : ecategory) where
  open ecategory-aux ℂ
  open iso-defs ℂ
  open epis&monos-defs ℂ
  open comm-shapes ℂ
  open equaliser-defs ℂ

  iseql-ext : {A B E : Obj} {f f' g g' : || Hom A B ||} {e : || Hom E A ||}
              {pfeq : f ∘ e ~ g ∘ e} (pfeq' : f' ∘ e ~ g' ∘ e)
                 → f ~ f' → g ~ g' → is-equaliser pfeq
                   → is-equaliser pfeq'
  iseql-ext {A} {f = f} {f'} {g} {g'} {e} {pfeq} pfeq' pff pfg eql = record
    { _|eql[_] = λ h pf → h |eql[ eq' pf ]
    ; eqltr = λ pf → eqltr (eq' pf)
    ; eqluq = eqluq
    }
    where open is-equaliser eql
          eq' : {C : Obj} {h : || Hom C A ||} → f' ∘ h ~ g' ∘ h → f ∘ h ~ g ∘ h
          eq' pf = ∘e r pff ⊙ pf ⊙ ∘e r (pfg ˢ)


  eqlar-ext : {A B E : Obj} {f g : || Hom A B ||} {e e' : || Hom E A ||}
              {pfeq : f ∘ e ~ g ∘ e} (pfeq' : f ∘ e' ~ g ∘ e')
                → e ~ e' → is-equaliser pfeq
                  → is-equaliser pfeq'
  eqlar-ext {A} {f = f} {g} {e} {e'} {pfeq} pfeq' pfe eql = record
    { _|eql[_] = _|eql[_]
    ; eqltr = λ pf → ∘e r (pfe ˢ) ⊙ eqltr pf
    ; eqluq = λ pf → eqluq (∘e r pfe ⊙ pf ⊙ ∘e r (pfe ˢ))
    }
    where open is-equaliser eql

  eqlof-ext : {A B E : Obj} {f f' g g' : || Hom A B ||}
                 → f ~ f' → g ~ g' → equaliser-of f g
                   → equaliser-of f' g'
  eqlof-ext pff pfg eqlof = record
    { Eql = Eql
    ; eqlar = eqlar
    ; eqleq = ∘e r (pff ˢ) ⊙ eqleq ⊙ ∘e r pfg
    ; iseql = iseql-ext (∘e r (pff ˢ) ⊙ eqleq ⊙ ∘e r pfg) pff pfg iseql
    }
    where open equaliser-of eqlof

-- end equaliser-props
