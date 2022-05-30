
{-# OPTIONS --without-K #-}

module ecats.finite-limits.props.equaliser where

open import ecats.basic-defs.ecat-def&not
open import ecats.basic-defs.commut-shapes
open import ecats.basic-defs.isomorphism
open import ecats.basic-defs.epi&mono
open import ecats.basic-props.isomorphism
open import ecats.basic-props.epi&mono-basic
open import ecats.finite-limits.defs.equaliser





module equaliser-props (ℂ : ecategory) where
  open ecategory-aux ℂ
  open iso-defs ℂ
  open iso-props ℂ
  open epi&mono-defs ℂ
  open epi&mono-props ℂ
  open comm-shapes ℂ
  open equaliser-defs ℂ

  iseql-ext : {A B E : Obj} {f f' g g' : || Hom A B ||} {e : || Hom E A ||}
              {pfeq : f ∘ e ~ g ∘ e} (pfeq' : f' ∘ e ~ g' ∘ e)
                 → f ~ f' → g ~ g' → is-equaliser pfeq
                   → is-equaliser pfeq'
  iseql-ext {A} {f = f} {f'} {g} {g'} {e} {pfeq} pfeq' pff pfg eql = record
    { _|[_] = λ h pf → h |[ eq' pf ]
    ; tr = λ pf → tr (eq' pf)
    ; uq = uq
    }
    where open is-equaliser eql
          eq' : {C : Obj} {h : || Hom C A ||} → f' ∘ h ~ g' ∘ h → f ∘ h ~ g ∘ h
          eq' pf = ∘e r pff ⊙ pf ⊙ ∘e r (pfg ˢ)


  eqlar-ext : {A B E : Obj} {f g : || Hom A B ||} {e e' : || Hom E A ||}
              {pfeq : f ∘ e ~ g ∘ e} (pfeq' : f ∘ e' ~ g ∘ e')
                → e ~ e' → is-equaliser pfeq
                  → is-equaliser pfeq'
  eqlar-ext {A} {f = f} {g} {e} {e'} {pfeq} pfeq' pfe eql = record
    { _|[_] = _|[_]
    ; tr = λ pf → ∘e r (pfe ˢ) ⊙ tr pf
    ; uq = λ pf → uq (∘e r pfe ⊙ pf ⊙ ∘e r (pfe ˢ))
    }
    where open is-equaliser eql

  eqlof-ext : {A B E : Obj} {f f' g g' : || Hom A B ||}
                 → f ~ f' → g ~ g' → equaliser-of f g
                   → equaliser-of f' g'
  eqlof-ext pff pfg eqlof = record
    { Ob = Ob
    ; ar = ar
    ; eq = ∘e r (pff ˢ) ⊙ eq ⊙ ∘e r pfg
    ; iseql = iseql-ext (∘e r (pff ˢ) ⊙ eq ⊙ ∘e r pfg) pff pfg iseql
    }
    where open equaliser-of eqlof

  ar-iso-to-eql-is-eql : {A B E E' : Obj}{f g : || Hom A B ||}{e' : || Hom E' A ||}
                         (eq' : f ∘ e' ~ g ∘ e'){e : || Hom E A ||}{eq : f ∘ e ~ g ∘ e}
                         {med : || Hom E' E ||} → e ∘ med ~ e' → is-iso med
                              → is-equaliser eq → is-equaliser eq'
  ar-iso-to-eql-is-eql {A} {B} {E} {E'} {f} {g} {e'} eq' {e} {eq} {med} tr isiso iseql = record
    { _|[_] = λ h pf →  med.invf ∘ h eql.|[ pf ]
    ; tr = λ {_} {h} pf → ~proof e' ∘ med.invf ∘ h eql.|[ pf ]   ~[ ass ⊙ ∘e r (iso-trdom med.isisopair tr) ] /
                                  e ∘ h eql.|[ pf ]               ~[ eql.tr pf ]∎
                                  h ∎
    ; uq = f.mono-pf
    }
    where module eql = equaliser-of (mkeql-of iseql)
          module med = is-iso isiso
          fism : is-monic e'
          fism = ar-iso-to-mono-is-monic tr isiso (eqlof-is-monic (mkeql-of iseql))
          module f = is-monic fism
          

-- end equaliser-props
