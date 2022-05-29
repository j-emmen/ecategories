
{-# OPTIONS --without-K #-}

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

  pfeq-irr : {A B E : Obj} {f g : || Hom A B ||} {e : || Hom E A ||}
             {pfeq : f ∘ e ~ g ∘ e}(iseql : is-equaliser pfeq)
             (pfeq' : f ∘ e ~ g ∘ e) → is-equaliser pfeq'
  pfeq-irr {pfeq = pfeq} iseql pfeq' = record
    { _|eql[_] = _|eql[_]
    ; eqltr = eqltr
    ; eqluq = eqluq
    }
    where open is-equaliser iseql

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


  ar≅eqlar-is-eql : {A B E : Obj} {f f' : || Hom A B ||}{e : || Hom E A ||}{pfeq : f ∘ e ~ f' ∘ e}
                    (iseql : is-equaliser pfeq){E' : Obj}{e' : || Hom E' A ||}(pfeq' : f ∘ e' ~ f' ∘ e')
                    {uar : || Hom E' E ||} → e ∘ uar ~ e' → is-iso uar →  is-equaliser pfeq'
  ar≅eqlar-is-eql {f = f} {f'} {e} {pfeq} iseql {E'} {e'} pfeq' {uar} trar isoar = record
    { _|eql[_] = λ h pf → uar.invf ∘ h |eql[ pf ]
    ; eqltr = λ {_} {h} pf → ~proof
            e' ∘ uar.invf ∘ h |eql[ pf ]            ~[ ass ⊙ ∘e r (∘e r trar ˢ ⊙ assˢ) ] /
            (e ∘  uar ∘ uar.invf) ∘ h |eql[ pf ]    ~[ ∘e r (ridgg r uar.idcod) ] /
            e ∘ h |eql[ pf ]                       ~[ eqltr pf ]∎
            h ∎
    ; eqluq = λ {_} {h} {h'} pf → ~proof
            h                       ~[ lidggˢ r uar.iddom ⊙ assˢ ] /
            uar.invf ∘ uar ∘ h       ~[ ∘e (uq-aux pf) r ] /
            uar.invf ∘ uar ∘ h'      ~[ ass ⊙ lidgg r uar.iddom ]∎
            h' ∎
    }
    where open is-equaliser iseql
          module uar = is-iso isoar
          uq-aux : {C : Obj}{h : || Hom C E' ||} {h' : || Hom C E' ||}
                      → e' ∘ h ~ e' ∘ h' → uar ∘ h ~ uar ∘ h'
          uq-aux {_} {h} {h'} pf = eqluq (~proof
            e ∘ uar ∘ h              ~[ ass ⊙ ∘e r trar ] /
            e' ∘ h                   ~[ pf ] /
            e' ∘ h'                  ~[ ∘e r (trar ˢ) ⊙ assˢ ]∎
            e ∘ uar ∘ h' ∎)


  eqls-unv-is-iso : {A B E E' : Obj} {f f' : || Hom A B ||}{e : || Hom E A ||}{e' : || Hom E' A ||}
                    {pfeq : f ∘ e ~ f' ∘ e}{pfeq' : f ∘ e' ~ f' ∘ e'}
                    (iseql : is-equaliser pfeq)(iseql' : is-equaliser pfeq')
                    {uar : || Hom E' E ||} → e ∘ uar ~ e' → is-iso uar
  eqls-unv-is-iso {f = f} {f'} {e} {e'} {pfeq} {pfeq'} iseql iseql' {uar} trar = record
    { invf = e eql'.|eql[ pfeq ]
    ; isisopair = record
                { iddom = eql'.eqluq (~proof
                        e' ∘ (e eql'.|eql[ pfeq ]) ∘ uar     ~[ ass ⊙ ∘e r (eql'.eqltr pfeq) ] /
                        e  ∘ uar                             ~[ ridgenˢ trar ]∎
                        e' ∘ idar _ ∎)
                ; idcod = eql.eqluq (~proof
                        e ∘ uar ∘ e eql'.|eql[ pfeq ]        ~[ ass ⊙ ∘e r trar ] /
                        e'  ∘ e eql'.|eql[ pfeq ]            ~[ ridgenˢ (eql'.eqltr pfeq) ]∎
                        e ∘ idar _ ∎)
                }
    }
    where module eql = is-equaliser iseql
          module eql' = is-equaliser iseql'


  eqlar-mono : {A B E : Obj} {f g : || Hom A B ||} {e : || Hom E A ||}
               {pfeq : f ∘ e ~ g ∘ e} → is-equaliser pfeq → is-monic e
  eqlar-mono iseql = record { mono-pf = eqluq }
                   where open is-equaliser iseql
-- end equaliser-props
