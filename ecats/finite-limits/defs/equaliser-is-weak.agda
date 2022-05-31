
{-# OPTIONS --without-K #-}

module ecats.finite-limits.defs.equaliser-is-weak where

open import ecats.basic-defs.ecat-def&not
open import ecats.finite-limits.defs.weak-equaliser
open import ecats.finite-limits.defs.equaliser


module equaliser→weak-equaliser (ℂ : ecategory) where
  open ecategory ℂ
  open wequaliser-defs ℂ
  open equaliser-defs ℂ



  is-eql⇒is-weql : {A B E : Obj} {f f' : || Hom A B ||} {e : || Hom E A ||} {pfeq : f ∘ e ~ f' ∘ e}
                      → is-equaliser pfeq → is-wequaliser pfeq
  is-eql⇒is-weql iseql = record
    { _|w[_] = _|[_]
    ; wtr = tr
    }
    where open is-equaliser iseql


  eql-of⇒weql-of : {A B : Obj} {f f' : || Hom A B ||}
                      → equaliser-of f f' → wequaliser-of f f'
  eql-of⇒weql-of eqlof = mkweql-of (is-eql⇒is-weql iseql)
                        where open equaliser-of eqlof

-- end equaliser→weak-equaliser



has-eql⇒has-weql : {ℂ : ecategory} → has-equalisers ℂ → has-weak-equalisers ℂ
has-eql⇒has-weql {ℂ} eqlC = record
                           { weql-of = λ f f' → eql-of⇒weql-of (eql-of f f')
                           }
                           where open equaliser-defs ℂ
                                 open has-equalisers eqlC
                                 open equaliser→weak-equaliser ℂ
