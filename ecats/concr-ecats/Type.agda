 

{-# OPTIONS --without-K #-}

-- This module defines the category of small types and proves some of its properties

module ecats.concr-ecats.Type where

open import tt-basics.basics
open import tt-basics.id-type
open import tt-basics.setoids renaming (||_|| to ||_||std)
open import ecats.basic-defs.ecat-def&not
open import ecats.basic-defs.commut-shapes
open import ecats.basic-defs.isomorphism
open import ecats.basic-defs.generator
open import ecats.basic-defs.surjective
open import ecats.basic-defs.epi&mono
open import ecats.basic-props.epi&mono-basic
open import ecats.finite-limits.defs&not
open import ecats.finite-limits.props.relations-among-weak-limits


{-
infix 3 ||_||
||_|| : setoid → Set
||_|| X = ||_||std X
-}

TypeHom : (X Y : Set) → setoid
TypeHom X Y = record
  { object = X → Y
  ; _∼_ = λ f f' → (x : X) → f x == f' x
  ; istteqrel = record
    { refl = λ f x → =rf
    ; sym = λ p x → =sym (p x)
    ; tra = λ p q x → =tra (p x) (q x)
    }
  }
                       
Type : ecategory
Type = record
         { Obj = Set
         ; Hom = TypeHom
         ; isecat = record
                  { _∘_ = λ g f → λ x → g (f x)
                  ; idar = λ X x → x
                  ; ∘ext = λ f f' g g' p q x → =tra (=ap g (p x)) (q (f' x))
                  ; lidax = λ f x → =rf
                  ; ridax = λ f x → =rf
                  ; assoc = λ f g h x → =rf
                  }
         }

open ecategory-aux Type
open comm-shapes Type
open iso-defs Type
open epis&monos-defs Type



-- Type is quasi-cartesian

trm-Ty : has-terminal Type
trm-Ty = record
  { trmOb = N₁
  ; istrm = record
          { ! =  λ _ _ → 0₁
          ; !uniq = λ f x →  contr= (N₁-isContr) (f x)
          }
  }

open surjective-defs {Type} trm-Ty


prd-Ty : has-bin-products Type
prd-Ty = record
  { prd-of = λ A B → record
    { ×sp/ = mkspan/ prj1 prj2
    ; ×isprd = record
             { <_,_> = λ f g x → pair (f x) (g x)
             ; ×tr₁ = r
             ; ×tr₂ = r
             ; ×uq =  λ {_} {h} {h'} pf₁ pf₂ x →
                       =proof h x                               ==[ prdη⁻¹ (h x) ] /
                              pair (prj1 (h x)) (prj2 (h x))    ==[ =prdchar (pf₁ x) (pf₂ x) ] /
                              pair (prj1 (h' x)) (prj2 (h' x))  ==[ prdη (h' x) ]∎
                              h' x                              ∎
             }
    }
  }


weql-Ty : has-weak-equalisers Type
weql-Ty = record
  { weql-of = λ f f' → record
            { wEql = Σ _ (λ x → f x == f' x)
            ; weqlar = pj1
            ; weqleq = pj2
            ; isweql = record
                     { _|weql[_] = λ h pf → λ y → h y , pf y
                     ; weqltr = λ _ _ → =rf
                     }
            }
  }


wpb-Ty : has-weak-pullbacks Type
wpb-Ty = has-prd+weql⇒has-wpb prd-Ty weql-Ty


-- it may be worth to construct weak bows directly

wbw-Ty : has-weak-bows Type
wbw-Ty = has-weql+wpb⇒has-wbw weql-Ty wpb-Ty
{-record
  { wbw-of = λ sp₁ sp₂ → record
           { w×//sp = record
                    { O12 = {!!}
                    ; a1 = {!!}
                    ; a2 = {!!}
                    }
           ; is-wbw = record
                    { w×//⟨_,_⟩[_,_] = {!!}
                    ; w×//tr₁ = {!!}
                    ; w×//tr₂ = {!!}
                    }
           }
  }
-}

qcrt-Ty : is-quasi-cartesian Type
qcrt-Ty = record
  { hastrm = trm-Ty
  ; hasprd = prd-Ty
  ; hasweql = weql-Ty
  ; haswpb = wpb-Ty
  ; haswbw = wbw-Ty
  }


-- Elementality aka conservativity of the global section functor

module Type-is-elemental where
  glel : {A : Set} → A → || TypeHom N₁ A ||
  glel a = λ x → a
  tyel : {A : Set} → || TypeHom N₁ A || → A
  tyel a = a 0₁
  trmgen : terminal-is-generator trm-Ty
  trmgen = record { isgen  = λ H x → tyel (H (glel x)) }

  -- Every surjective function splits
  surj-splits : {A B : Set}{f : || TypeHom A B ||}
                  → is-surjective f → is-split-epi f
  surj-splits {A} {B} {f} issrj = record
    { rinv = λ b → tyel (srj.cntimg (glel b))
    ; rinv-ax = λ b → srj.cntimg-pf {glel b} 0₁
    }
    where module srj = is-surjective issrj
  monic-surj-is-iso : {A B : Obj} {f : || Hom A B ||} → is-monic f
                           → is-surjective f → is-iso f
  monic-surj-is-iso mon srj = monic-sepi-is-iso mon (surj-splits srj)
                            where open epis&monos-basic-props Type using (monic-sepi-is-iso)
-- end Type-is-elemental
open Type-is-elemental public






-- Equalisers imply UIP

module equalisers-imply-UIP (eql : has-equalisers Type) where
  module Type-eql = has-equalisers eql
  open equaliser-defs Type
  module eqlofel {A : Set} (a a' : A) = equaliser-of (Type-eql.eql-of (glel a) (glel a'))
  
  UIP-EqRel : {A : Set} → A → A → Set
  UIP-EqRel a a' = Type-eql.[ (glel a) ~ (glel a') ]

  UIP-ER→== : {A : Set} {a a' : A}
                  → UIP-EqRel a a' → a == a'
  UIP-ER→== {A} {a} {a'} = eqleq
                    where open eqlofel a a'

  UIP-ER-rf : {A : Set} (a : A) → UIP-EqRel a a
  UIP-ER-rf a = tyel (idar N₁ |eql[ r ])
              where open eqlofel a a

  UIP-ER-isprop : {A : Set} (a a' : A) → isProp (UIP-EqRel a a')
  UIP-ER-isprop a a' = λ e e' → eqluq {N₁} {glel e} {glel e'} (λ _ → isContr→isProp N₁-isContr _ _) 0₁
                     where open eqlofel a a'


  UIP-ER-pf : (A : Set) → UIP A
  UIP-ER-pf A = HoTT-Thm7-2-2 UIP-ER-rf UIP-ER-isprop (λ a a' → UIP-ER→== {A} {a} {a'})

-- end equalisers-imply-UIP



eql-Ty→UIP : has-equalisers Type → (A : Obj) → UIP A
eql-Ty→UIP eql = UIP-ER-pf
                where open equalisers-imply-UIP eql
