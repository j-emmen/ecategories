 
-- disable the K axiom:

{-# OPTIONS --without-K #-}

-- Agda version 2.5.4.1



-- This module defines the category of small setoids and proves some of its properties

module ecats.concr-ecats.Std where

open import basics
open import id-type
open import setoids
open import ecats.basic-defs.ecat-def&not
open import ecats.basic-defs.commut-shapes
open import ecats.finite-limits.defs&not
open import ecats.finite-limits.props.relations-among-limits



                       
Std : ecategory
Std = record
         { Obj = setoid
         ; Hom = setoidmaps
         ; isecat = record
                  { _∘_ = std-cmp
                  ; idar = λ A → std-id {A}
                  ; ∘ext = λ f f' g g' pff pfg → std-cmp-ext g g' f f' pfg pff
                  ; lid = λ {_} {B} f x → std.r B
                  ; rid = λ {_} {B} f x → std.r B
                  ; assoc = λ {_} {_} {_} {D} f g h x → std.r D
                  }
         }
         where module std (A : setoid) = setoid-aux A


open ecategory-aux Std
open comm-shapes Std


-- Std has finite limits



trm-Std : has-terminal Std
trm-Std = record
  { trmOb = Freestd N₁
  ; istrm = record
          { ! =  λ _ → record { op = λ _ → 0₁
                               ; ext = λ _ → =rf }
          ; !uniq = λ f x → contr= (N₁-isContr) (ap f x)
          }
  }
  where module std (A : setoid) = setoid-aux A



prd-Std : has-bin-products Std
prd-Std = {!!}


eql-Std : has-equalisers Std
eql-Std = {!!}


pb-Std : has-pullbacks Std
pb-Std = {!!} --has-prd+eql⇒has-pb prd-Std eql-Std
