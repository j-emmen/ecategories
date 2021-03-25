 

{-# OPTIONS --without-K #-}

module ecats.basic-defs.opposite where

open import ecats.basic-defs.ecat-def&not
open import tt-basics.id-type

_ᵒᵖ : ecategory → ecategory
_ᵒᵖ ℂ = record
  { Obj = Obj
  ; Hom = λ X Y → Hom Y X
  ; isecat = record
           { _∘_ = λ f g → g ∘ f
           ; idar = idar
           ; ∘ext = λ f f' g g' pff pfg → ∘e pfg pff 
           ; lidax = ridax
           ; ridax = lidax
           ; assoc = λ f g h → assˢ
           }
  }
  where open ecategory-aux ℂ
