
{-# OPTIONS --without-K #-}

module ecats.constructions.opposite where

open import Agda.Primitive
open import tt-basics.setoids using (setoid)
open import ecats.basic-defs.ecat-def&not

is-ecat-op : {ℓ ℓ' : Level}{Obj : Set ℓ}{Hom : Obj → Obj → setoid {ℓ'}}
         → is-ecategory Obj Hom → is-ecategory Obj (λ x y → Hom y x)
is-ecat-op isecat = record
  { _∘_ = λ g f → f ∘ g
  ; idar = idar
  ; ∘ext = λ f f' g g' pff pfg → ∘ext g g' f f' pfg pff
  ; lidax = ridax
  ; ridax = lidax
  ; assoc = λ f g h → assˢ
  }
  where open is-ecategory isecat
        open ecategory-aux-level isecat using (assˢ)

op-small : small-ecategory → small-ecategory
op-small ℂ = record
  { Obj = Obj
  ; Hom = λ x y → Hom y x
  ; isecat = is-ecat-op isecat
  }
  where open small-ecategory ℂ using (Obj; Hom; isecat)

op-locsmall : ecategory → ecategory
op-locsmall ℂ = record
  { Obj = Obj
  ; Hom = λ x y → Hom y x
  ; isecat = is-ecat-op isecat
  }
  where open ecategory ℂ using (Obj; Hom; isecat)

_ᵒᵖ : ecategory → ecategory
_ᵒᵖ = op-locsmall
