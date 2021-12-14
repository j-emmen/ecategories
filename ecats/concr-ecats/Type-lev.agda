
{-# OPTIONS --without-K #-}

module ecats.concr-ecats.Type-lev where

open import tt-basics.id-type public
open import tt-basics.setoids using (setoid)
open import ecats.basic-defs.ecat-def&not

-- The ecategory of types at each universe level

module Type-lev-defs (ℓ : Level) where
  TypeHom : (X Y : Set ℓ) → setoid {ℓ} {ℓ}
  TypeHom X Y = record
    { object = X → Y
    ; _∼_ = λ f f' → (x : X) → f x == f' x
    ; istteqrel = record
      { refl = λ f x → =rf
      ; sym = λ p x → =sym (p x)
      ; tra = λ p q x → =tra (p x) (q x)
      }
    }
-- end Type-lev-defs

Typeₗₑᵥ : (ℓ : Level) → ecategoryₗₑᵥ (sucₗₑᵥ ℓ) ℓ ℓ
Typeₗₑᵥ ℓ = record
         { Obj = Set ℓ
         ; Hom = TypeHom ℓ
         ; isecat = record
                  { _∘_ = λ g f → λ x → g (f x)
                  ; idar = λ X x → x
                  ; ∘ext = λ f f' g g' p q x → =tra (=ap g (p x)) (q (f' x))
                  ; lidax = λ f x → =rf
                  ; ridax = λ f x → =rf
                  ; assoc = λ f g h x → =rf
                  }
         }
         where open Type-lev-defs

module Typeₗₑᵥ (ℓ : Level) = ecat (Typeₗₑᵥ ℓ)


-- The ecategory of small types

Type : ecategory
Type = Typeₗₑᵥ 0ₗₑᵥ
