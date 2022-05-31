
{-# OPTIONS --without-K #-}

module ecats.concr-ecats.Std-lev where

open import tt-basics.setoids renaming (||_|| to ||_||std)
open import ecats.basic-defs.ecat-def&not

-- The ecategory of setoids at each universe level

Stdₗₑᵥ : (ℓo ℓr : Level) → ecategoryₗₑᵥ (sucₗₑᵥ (ℓo ⊔ ℓr)) (ℓo ⊔ ℓr) (ℓo ⊔ ℓr)
Stdₗₑᵥ ℓo ℓr = record
         { Obj = setoid {ℓo} {ℓr}
         ; Hom = setoidmaps {ℓo} {ℓr} {ℓo} {ℓr}
         ; isecat = record
                  { _∘_ = std-cmp {ℓo} {ℓr} {ℓo} {ℓr} {ℓo} {ℓr}
                  ; idar = λ A → std-id {A = A}
                  ; ∘ext = λ f f' g g' pff pfg → std-cmp-ext g g' f f' pfg pff
                  ; lidax = λ {_} {B} f x → std.r B
                  ; ridax = λ {_} {B} f x → std.r B
                  ; assoc = λ {_} {_} {_} {D} f g h x → std.r D
                  }
         }
         where module std (A : setoid {ℓo} {ℓr}) = setoid-aux A

module Stdₗₑᵥ (ℓo ℓr : Level) = ecat (Stdₗₑᵥ ℓo ℓr)
module StdObj {ℓo ℓr}(A : ecat.Obj (Stdₗₑᵥ ℓo ℓr)) = setoid-aux A
module StdHom {ℓo ℓr}{A B : ecat.Obj (Stdₗₑᵥ ℓo ℓr)}(f : || ecat.Hom (Stdₗₑᵥ ℓo ℓr) A B ||)
  = setoidmap f renaming (op to ap)


-- The ecategory of small setoids

Std : ecategory
Std = Stdₗₑᵥ 0ₗₑᵥ 0ₗₑᵥ
