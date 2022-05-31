
{-# OPTIONS --without-K #-}

module ecats.basic-defs.preorder where

open import ecats.basic-defs.ecat-def&not


record is-preorder {ℓ₁ ℓ₂ ℓ₃ : Level}(ℂ : ecategoryₗₑᵥ ℓ₁ ℓ₂ ℓ₃) : Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃) where
  open ecat ℂ
  field
    pf : {X Y : Obj}{f f' : || Hom X Y ||} → f ~ f'


record preorder (ℓ₁ ℓ₂ ℓ₃ : Level) : Set (sucₗₑᵥ (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃)) where
  field
    ℂ : ecategoryₗₑᵥ ℓ₁ ℓ₂ ℓ₃
    ispreord : is-preorder ℂ
  module ispreord = is-preorder ispreord

small-preorder : Set₁
small-preorder = preorder 0ₗₑᵥ 0ₗₑᵥ 0ₗₑᵥ
