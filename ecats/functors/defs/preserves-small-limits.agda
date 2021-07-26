
{-# OPTIONS --without-K #-}

module ecats.functors.defs.preserves-small-limits where

open import Agda.Primitive
open import ecats.basic-defs.ecat-def&not
open import ecats.small-limits.defs.small-limit
open import ecats.functors.defs.efunctor-d&n
open import ecats.functors.defs.basic-defs


private
  module pres-lim-aux {ℓₒ ℓₐ ℓ~ : Level}(𝕏 : ecategoryₗₑᵥ ℓₒ ℓₐ ℓ~) where
    open ecat 𝕏 public
    open small-limit-defs 𝕏 public

record preserves-limits {ℓₒ₁ ℓₐ₁ ℓ~₁ : Level}{ℂ : ecategoryₗₑᵥ ℓₒ₁ ℓₐ₁ ℓ~₁}
                        {ℓₒ₂ ℓₐ₂ ℓ~₂ : Level}{𝔻 : ecategoryₗₑᵥ ℓₒ₂ ℓₐ₂ ℓ~₂}
                        (F : efunctorₗₑᵥ ℂ 𝔻)
                        : Set (1ₗₑᵥ ⊔ ecat.ℓₐₗₗ ℂ ⊔ ecat.ℓₐₗₗ 𝔻) where
  private
    module ℂ = small-limit-defs ℂ
    module 𝔻 = pres-lim-aux 𝔻
    module F = efctr F
  field
    pres-lim : {𝕀 : small-ecategory}(D : 𝕀 diag-in ℂ){C : Cone/.Obj D}
                  → ℂ.is-limit-cone C → 𝔻.is-limit-cone (Fcone F D C)
