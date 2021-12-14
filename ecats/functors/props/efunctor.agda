
{-# OPTIONS --without-K #-}

module ecats.functors.props.efunctor where

open import ecats.basic-defs.ecat-def&not
open import ecats.isomorphism
open import ecats.functors.defs.efunctor-d&n


module efunctor-lev-props {ℓ₁ₒ ℓ₁ₕ ℓ₁~}{ℂ : ecategoryₗₑᵥ ℓ₁ₒ ℓ₁ₕ ℓ₁~}
                          {ℓ₂ₒ ℓ₂ₕ ℓ₂~}{𝔻 : ecategoryₗₑᵥ ℓ₂ₒ ℓ₂ₕ ℓ₂~}
                          (F : efunctorₗₑᵥ ℂ 𝔻)
                          where
  private
    module ℂ where
      open ecat ℂ public
      open iso-d&p ℂ public
    module 𝔻 where
      open ecat 𝔻 public
      open iso-d&p 𝔻 public
    module F = efunctor-aux F

  pres-iso-pair : {A B : ℂ.Obj}{f : || ℂ.Hom A B ||}{invf : || ℂ.Hom B A ||}
                     → ℂ.is-iso-pair f invf → 𝔻.is-iso-pair (F.ₐ f) (F.ₐ invf)
  pres-iso-pair {f = f} {invf} isopair = record
    { iddom = F.∘ax iddom ⊙ F.id
    ; idcod = F.∘ax idcod ⊙ F.id
    }
    where open ℂ.is-iso-pair isopair
          open ecategory-aux 𝔻 using (_⊙_)

  pres-iso : {A B : ℂ.Obj} {f : || ℂ.Hom A B ||}
                 → ℂ.is-iso f → 𝔻.is-iso (F.ₐ f)
  pres-iso isof = record
    { invf = F.ₐ invf
    ; isisopair = pres-iso-pair isisopair
    }
    where open ℂ.is-iso isof

-- end efunctor-lev-props
