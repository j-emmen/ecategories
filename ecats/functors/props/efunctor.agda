
{-# OPTIONS --without-K #-}

module ecats.functors.props.efunctor where

open import ecats.basic-defs.ecat-def&not
open import ecats.isomorphism
open import ecats.functors.defs.efunctor-d&n
open import ecats.functors.defs.natural-iso

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

  pres≅ₒ : {A B : ℂ.Obj} → A ℂ.≅ₒ B → (F.ₒ A) 𝔻.≅ₒ (F.ₒ B)
  pres≅ₒ iso = record
    { a12 = F.ₐ a12
    ; a21 = F.ₐ a21
    ; isop = pres-iso-pair isop
    }
    where open ℂ._≅ₒ_ iso

-- end efunctor-lev-props


module ≅ₐ2≅ₒ-defs {ℓ₁ ℓ₂ ℓ₃ : Level}{ℂ : ecategoryₗₑᵥ ℓ₁ ℓ₂ ℓ₃}
                  {ℓ₄ ℓ₅ ℓ₆ : Level}{𝔻 : ecategoryₗₑᵥ ℓ₄ ℓ₅ ℓ₆}
                  (F G : efunctorₗₑᵥ ℂ 𝔻)
                  where
  private
    module ℂ = ecat ℂ
    module 𝔻 = iso-d&p 𝔻
    module F = efctr F
    module G = efctr G
  ≅ₐ2≅ₒ : F ≅ₐ G → {X : ℂ.Obj} → F.ₒ X 𝔻.≅ₒ G.ₒ X
  ≅ₐ2≅ₒ natiso {X} = record
    { a12 = F≅G.fnc {X}
    ; a21 = F≅G.fnc⁻¹ {X}
    ; isop = F≅G.isiso {X}
    }
    where module F≅G = natural-iso natiso
-- end ≅ₐ2≅ₒ-defs
--open ≅ₐ2≅ₒ-defs public
private module tmp {ℓ₁ ℓ₂ ℓ₃ : Level}{ℂ : ecategoryₗₑᵥ ℓ₁ ℓ₂ ℓ₃}
                   {ℓ₄ ℓ₅ ℓ₆ : Level}{𝔻 : ecategoryₗₑᵥ ℓ₄ ℓ₅ ℓ₆}
                   {F G : efunctorₗₑᵥ ℂ 𝔻}
                   = ≅ₐ2≅ₒ-defs F G
open tmp public
