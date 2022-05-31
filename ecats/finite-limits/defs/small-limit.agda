
{-# OPTIONS --without-K #-}

module ecats.finite-limits.defs.small-limit where

open import Agda.Primitive using (Level;_⊔_)
open import ecats.basic-defs.ecat-def&not
open import ecats.basic-defs.commut-shapes
open import ecats.functors.defs.efunctor-d&n

module small-limit-defs {ℓₒ ℓₕ}(ℂ : ecategoryₗₑᵥ ℓₒ ℓₕ) where
  open ecat ℂ

  record cone/ {𝕁 : small-ecategory}(D : efunctorₗₑᵥ 𝕁 ℂ) : Set (ℓₒ ⊔ ℓₕ) where
    private
      module 𝕁 = small-ecategory 𝕁
      module D = efunctorₗₑᵥ D
    field
      Vx : Obj
      leg : (J : 𝕁.Obj) → || Hom Vx (D.ₒ J) ||
      tr : {J J' : 𝕁.Obj}(j : || 𝕁.Hom J J' ||) → D.ₐ j ∘ leg J ~ leg J'
    trˢ : {J J' : 𝕁.Obj}(j : || 𝕁.Hom J J' ||) → leg J' ~ D.ₐ j ∘ leg J
    trˢ j = tr j ˢ
          where open ecategory-aux-only ℂ using (_ˢ)

  record is-jointly-monic-cone/ {𝕁 : small-ecategory}{D : efunctorₗₑᵥ 𝕁 ℂ}
                                (mcn : cone/ D) : Set (ℓₒ ⊔ ℓₕ)
                                where
    private
      module 𝕁 = small-ecategory 𝕁
      module D = efunctorₗₑᵥ D
      module mcn = cone/ mcn
    field
      jm-pf : {A : Obj}{f f' : || Hom A mcn.Vx ||}
                 → ((J : 𝕁.Obj) → mcn.leg J ∘ f ~ mcn.leg J ∘ f')
                      → f ~ f'
    
  record is-universal-cone {𝕁 : small-ecategory}{D : efunctorₗₑᵥ 𝕁 ℂ}
                           (ucn : cone/ D) : Set (ℓₒ ⊔ ℓₕ)
                           where
    private
      module 𝕁 = small-ecategory 𝕁
      module D = efunctorₗₑᵥ D
      module ucn = cone/ ucn
      module cn = cone/
    field
      ar : (cn : cone/ D) → || Hom (cn.Vx cn) ucn.Vx ||
      tr : (cn : cone/ D){J : 𝕁.Obj} → ucn.leg J ∘ ar cn ~ cn.leg cn J
      isjm : is-jointly-monic-cone/ ucn
    open is-jointly-monic-cone/ isjm public
    ar-uq : (cn : cone/ D){f : || Hom (cn.Vx cn) ucn.Vx ||}
                 → ((J : 𝕁.Obj) → ucn.leg J ∘ f ~ cn.leg cn J)
                      → f ~ ar cn
    ar-uq cn tr' = jm-pf λ J → tr' J ⊙ tr cn ˢ
                 where open ecategory-aux-only ℂ using (_⊙_; _ˢ)

  record limit-of {𝕁 : small-ecategory}(D : efunctorₗₑᵥ 𝕁 ℂ) : Set (ℓₒ ⊔ ℓₕ) where
    field
      ucn : cone/ D
      isuniv : is-universal-cone ucn
    open cone/ ucn renaming (leg to π) public
    open is-universal-cone isuniv public      
    
-- end small-limit-defs


record has-small-limits {ℓₒ ℓₕ}(ℂ : ecategoryₗₑᵥ ℓₒ ℓₕ) : Set (1ₗₑᵥ ⊔ ℓₒ ⊔ ℓₕ) where
  open small-limit-defs ℂ
  field
    lim-of : {𝕁 : small-ecategory}(D : efunctorₗₑᵥ 𝕁 ℂ) → limit-of D
  module lim-of {𝕁 : small-ecategory}(D : efunctorₗₑᵥ 𝕁 ℂ) = limit-of (lim-of D)
  --open lim-of public
