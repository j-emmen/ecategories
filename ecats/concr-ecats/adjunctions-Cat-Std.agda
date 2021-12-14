
{-# OPTIONS --without-K #-}

module ecats.concr-ecats.adjunctions-Cat-Std where

open import tt-basics.basics
open import tt-basics.setoids renaming (||_|| to ||_||std)
open import ecats.basic-defs.ecat-def&not
open import ecats.isomorphism
open import ecats.functors.defs.efunctor-d&n
open import ecats.functors.defs.natural-transformation
open import ecats.functors.defs.natural-iso
open import ecats.functors.defs.adjunction
open import ecats.functors.props.efunctor
open import ecats.concr-ecats.ecat-ecats
open import ecats.concr-ecats.Type-lev
open import ecats.concr-ecats.Std-lev


-----------------------------------------------------------------------
-- The obvious "functor" from Cat to Type is not extensional
-----------------------------------------------------------------------
{-
attempt : efunctor Cat Type
attempt = record
  { FObj = ecat.Obj
  ; FHom = efctr.ₒ
  ; isF = record
        { ext = λ {f = F} {F'} natiso → {!!} -- it's just FX ≅ F'X, not FX == F'X as required.
        ; id = λ {ℂ} X → =rf
        ; cmp = λ F G X → =rf
        }
  }
-}

module obj-up-to-iso {ℓ₁ ℓ₂ ℓ₃ : Level}(ℂ : ecategoryₗₑᵥ ℓ₁ ℓ₂ ℓ₃) where
  private
    module ℂ where
      open ecat ℂ public
      open iso-d&p ℂ public
  Obj/≅ₒ : setoid {ℓ₁} {ℓ₂ ⊔ ℓ₃}
  Obj/≅ₒ = record
         { object = ℂ.Obj
         ; _∼_ = λ X Y → X ℂ.≅ₒ Y
         ; istteqrel = record
                     { refl = ℂ.≅ₒrefl
                     ; sym = ℂ.≅ₒsym
                     ; tra = ℂ.≅ₒtra
                     }
         }
  module Obj/≅ₒ = setoid-aux Obj/≅ₒ
-- end obj-up-to-iso

module efctrs-are-ext {ℓ₁ₒ ℓ₁ₐ ℓ₁~}{ℂ : ecategoryₗₑᵥ ℓ₁ₒ ℓ₁ₐ ℓ₁~}
                      {ℓ₂ₒ ℓ₂ₐ ℓ₂~}{𝔻 : ecategoryₗₑᵥ ℓ₂ₒ ℓ₂ₐ ℓ₂~}
                      (F : efunctorₗₑᵥ ℂ 𝔻)
                      where
  private
    module ℂ where
      open ecat ℂ public
      open iso-d&p ℂ public
    module 𝔻 where
      open ecat 𝔻 public
      open iso-d&p 𝔻 public
    module F where
      open efctr F public
      open efunctor-lev-props F public
  open obj-up-to-iso
  ₒ/≅ₒ : setoidmap (Obj/≅ₒ ℂ) (Obj/≅ₒ 𝔻)
  ₒ/≅ₒ = record
    { op = F.ₒ
    ; ext = F.pres≅ₒ
    }
-- end efctrs-are-ext

module making-efctrs-ext-is-ext {ℓ₁ₒ ℓ₁ₐ ℓ₁~}{ℂ : ecategoryₗₑᵥ ℓ₁ₒ ℓ₁ₐ ℓ₁~}
                                {ℓ₂ₒ ℓ₂ₐ ℓ₂~}{𝔻 : ecategoryₗₑᵥ ℓ₂ₒ ℓ₂ₐ ℓ₂~}
                                {F G : efunctorₗₑᵥ ℂ 𝔻}(natiso : F ≅ₐ G)
                                where
  private
    module ℂ where
      open ecat ℂ public
      open iso-d&p ℂ public
    module 𝔻 where
      open ecat 𝔻 public
      open iso-d&p 𝔻 public
    module F where
      open efctr F public
      open efunctor-lev-props F public
    module G where
      open efctr G public
      open efunctor-lev-props G public
    module F≅G = natural-iso natiso
  ≅ptw : (X : ℂ.Obj) → F.ₒ X 𝔻.≅ₒ G.ₒ X
  ≅ptw X = record
    { a12 = F≅G.fnc
    ; a21 = F≅G.fnc⁻¹
    ; isop = F≅G.isiso
    }
-- end making-efctrs-ext-is-ext


--------------------------------------------------------------
-- Objects functor from categories to setoids, at every level
--------------------------------------------------------------

O/≅ₒ : (ℓₒ ℓₐ ℓ~ : Level) → efunctor (CATₗₑᵥ ℓₒ ℓₐ ℓ~) (Stdₗₑᵥ ℓₒ (ℓₐ ⊔ ℓ~))
O/≅ₒ ℓₒ ℓₐ ℓ~ = record
  { FObj = Obj/≅ₒ
  ; FHom = ₒ/≅ₒ
  ; isF = record
        { ext = ≅ptw
        ; id = λ {ℂ} X → Obj/≅ₒ.r ℂ {X}
        ; cmp = λ {ℂ} {𝔻} {𝔼} F G X → Obj/≅ₒ.r 𝔼 {_}
        }
  }
  where open obj-up-to-iso
        open efctrs-are-ext
        open making-efctrs-ext-is-ext











{-
module Setoid-of-arrows {ℓ₁ ℓ₂ ℓ₃ : Level}(ℂ : ecategoryₗₑᵥ ℓ₁ ℓ₂ ℓ₃) where
  private module ℂ = ecat ℂ

  Arr-ty : Set (ℓ₁ ⊔ ℓ₂)
  Arr-ty = Σ (prod ℂ.Obj ℂ.Obj) (λ XY → || ℂ.Hom (prj1 XY) (prj2 XY) ||)

  Arr-eq : Arr-ty → Arr-ty → Set 
  Arr-eq u u' = {!!}

  Arr : setoid {ℓ₁ ⊔ ℓ₂}
  Arr = record
      { object = Arr-ty
      ; _∼_ = {!!}
      ; istteqrel = {!!}
      }

-- end Setoid-of-arrows
-}
