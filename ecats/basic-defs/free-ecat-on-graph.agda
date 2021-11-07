
{-# OPTIONS --without-K #-}

module ecats.basic-defs.free-ecat-on-graph where

open import tt-basics.setoids hiding (||_||)
open import ecats.basic-defs.ecat-def&not
open import ecats.basic-defs.commut-shapes
open import ecats.basic-defs.isomorphism
open import ecats.basic-props.isomorphism
open import ecats.functors.defs.efunctor-d&n
--open import ecats.functors.defs.cone
open import ecats.functors.defs.natural-transformation
--open import ecats.constructions.functor-ecat
--open import ecats.constructions.slice-ecat

module free-category-on-graph-defs {ℓ₁ ℓ₂ ℓ₃ : Level}(ℂ : ecategoryₗₑᵥ ℓ₁ ℓ₂ ℓ₃)
                                   {V : Set ℓ₁}(E : V → V → setoid {ℓ₂} {ℓ₃})
                                   {FO : V → ecat.Obj ℂ}
                                   (FH : {u v : V} → || E u v || → || ecat.Hom ℂ (FO u) (FO v) ||)
                                   (Fext : {u v : V}{uv uv' : || E u v ||} → < E u v > uv ~ uv'
                                              → < ecat.Hom ℂ (FO u) (FO v) > FH uv ~ FH uv')
                                   where
  private
    module ℂ = ecat ℂ
    module unvprop-aux (𝕏 : ecategoryₗₑᵥ ℓ₁ ℓ₂ ℓ₃) where
      open ecat 𝕏 public
      open iso-defs 𝕏 public
      open iso-props 𝕏 public

  record is-free-on-graph-prop (𝔻 : ecategoryₗₑᵥ ℓ₁ ℓ₂ ℓ₃){GO : V → ecat.Obj 𝔻}
                               {GH : {u v : V} → || E u v || → || ecat.Hom 𝔻 (GO u) (GO v) ||}
                               (Gext : {u v : V}{uv uv' : || E u v ||} → < E u v > uv ~ uv'
                                          → < ecat.Hom 𝔻 (GO u) (GO v) > GH uv ~ GH uv')
                               : Set ℂ.ℓₐₗₗ where
    private
      module 𝔻 = unvprop-aux 𝔻
    field
      fctr : efunctorₗₑᵥ ℂ 𝔻
    private module fctr = efunctorₗₑᵥ fctr
    field
      tr-fnc : {v : V} → || 𝔻.Hom (fctr.ₒ (FO v)) (GO v) ||
      tr-nat : {u v : V}(uv : || E u v ||) → tr-fnc {v} 𝔻.∘ fctr.ₐ (FH uv) 𝔻.~ GH uv 𝔻.∘ tr-fnc {u}
      tr-iso : {v : V} → 𝔻.is-iso (tr-fnc {v})
    private module tmp {v : V} = 𝔻.is-iso (tr-iso {v}) renaming (invf to tr-fnc⁻¹)
    open tmp public
    tr-nat⁻¹ : {u v : V}(uv : || E u v ||) → tr-fnc⁻¹ 𝔻.∘ GH uv 𝔻.~ fctr.ₐ (FH uv) 𝔻.∘ tr-fnc⁻¹
    tr-nat⁻¹ {u} {v} uv = 𝔻.iso-sq (isisopair {u}) (isisopair {v}) (tr-nat uv)
-- end free-category-on-graph-defs

record _is-free-category-on-graph {ℓ₁ ℓ₂ ℓ₃ : Level}(ℂ : ecategoryₗₑᵥ ℓ₁ ℓ₂ ℓ₃)
                                  {V : Set ℓ₁}(E : V → V → setoid {ℓ₂} {ℓ₃})
                                  {FO : V → ecat.Obj ℂ}
                                  (FH : {u v : V} → || E u v || → || ecat.Hom ℂ (FO u) (FO v) ||)
                                  : Set (sucₗₑᵥ (ecat.ℓₐₗₗ ℂ)) where
  private
    module ℂ = ecat ℂ
  open free-category-on-graph-defs ℂ E FH
  field
    ext : {u v : V}{uv uv' : || E u v ||} → < E u v > uv ~ uv'
             → FH uv ℂ.~ FH uv'
    unvprop : (𝔻 : ecategoryₗₑᵥ ℓ₁ ℓ₂ ℓ₃){GO : V → ecat.Obj 𝔻}
              {GH : {u v : V} → || E u v || → || ecat.Hom 𝔻 (GO u) (GO v) ||}
              (Gext : {u v : V}{uv uv' : || E u v ||} → < E u v > uv ~ uv'
                           → < ecat.Hom 𝔻 (GO u) (GO v) > GH uv ~ GH uv')
                    → is-free-on-graph-prop ext 𝔻 Gext
  module unv (𝔻 : ecategoryₗₑᵥ ℓ₁ ℓ₂ ℓ₃){GO : V → ecat.Obj 𝔻}
             {GH : {u v : V} → || E u v || → || ecat.Hom 𝔻 (GO u) (GO v) ||}
             (Gext : {u v : V}{uv uv' : || E u v ||} → < E u v > uv ~ uv'
                        → < ecat.Hom 𝔻 (GO u) (GO v) > GH uv ~ GH uv')
             = is-free-on-graph-prop ext (unvprop 𝔻 Gext)
