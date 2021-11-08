
{-# OPTIONS --without-K #-}

module ecats.basic-defs.free-ecat-on-graph where

open import tt-basics.setoids hiding (||_||)
open import ecats.basic-defs.ecat-def&not
open import ecats.basic-defs.isomorphism
open import ecats.basic-props.isomorphism
open import ecats.functors.defs.efunctor-d&n
open import ecats.functors.defs.natural-iso

module free-category-on-graph-defs {ℓ₁ ℓ₂ ℓ₃ : Level}(ℂ : ecategoryₗₑᵥ ℓ₁ ℓ₂ ℓ₃)
                                   {V : Set ℓ₁}(E : V → V → setoid {ℓ₂} {ℓ₃})
                                   {FO : V → ecat.Obj ℂ}
                                   (FE : {u v : V} → || E u v || → || ecat.Hom ℂ (FO u) (FO v) ||)
                                   (FEext : {u v : V}{uv uv' : || E u v ||} → < E u v > uv ~ uv'
                                              → < ecat.Hom ℂ (FO u) (FO v) > FE uv ~ FE uv')
                                   where
  private
    module ℂ = ecat ℂ
    module unvprop-aux {ℓ₁' ℓ₂' ℓ₃' : Level}(𝕏 : ecategoryₗₑᵥ ℓ₁' ℓ₂' ℓ₃') where
      open ecat 𝕏 public
      open iso-defs 𝕏 public
      open iso-props 𝕏 public

  record is-free-on-graph-prop {ℓ₁' ℓ₂' ℓ₃' : Level}(𝔻 : ecategoryₗₑᵥ ℓ₁' ℓ₂' ℓ₃'){GO : V → ecat.Obj 𝔻}
                               {GE : {u v : V} → || E u v || → || ecat.Hom 𝔻 (GO u) (GO v) ||}
                               (GEext : {u v : V}{uv uv' : || E u v ||} → < E u v > uv ~ uv'
                                          → < ecat.Hom 𝔻 (GO u) (GO v) > GE uv ~ GE uv')
                               : Set (ℂ.ℓₐₗₗ ⊔ ecat.ℓₐₗₗ 𝔻) where
    private
      module 𝔻 = unvprop-aux 𝔻
    field
      fctr : efunctorₗₑᵥ ℂ 𝔻
    private module fctr = efunctorₗₑᵥ fctr
    field
      tr-fnc : {v : V} → || 𝔻.Hom (fctr.ₒ (FO v)) (GO v) ||
      tr-nat : {u v : V}(uv : || E u v ||) → tr-fnc {v} 𝔻.∘ fctr.ₐ (FE uv) 𝔻.~ GE uv 𝔻.∘ tr-fnc {u}
      tr-iso : {v : V} → 𝔻.is-iso (tr-fnc {v})
    private module tmp {v : V} = 𝔻.is-iso (tr-iso {v}) renaming (invf to tr-fnc⁻¹)
    open tmp public
    tr-nat⁻¹ : {u v : V}(uv : || E u v ||) → tr-fnc⁻¹ 𝔻.∘ GE uv 𝔻.~ fctr.ₐ (FE uv) 𝔻.∘ tr-fnc⁻¹
    tr-nat⁻¹ {u} {v} uv = 𝔻.iso-sq (isisopair {u}) (isisopair {v}) (tr-nat uv)
    field
      uq : {H : efunctorₗₑᵥ ℂ 𝔻}
           (Hfnc : {v : V} → || 𝔻.Hom (efctr.ₒ H (FO v)) (GO v) ||)
           (Hnat : {u v : V}(uv : || E u v ||)
                      → Hfnc {v} 𝔻.∘ efctr.ₐ H (FE uv) 𝔻.~ GE uv 𝔻.∘ Hfnc {u})
           (Hiso : {v : V} → 𝔻.is-iso (Hfnc {v}))
             → H ≅ₐ fctr
-- end free-category-on-graph-defs



record _is-free-category-on-graph_via_at-lev[_,_,_]
         {ℓ₁ ℓ₂ ℓ₃ : Level}(ℂ : ecategoryₗₑᵥ ℓ₁ ℓ₂ ℓ₃)
         {V : Set ℓ₁}(E : V → V → setoid {ℓ₂} {ℓ₃})
         {FO : V → ecat.Obj ℂ}
         (FE : {u v : V} → || E u v || → || ecat.Hom ℂ (FO u) (FO v) ||)
         (ℓ₁' ℓ₂' ℓ₃' : Level)
         : Set (sucₗₑᵥ (ecat.ℓₐₗₗ ℂ ⊔ ℓ₁' ⊔ ℓ₂' ⊔ ℓ₃'))
         where
  private
    module ℂ = ecat ℂ
  open free-category-on-graph-defs ℂ E FE
  field
    ext : {u v : V}{uv uv' : || E u v ||} → < E u v > uv ~ uv'
             → FE uv ℂ.~ FE uv'
    unvprop : (𝔻 : ecategoryₗₑᵥ ℓ₁' ℓ₂' ℓ₃'){GO : V → ecat.Obj 𝔻}
              {GE : {u v : V} → || E u v || → || ecat.Hom 𝔻 (GO u) (GO v) ||}
              (GEext : {u v : V}{uv uv' : || E u v ||} → < E u v > uv ~ uv'
                           → < ecat.Hom 𝔻 (GO u) (GO v) > GE uv ~ GE uv')
                    → is-free-on-graph-prop ext 𝔻 GEext
  module unv (𝔻 : ecategoryₗₑᵥ ℓ₁' ℓ₂' ℓ₃'){GO : V → ecat.Obj 𝔻}
             {GE : {u v : V} → || E u v || → || ecat.Hom 𝔻 (GO u) (GO v) ||}
             (GEext : {u v : V}{uv uv' : || E u v ||} → < E u v > uv ~ uv'
                        → < ecat.Hom 𝔻 (GO u) (GO v) > GE uv ~ GE uv')
             = is-free-on-graph-prop ext (unvprop 𝔻 GEext)
