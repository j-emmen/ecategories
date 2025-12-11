{-# OPTIONS --without-K #-}

module ecats.functors.defs.monoidal where 

open import ecats.basic-defs.ecat-def&not
open import ecats.isomorphism
open import ecats.functors.defs.efunctor-d&n
open import ecats.functors.defs.natural-transformation
open import ecats.functors.defs.natural-iso
open import ecats.constructions.functor-ecat
open import ecats.basic-defs.monoidal

module monoidal-functor-defs {ℓₒ₁ ℓₐ₁ ℓ~₁ : Level} {𝕍 : ecategoryₗₑᵥ ℓₒ₁ ℓₐ₁ ℓ~₁}
                             {ℓₒ₂ ℓₐ₂ ℓ~₂ : Level} {𝕎 : ecategoryₗₑᵥ ℓₒ₂ ℓₐ₂ ℓ~₂}
                             (𝕍mon : is-monoidal 𝕍) (𝕎mon : is-monoidal 𝕎)
                             where
  private
    module moncat {ℓₒ ℓₐ ℓ~ : Level} {𝕏 : ecategoryₗₑᵥ ℓₒ ℓₐ ℓ~} (𝕏mon : is-monoidal 𝕏) where
      open ecat 𝕏 public
      open iso-d&p 𝕏 public
      open is-monoidal 𝕏mon public
    module 𝕍 = moncat 𝕍mon
    module 𝕎 = moncat 𝕎mon


  record preserves-monoidal-prod (F : efunctorₗₑᵥ 𝕍 𝕎)
                                 : Set (𝕍.ℓₙₒ~ ⊔ 𝕎.ℓₕₒₘ) where
    private module F = efctr F
    F⊗F : efunctorₗₑᵥ 𝕍 [ 𝕍 , 𝕎 ]ᶜᵃᵗ
    F⊗F =  precmp-Fctr 𝕎 F ○ 𝕎.tenf ○ F
    F⊗ : efunctorₗₑᵥ 𝕍 [ 𝕍 , 𝕎 ]ᶜᵃᵗ
    F⊗ = postcmp-Fctr F ○ 𝕍.tenf
    field
      Iiso : 𝕎.I 𝕎.≅ₒ (F.ₒ 𝕍.I)
      ⊗iso : natural-iso F⊗F F⊗
    module I≅ = 𝕎._≅ₒ_ Iiso renaming (a12 to ar; a21 to ar⁻¹)
    module ⊗≅ = uncurry-nat-iso-into-functor-cat ⊗iso
    field
      run-eq : {X : 𝕍.Obj}
               → F.ₐ (𝕍.run.fnc {X}) 𝕎.∘ ⊗≅.fnc X {𝕍.I} 𝕎.∘ (𝕎.l⊗ₒ.ₐ (F.ₒ X) I≅.ar)
                     𝕎.~ 𝕎.run.fnc {F.ₒ X}
      lun-eq : {X : 𝕍.Obj}
                  → F.ₐ (𝕍.lun.fnc {X}) 𝕎.∘ ⊗≅.fnc 𝕍.I {X} 𝕎.∘ (𝕎.⊗rₒ.ₐ (F.ₒ X) I≅.ar)
                                𝕎.~ 𝕎.lun.fnc {F.ₒ X}
      ass-eq : {X Y Z : 𝕍.Obj}
                  → F.ₐ (𝕍.ass.fnc X Y {Z})
                     𝕎.∘ (⊗≅.fnc (X 𝕍.⊗ₒ Y) {Z} 𝕎.∘ 𝕎.⊗rₒ.ₐ (F.ₒ Z) (⊗≅.fnc X {Y}) )
                          𝕎.~ (⊗≅.fnc X {Y 𝕍.⊗ₒ Z} 𝕎.∘ 𝕎.l⊗ₒ.ₐ (F.ₒ X) (⊗≅.fnc Y {Z}))
                               𝕎.∘ 𝕎.ass.fnc (F.ₒ X) (F.ₒ Y) {F.ₒ Z}
  -- end preserves-monoidal-prod
-- end monoidal-functor-defs


is-monoidal-functor :  {ℓₒ₁ ℓₐ₁ ℓ~₁ : Level} {𝕍 : ecategoryₗₑᵥ ℓₒ₁ ℓₐ₁ ℓ~₁}
                       {ℓₒ₂ ℓₐ₂ ℓ~₂ : Level} {𝕎 : ecategoryₗₑᵥ ℓₒ₂ ℓₐ₂ ℓ~₂}
                         → efunctorₗₑᵥ 𝕍 𝕎
                           → is-monoidal 𝕍 → is-monoidal 𝕎 
                             → Set (ecat.ℓₙₒ~ 𝕍 ⊔ ecat.ℓₕₒₘ 𝕎)
is-monoidal-functor F 𝕍mon 𝕎mon = preserves-monoidal-prod F
  where open monoidal-functor-defs 𝕍mon 𝕎mon
