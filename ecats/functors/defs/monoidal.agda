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
                             (𝕍mon : is-monoidal-cat 𝕍) (𝕎mon : is-monoidal-cat 𝕎)
                             where
  private
    module 𝕍 = moncat 𝕍mon
    module 𝕎 = moncat 𝕎mon
  
  module aux (F : efunctorₗₑᵥ 𝕍 𝕎) where
    private module F = efctr F
    
    F⊗F : efunctorₗₑᵥ 𝕍 [ 𝕍 , 𝕎 ]ᶜᵃᵗ
    F⊗F =  precmp-Fctr 𝕎 F ○ 𝕎.tenf ○ F
    F⊗ : efunctorₗₑᵥ 𝕍 [ 𝕍 , 𝕎 ]ᶜᵃᵗ
    F⊗ = postcmp-Fctr F ○ 𝕍.tenf

    record is-monoidal-with-isos (Iiso : 𝕎.I 𝕎.≅ₒ (F.ₒ 𝕍.I))
                                 (⊗iso : natural-iso F⊗F F⊗)
                                 : Set (𝕍.ℓₙₒ~ ⊔ 𝕎.ℓₕₒₘ) where
      private
        module I≅ = 𝕎._≅ₒ_ Iiso renaming (a12 to ar; a21 to ar⁻¹)
        module ⊗≅ = uncurry-nat-iso-into-functor-cat ⊗iso
      field
        run-eq : {X : 𝕍.Obj}
                 → F.ₐ (𝕍.⊗run.fnc {X}) 𝕎.∘ ⊗≅.fnc X {𝕍.I} 𝕎.∘ (𝕎.l⊗ₒ.ₐ (F.ₒ X) I≅.ar)
                       𝕎.~ 𝕎.⊗run.fnc {F.ₒ X}
        lun-eq : {X : 𝕍.Obj}
                    → F.ₐ (𝕍.⊗lun.fnc {X}) 𝕎.∘ ⊗≅.fnc 𝕍.I {X} 𝕎.∘ (𝕎.⊗rₒ.ₐ (F.ₒ X) I≅.ar)
                                  𝕎.~ 𝕎.⊗lun.fnc {F.ₒ X}
        ass-eq : {X Y Z : 𝕍.Obj}
                    → F.ₐ (𝕍.⊗ass.fnc X Y {Z})
                       𝕎.∘ ⊗≅.fnc (X 𝕍.⊗ₒ Y) {Z} 𝕎.∘ 𝕎.⊗rₒ.ₐ (F.ₒ Z) (⊗≅.fnc X {Y})
                            𝕎.~ (⊗≅.fnc X {Y 𝕍.⊗ₒ Z} 𝕎.∘ 𝕎.l⊗ₒ.ₐ (F.ₒ X) (⊗≅.fnc Y {Z}))
                                 𝕎.∘ 𝕎.⊗ass.fnc (F.ₒ X) (F.ₒ Y) {F.ₒ Z}

      run-eqˢ : {X : 𝕍.Obj}
                 → 𝕎.⊗run.fnc {F.ₒ X} 𝕎.~
                   F.ₐ (𝕍.⊗run.fnc {X}) 𝕎.∘ ⊗≅.fnc X {𝕍.I} 𝕎.∘ (𝕎.l⊗ₒ.ₐ (F.ₒ X) I≅.ar)
      run-eqˢ {X} = run-eq {X} ˢ
        where open ecategory-aux-only 𝕎 using (_ˢ)
      
      lun-eqˢ : {X : 𝕍.Obj}
                    → 𝕎.⊗lun.fnc {F.ₒ X} 𝕎.~
                      F.ₐ (𝕍.⊗lun.fnc {X}) 𝕎.∘ ⊗≅.fnc 𝕍.I {X} 𝕎.∘ (𝕎.⊗rₒ.ₐ (F.ₒ X) I≅.ar)
      lun-eqˢ {X} = lun-eq {X} ˢ
        where open ecategory-aux-only 𝕎 using (_ˢ)
      
      ass-eqˢ : {X Y Z : 𝕍.Obj}
                    → (⊗≅.fnc X {Y 𝕍.⊗ₒ Z} 𝕎.∘ 𝕎.l⊗ₒ.ₐ (F.ₒ X) (⊗≅.fnc Y {Z}))
                                 𝕎.∘ 𝕎.⊗ass.fnc (F.ₒ X) (F.ₒ Y) {F.ₒ Z}
                       𝕎.~ F.ₐ (𝕍.⊗ass.fnc X Y {Z})
                         𝕎.∘ ⊗≅.fnc (X 𝕍.⊗ₒ Y) {Z} 𝕎.∘ 𝕎.⊗rₒ.ₐ (F.ₒ Z) (⊗≅.fnc X {Y})
      ass-eqˢ {X} {Y} {Z} = ass-eq {X} {Y} {Z} ˢ
        where open ecategory-aux-only 𝕎 using (_ˢ)
      
      run-eq⁻¹ : {X : 𝕍.Obj}
                 → 𝕎.⊗run.fnc {F.ₒ X} 𝕎.∘ 𝕎.l⊗ₒ.ₐ (F.ₒ X) I≅.ar⁻¹ 𝕎.∘ ⊗≅.fnc⁻¹ X {𝕍.I}
                       𝕎.~ F.ₐ (𝕍.⊗run.fnc {X})
      run-eq⁻¹ {X} =
        𝕎.iso-trdom (𝕎.isopair-cmp (𝕎.l⊗ₒ.ᵢₛₒ (F.ₒ X) I≅.isop) ⊗≅.isisopair) (run-eq {X})
      run-eq⁻¹ˢ : {X : 𝕍.Obj}
                 → F.ₐ (𝕍.⊗run.fnc {X}) 𝕎.~
                   𝕎.⊗run.fnc {F.ₒ X} 𝕎.∘ 𝕎.l⊗ₒ.ₐ (F.ₒ X) I≅.ar⁻¹ 𝕎.∘ ⊗≅.fnc⁻¹ X {𝕍.I}
      run-eq⁻¹ˢ {X} = run-eq⁻¹ {X} ˢ
        where open ecategory-aux-only 𝕎 using (_ˢ)

      lun-eq⁻¹ : {X : 𝕍.Obj}
                 → 𝕎.⊗lun.fnc {F.ₒ X} 𝕎.∘ 𝕎.⊗rₒ.ₐ (F.ₒ X) I≅.ar⁻¹ 𝕎.∘ ⊗≅.fnc⁻¹ 𝕍.I {X}
                      𝕎.~ F.ₐ (𝕍.⊗lun.fnc {X})
      lun-eq⁻¹ {X} =
        𝕎.iso-trdom (𝕎.isopair-cmp (𝕎.⊗rₒ.ᵢₛₒ (F.ₒ X) I≅.isop) ⊗≅.isisopair) (lun-eq {X})
      lun-eq⁻¹ˢ : {X : 𝕍.Obj}
                 → F.ₐ (𝕍.⊗lun.fnc {X}) 𝕎.~
                   𝕎.⊗lun.fnc {F.ₒ X} 𝕎.∘ 𝕎.⊗rₒ.ₐ (F.ₒ X) I≅.ar⁻¹ 𝕎.∘ ⊗≅.fnc⁻¹ 𝕍.I {X}
      lun-eq⁻¹ˢ {X} = lun-eq⁻¹ {X} ˢ
        where open ecategory-aux-only 𝕎 using (_ˢ)
  
      ass-eq⁻¹ : {X Y Z : 𝕍.Obj}
                    → (𝕎.l⊗ₒ.ₐ (F.ₒ X) (⊗≅.fnc⁻¹ Y {Z}) 𝕎.∘ ⊗≅.fnc⁻¹ X {Y 𝕍.⊗ₒ Z})
                              𝕎.∘ F.ₐ (𝕍.⊗ass.fnc X Y {Z})
                      𝕎.~  𝕎.⊗ass.fnc (F.ₒ X) (F.ₒ Y) {F.ₒ Z}
                             𝕎.∘ 𝕎.⊗rₒ.ₐ (F.ₒ Z) (⊗≅.fnc⁻¹ X {Y}) 𝕎.∘ ⊗≅.fnc⁻¹ (X 𝕍.⊗ₒ Y) {Z}
      ass-eq⁻¹ {X} {Y} {Z} =
        𝕎.iso-sq (𝕎.isopair-cmp (𝕎.⊗rₒ.ᵢₛₒ (F.ₒ Z) ⊗≅.isisopair) ⊗≅.isisopair)
                        (𝕎.isopair-cmp (𝕎.l⊗ₒ.ᵢₛₒ (F.ₒ X) ⊗≅.isisopair) ⊗≅.isisopair)
                        (ass-eqˢ {X} {Y} {Z})
      ass-eq⁻¹ˢ : {X Y Z : 𝕍.Obj}
                    → 𝕎.⊗ass.fnc (F.ₒ X) (F.ₒ Y) {F.ₒ Z}
                        𝕎.∘ 𝕎.⊗rₒ.ₐ (F.ₒ Z) (⊗≅.fnc⁻¹ X {Y}) 𝕎.∘ ⊗≅.fnc⁻¹ (X 𝕍.⊗ₒ Y) {Z}
                      𝕎.~ (𝕎.l⊗ₒ.ₐ (F.ₒ X) (⊗≅.fnc⁻¹ Y {Z}) 𝕎.∘ ⊗≅.fnc⁻¹ X {Y 𝕍.⊗ₒ Z})
                            𝕎.∘ F.ₐ (𝕍.⊗ass.fnc X Y {Z})
      ass-eq⁻¹ˢ {X} {Y} {Z} = ass-eq⁻¹ {X} {Y} {Z} ˢ
        where open ecategory-aux-only 𝕎 using (_ˢ)
    -- end is-monoidal-with-isos
  --end aux

{-
  record preserves-monoidal-prod (F : efunctorₗₑᵥ 𝕍 𝕎)
                                 : Set (𝕍.ℓₙₒ~ ⊔ 𝕎.ℓₕₒₘ) where
    private module F = efctr F
    open aux F
    field
      Iiso : 𝕎.I 𝕎.≅ₒ (F.ₒ 𝕍.I)
      ⊗iso : natural-iso F⊗F F⊗
    module I≅ = 𝕎._≅ₒ_ Iiso renaming (a12 to ar; a21 to ar⁻¹)
    module ⊗≅ = uncurry-nat-iso-into-functor-cat ⊗iso
    field
      run-eq : {X : 𝕍.Obj}
               → F.ₐ (𝕍.⊗run.fnc {X}) 𝕎.∘ ⊗≅.fnc X {𝕍.I} 𝕎.∘ (𝕎.l⊗ₒ.ₐ (F.ₒ X) I≅.ar)
                     𝕎.~ 𝕎.⊗run.fnc {F.ₒ X}
      lun-eq : {X : 𝕍.Obj}
                  → F.ₐ (𝕍.⊗lun.fnc {X}) 𝕎.∘ ⊗≅.fnc 𝕍.I {X} 𝕎.∘ (𝕎.⊗rₒ.ₐ (F.ₒ X) I≅.ar)
                                𝕎.~ 𝕎.⊗lun.fnc {F.ₒ X}
      ass-eq : {X Y Z : 𝕍.Obj}
                  → F.ₐ (𝕍.⊗ass.fnc X Y {Z})
                     𝕎.∘ (⊗≅.fnc (X 𝕍.⊗ₒ Y) {Z} 𝕎.∘ 𝕎.⊗rₒ.ₐ (F.ₒ Z) (⊗≅.fnc X {Y}) )
                          𝕎.~ (⊗≅.fnc X {Y 𝕍.⊗ₒ Z} 𝕎.∘ 𝕎.l⊗ₒ.ₐ (F.ₒ X) (⊗≅.fnc Y {Z}))
                               𝕎.∘ 𝕎.⊗ass.fnc (F.ₒ X) (F.ₒ Y) {F.ₒ Z}
  -- end preserves-monoidal-prod
-}

  open aux public
-- end monoidal-functor-defs


record is-monoidal-functor {ℓₒ₁ ℓₐ₁ ℓ~₁ : Level} {𝕍 : ecategoryₗₑᵥ ℓₒ₁ ℓₐ₁ ℓ~₁}
                           {ℓₒ₂ ℓₐ₂ ℓ~₂ : Level} {𝕎 : ecategoryₗₑᵥ ℓₒ₂ ℓₐ₂ ℓ~₂}
                           (F : efunctorₗₑᵥ 𝕍 𝕎)
                           (𝕍mon : is-monoidal-cat 𝕍) (𝕎mon : is-monoidal-cat 𝕎)
                           : Set (ecat.ℓₙₒ~ 𝕍 ⊔ ecat.ℓₕₒₘ 𝕎)
                           where
  open monoidal-functor-defs 𝕍mon 𝕎mon
  private
    module 𝕎 = moncat 𝕎mon
    module 𝕍 = moncat 𝕍mon
    module F = efctr F
  field
    Iiso : 𝕎.I 𝕎.≅ₒ (F.ₒ 𝕍.I)
    ⊗iso : natural-iso (F⊗F F) (F⊗ F)
    pf : is-monoidal-with-isos F Iiso ⊗iso
  module I≅ = 𝕎._≅ₒ_ Iiso renaming (a12 to ar; a21 to ar⁻¹)
  module ⊗≅ = uncurry-nat-iso-into-functor-cat ⊗iso
  open is-monoidal-with-isos pf public
    --pres-mon : preserves-monoidal-prod F
--  open preserves-monoidal-prod pres-mon public

