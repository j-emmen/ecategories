
{-# OPTIONS --without-K #-}

module ecats.small-colimits.defs.small-colimit where

open import Agda.Primitive
open import ecats.basic-defs.ecat-def&not
open import ecats.functors.defs.cocone public
open import ecats.functors.defs.efunctor-d&n
open import ecats.functors.defs.natural-transformation
open import ecats.constructions.functor-ecat
open import ecats.constructions.slice-ecat
open import ecats.finite-limits.defs.terminal public
open import ecats.basic-defs.initial public

module small-colimit-defs {ℓ₁ ℓ₂ ℓ₃ : Level}(ℂ : ecategoryₗₑᵥ ℓ₁ ℓ₂ ℓ₃) where
  private
    module ℂ = ecat ℂ

  -- small colimits
  is-universal-cone-under is-colimit-cone : {𝕀 : small-ecategory}{D : 𝕀 diag-in ℂ}(cone : /Cone.Obj D)
                              → Set ℂ.ℓₐₗₗ -- = (/Cone.ℓₐₗₗ D)
  is-universal-cone-under {𝕀} {D} cone = is-initial cone
                                        where open initial-defs (/Cone D)
  is-colimit-cone = is-universal-cone-under
  
  module is-colimit-cone {𝕀 : small-ecategory}{D : 𝕀 diag-in ℂ}{cL : /Cone.Obj D}
                         (iscolim : is-colimit-cone cL)
                         where
    private
      module /ConeD where
        open /Cone D public
        open initial-defs (/Cone D) public
      module cL where
        open /ConeD.ₒ cL renaming (leg to ι) public
        open /ConeD.is-initial {cL} iscolim public
    open cL using () renaming (ø to unv) public
    module unv (cn : /Cone.Obj D) where
      private module cn = /ConeD.ₒ cn
      open /ConeD.ₐ (cL.ø cn) public
      uq : {f : || ℂ.Hom cL.Vx cn.Vx ||}(trf : ∀ i → f ℂ.∘ cL.ι i ℂ.~ cn.leg i)
              → f ℂ.~ ar
      uq {f} tr = cL.øuq {cn} (/Cone.if-tr-then-ar D cL cn tr)
    ι-je :  {A : ℂ.Obj}{f g : || ℂ.Hom cL.Vx A ||}
            (eq : ∀ i → f ℂ.∘ cL.ι i ℂ.~ g ℂ.∘ cL.ι i)
              → f ℂ.~ g
    ι-je {f = f} {g} eq = cL.øuqg {f = /ConeD.ar-is-mor cL f}
                                  {g = /ConeD.if-tr-then-ar cL (/ConeD.ar-is-mor-cod cL f) {g}
                                                            (λ I → eq I ˢ)}
                        where open ecategory-aux-only ℂ using (_ˢ)

  record colimit-of {𝕀 : small-ecategory}(D : 𝕀 diag-in ℂ) : Set ℂ.ℓₐₗₗ where
    private module Cn = /Cone.ₒ D
    field
      cone : /Cone.Obj D
      iscolim : is-colimit-cone cone
    open /Cone.ₒ D cone renaming (leg to ι; sides to ι-natt) public
    open is-colimit-cone {𝕀} {D} {cone} iscolim public


  -- small products
  is-coproduct : {I : Set}{D : I → ecat.Obj ℂ}(span : /Span.Obj ℂ D)
                  → Set ℂ.ℓₐₗₗ
  is-coproduct {_} {D} = is-initial
                     where open initial-defs (/Span ℂ D)

  module is-coproduct {I : Set}{D : I → ecat.Obj ℂ}{P : /Span.Obj ℂ D}
                    (iscprd : is-coproduct P)
                    where
    private
      module D/Sp = /Span ℂ D
      module P = D/Sp.ₒ P renaming (leg to ι)
    open initial-defs.is-initial {ℂ = /Span ℂ D} {P} iscprd
    module unv (sp : D/Sp.Obj) where
      private module sp = D/Sp.ₒ sp
      open D/Sp.ₐ (ø sp) public
      uq : {f : || ℂ.Hom P.Vx sp.Vx ||}(trf : ∀ i → f ℂ.∘ P.ι i ℂ.~ sp.leg i)
              → f ℂ.~ ar
      uq {f} tr = øuq {sp} (D/Sp.if-tr-then-ar P sp tr)
    ι-je :  (sp : D/Sp.Obj){f g : || ℂ.Hom P.Vx (D/Sp.ₒ.Vx sp) ||}
            (trf : ∀ i → f ℂ.∘ P.ι i ℂ.~ D/Sp.ₒ.leg sp i)
            (trg : ∀ i → g ℂ.∘ P.ι i ℂ.~ D/Sp.ₒ.leg sp i)
              → f ℂ.~ g
    ι-je sp trf trg = øuqg {f = D/Sp.if-tr-then-ar P sp trf}
                           {g = D/Sp.if-tr-then-ar P sp trg}

  
  record coproduct-of {I : Set}(D : I → ecat.Obj ℂ) : Set ℂ.ℓₐₗₗ where
    private module D/Sp = /Span ℂ D
    field
      ⨿span/ : D/Sp.Obj
      iscprd : is-coproduct ⨿span/
    open D/Sp.ₒ ⨿span/ renaming (leg to ι) public
    open is-coproduct iscprd public

-- end small-colimit-defs


record has-small-colimits {ℓ₁ ℓ₂ ℓ₃ : Level}(ℂ : ecategoryₗₑᵥ ℓ₁ ℓ₂ ℓ₃) : Set (1ₗₑᵥ ⊔ ecat.ℓₐₗₗ ℂ) where
  open small-colimit-defs ℂ
  field
    clim-of : {𝕀 : small-ecategory}(D : 𝕀 diag-in ℂ) → colimit-of D
  module clim-of {𝕀 : small-ecategory}(D : 𝕀 diag-in ℂ) = colimit-of (clim-of D)
  open clim-of public

has-small-colimits-lc : ecategory → Set₁
has-small-colimits-lc = has-small-colimits

record has-small-coproducts {ℓ₁ ℓ₂ ℓ₃ : Level}(ℂ : ecategoryₗₑᵥ ℓ₁ ℓ₂ ℓ₃) : Set (1ₗₑᵥ ⊔ ecat.ℓₐₗₗ ℂ) where
  open small-colimit-defs ℂ
  field
    cprd-of : {I : Set}(D : I → ecat.Obj ℂ) → coproduct-of D
  module cprd-of {I : Set}(D : I → ecat.Obj ℂ) = coproduct-of (cprd-of D)
  open cprd-of public

