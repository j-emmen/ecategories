
{-# OPTIONS --without-K #-}

module ecats.functors.defs.cocone where

open import Agda.Primitive
open import ecats.basic-defs.ecat-def&not
open import ecats.functors.defs.efunctor-d&n
open import ecats.functors.defs.natural-transformation
open import ecats.functors.defs.cone
open import ecats.constructions.functor-ecat
open import ecats.constructions.slice-ecat


-- Category of cones over a diagram
/Cone : {𝕀 : small-ecategory}{ℓ₁ ℓ₂ ℓ₃ : Level}{ℂ : ecategoryₗₑᵥ ℓ₁ ℓ₂ ℓ₃}(D : 𝕀 diag-in ℂ)
          → ecategoryₗₑᵥ (ecat.ℓₐₗₗ ℂ) (ecat.ℓₕₒₘ ℂ) (ecat.ℓ~ ℂ)
/Cone {𝕀} {ℂ = ℂ} D = D ₒ↓ (const-Diagr 𝕀 ℂ)


-- The category of cones over a diagram in a locally-small ecategory is locally-small
/Cone-lc : {𝕀 : small-ecategory}{ℂ : ecategory}(D : 𝕀 diag-in ℂ)
              → ecategory
/Cone-lc {𝕀} {ℂ} D = /Cone {𝕀} {ℂ = ℂ} D

module /Cone {𝕀 : small-ecategory}{ℓ₁ ℓ₂ ℓ₃ : Level}{ℂ : ecategoryₗₑᵥ ℓ₁ ℓ₂ ℓ₃}
             (D : 𝕀 diag-in ℂ) where
  private
    module 𝕀 = ecat 𝕀
    module ℂ = ecat ℂ
    module D = diagram D
    module D/Cn = ecat (/Cone D)
  --tr→sq : (f : ∀ i → || ℂ.Hom Vx (D.ₒ i) ||){i j : 𝕀.Obj}(ij : || 𝕀.Hom i j ||)
    --         → D.ₐ ij ℂ.∘ f i ℂ.~ f j → D.ₐ ij ℂ.∘ f i ℂ.~ f j ℂ.∘ ℂ.idar Vx
  -- renaming the components of the natural transformation
  module ₒ (cocone : D/Cn.Obj) where
    open slice-funct-ecat.ₒ (const-Diagr 𝕀 ℂ) D cocone renaming (R to Vx; ar to sides) public
    module sides = natural-transformation sides
    leg : (i : 𝕀.Obj) → || ℂ.Hom (D.ₒ i) Vx ||
    leg = λ i → sides.fnc {i}
    tr : {i j : 𝕀.Obj}(ij : || 𝕀.Hom i j ||) → leg j ℂ.∘ D.ₐ ij ℂ.~ leg i
    tr = λ ij → sides.nat ij ⊙ lid
       where open ecategory-aux-only ℂ using (_⊙_; _ˢ; lid)
  module ₐ {cocone cocone' : D/Cn.Obj}(cocone-ar : || D/Cn.Hom cocone cocone' ||) where
    open slice-funct-ecat.ₐ (const-Diagr 𝕀 ℂ) D cocone-ar renaming (arR to ar) public
  if-tr-then-ob : {A : ℂ.Obj}{f : (I : 𝕀.Obj) → || ℂ.Hom (D.ₒ I) A ||}
                      → (∀ {i} {j} ij → f j ℂ.∘ D.ₐ ij ℂ.~ f i)
                        → D/Cn.Obj
  if-tr-then-ob {A} {f} tr = record
    { R = A
    ; ar = record
         { fnc = λ {I} → f I
         ; nat = λ {I} {J} IJ → tr IJ ⊙ lidˢ
         }
    }
    where open ecategory-aux-only ℂ using (lidˢ; _⊙_)
  if-tr-then-ar : (cn cn' : D/Cn.Obj){f : || ℂ.Hom (ₒ.Vx cn) (ₒ.Vx cn') ||}
                      → (∀ i → f ℂ.∘ ₒ.leg cn i ℂ.~ ₒ.leg cn' i)
                        → || D/Cn.Hom cn cn' ||
  if-tr-then-ar cn cn' {f} pf = record { arR = f ; tr = pf }
  ar-is-mor-cod : (cn : D/Cn.Obj){A : ℂ.Obj}
                      → || ℂ.Hom (ₒ.Vx cn) A || → D/Cn.Obj
  ar-is-mor-cod cn {A} f = if-tr-then-ob {f = λ I → f ℂ.∘ leg I}
                                         λ {I} {J} IJ → assˢ ⊙ ∘e (tr IJ) r
                         where open ecategory-aux-only ℂ using (_⊙_; ∘e; assˢ; r)
                               open ₒ cn
  ar-is-mor : (cn : D/Cn.Obj){A : ℂ.Obj}(f : || ℂ.Hom (ₒ.Vx cn) A ||)
                  → || D/Cn.Hom cn (ar-is-mor-cod cn f) ||
  ar-is-mor cn f = if-tr-then-ar cn ((ar-is-mor-cod cn f)) (λ I → r)
                 where open ecategory-aux-only ℂ using (r)
  open ecategory-aux (/Cone D) public


-- An efunctor maps cocones into cocones
Fcocone : {ℓ₁ ℓ₂ ℓ₃ : Level}{ℂ : ecategoryₗₑᵥ ℓ₁ ℓ₂ ℓ₃}{ℓ₄ ℓ₅ ℓ₆ : Level}{𝔻 : ecategoryₗₑᵥ ℓ₄ ℓ₅ ℓ₆}
        (F : efunctorₗₑᵥ ℂ 𝔻){𝕀 : small-ecategory}(D : 𝕀 diag-in ℂ)
            → /Cone.Obj D → /Cone.Obj (F ○ D)
Fcocone F {𝕀} D C = Cn/FD.if-tr-then-ob {f = λ I → F.ₐ (C.leg I)} (λ IJ → F.∘ax (C.tr IJ))
                where module F = efunctor-aux F
                      module Cn/FD = /Cone (F ○ D)
                      module C = /Cone.ₒ D C




-- Category of cospans under a family of objects
/Span : {I : Set}{ℓ₁ ℓ₂ ℓ₃ : Level}(ℂ : ecategoryₗₑᵥ ℓ₁ ℓ₂ ℓ₃)(D : I → ecat.Obj ℂ)
             → ecategoryₗₑᵥ (ecat.ℓₙₒ~ ℂ) (ecat.ℓₕₒₘ ℂ) (ecat.ℓ~ ℂ)
/Span {I} ℂ D = D ₒ↓ (const-discDiagr I ℂ)

module /Span {I : Set}{ℓ₁ ℓ₂ ℓ₃ : Level}(ℂ : ecategoryₗₑᵥ ℓ₁ ℓ₂ ℓ₃)(D : I → ecat.Obj ℂ) where
  private
    module ℂ = ecat ℂ
    module D/Sp = ecat (/Span ℂ D)
  -- renaming the components of the natural transformation
  module ₒ (cospan : D/Sp.Obj) = slice-funct-ecat.ₒ (const-discDiagr I ℂ) D cospan
                               renaming (R to Vx; ar to leg)
  if-tr-then-ar : (cn cn' : D/Sp.Obj){f : || ℂ.Hom (ₒ.Vx cn) (ₒ.Vx cn') ||}
                      → (∀ i → f ℂ.∘ ₒ.leg cn i ℂ.~ ₒ.leg cn' i)
                        → || D/Sp.Hom cn cn' ||
  if-tr-then-ar cn cn' {f} pf = record { arR = f ; tr = pf }
  module ₐ {cospan cospan' : D/Sp.Obj}(cospan-ar : || D/Sp.Hom cospan cospan' ||)
         = slice-funct-ecat.ₐ (const-discDiagr I ℂ) D cospan-ar
         renaming (arR to ar)
  open ecategory-aux (/Span ℂ D) public

-- underlying family of a cocone
cocone→cospan : {𝕀 : small-ecategory}{ℓ₁ ℓ₂ ℓ₃ : Level}{ℂ : ecategoryₗₑᵥ ℓ₁ ℓ₂ ℓ₃}{D : 𝕀 diag-in ℂ}
                     → /Cone.Obj D → /Span.Obj ℂ (efctr.ₒ D)
cocone→cospan {D = D} cocone = record
         { R = cocone.Vx
         ; ar = cocone.leg
         }
         where module cocone = /Cone.ₒ D cocone


-- an efunctor maps cospans into cospans
Fcospan : {ℓ₁ ℓ₂ ℓ₃ : Level}{ℂ : ecategoryₗₑᵥ ℓ₁ ℓ₂ ℓ₃}{ℓ₄ ℓ₅ ℓ₆ : Level}{𝔻 : ecategoryₗₑᵥ ℓ₄ ℓ₅ ℓ₆}
        (F : efunctorₗₑᵥ ℂ 𝔻){I : Set}(D : I → ecat.Obj ℂ)
            → /Span.Obj ℂ D → /Span.Obj 𝔻 (λ i → efctr.ₒ F (D i))
Fcospan F {𝕀} D C = record
  { R = F.ₒ C.Vx
  ; ar = λ i → F.ₐ (C.leg i)
  }
  where module F = efunctor-aux F
        module C = /Span.ₒ _ D C
