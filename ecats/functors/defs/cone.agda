
{-# OPTIONS --without-K #-}

module ecats.functors.defs.cone where

open import Agda.Primitive
open import ecats.basic-defs.ecat-def&not
open import ecats.functors.defs.efunctor-d&n
open import ecats.functors.defs.natural-transformation
open import ecats.constructions.functor-ecat
open import ecats.constructions.comma-ecat


-- Category of cones over a diagram
Cone/ : {𝕀 : small-ecategory}{ℓ₁ ℓ₂ ℓ₃ : Level}{ℂ : ecategoryₗₑᵥ ℓ₁ ℓ₂ ℓ₃}(D : 𝕀 diag-in ℂ)
          → ecategoryₗₑᵥ (ecat.ℓₐₗₗ ℂ) (ecat.ℓₕₒₘ ℂ) (ecat.ℓ~ ℂ)
Cone/ {𝕀} {ℂ = ℂ} D = (const-Diagr 𝕀 ℂ) ↓ₒ D

-- The category of cones over a diagram in a locally-small ecategory is locally-small
Cone/lc : {𝕀 : small-ecategory}{ℂ : ecategory}(D : 𝕀 diag-in ℂ)
             → ecategory
Cone/lc {𝕀} {ℂ} D = Cone/ {𝕀} {ℂ = ℂ} D

module Cone/ {𝕀 : small-ecategory}{ℓ₁ ℓ₂ ℓ₃ : Level}{ℂ : ecategoryₗₑᵥ ℓ₁ ℓ₂ ℓ₃}
             (D : 𝕀 diag-in ℂ) where
  private
    module 𝕀 = ecat 𝕀
    module ℂ = ecat ℂ
    module D = diagram D
    module Cn/D = ecat (Cone/ D)
  --tr→sq : (f : ∀ i → || ℂ.Hom Vx (D.ₒ i) ||){i j : 𝕀.Obj}(ij : || 𝕀.Hom i j ||)
    --         → D.ₐ ij ℂ.∘ f i ℂ.~ f j → D.ₐ ij ℂ.∘ f i ℂ.~ f j ℂ.∘ ℂ.idar Vx
  -- renaming the components of the natural transformation
  module ₒ (cone : Cn/D.Obj) where
    open funct-slice-ecat.ₒ (const-Diagr 𝕀 ℂ) D cone renaming (L to Vx; ar to sides) public
    module sides = natural-transformation sides
    leg : (i : 𝕀.Obj) → || ℂ.Hom Vx (D.ₒ i) ||
    leg = λ i → sides.fnc {i}
    tr : {i j : 𝕀.Obj}(ij : || 𝕀.Hom i j ||) → D.ₐ ij ℂ.∘ leg i ℂ.~ leg j
    tr = λ ij → sides.nat ij ˢ ⊙ rid
       where open ecategory-aux-only ℂ using (_⊙_; _ˢ; rid)
  module ₐ {cone cone' : Cn/D.Obj}(cone-ar : || Cn/D.Hom cone cone' ||) where
    open funct-slice-ecat.ₐ (const-Diagr 𝕀 ℂ) D cone-ar renaming (arL to ar) public
  if-tr-then-ob : {A : ℂ.Obj}{f : (I : 𝕀.Obj) → || ℂ.Hom A (D.ₒ I) ||}
                      → (∀ {i} {j} ij → D.ₐ ij ℂ.∘ f i ℂ.~ f j)
                        → Cn/D.Obj
  if-tr-then-ob {A} {f} tr = record
    { L = A
    ; ar = record
         { fnc = λ {I} → f I
         ; nat = λ {I} {J} IJ → ridgen (tr IJ ˢ)
         }
    }
    where open ecategory-aux-only ℂ using (ridgen; _ˢ)
  if-tr-then-ar : (cn cn' : Cn/D.Obj){f : || ℂ.Hom (ₒ.Vx cn) (ₒ.Vx cn') ||}
                      → (∀ i → ₒ.leg cn' i ℂ.∘ f ℂ.~ ₒ.leg cn i)
                        → || Cn/D.Hom cn cn' ||
  if-tr-then-ar cn cn' {f} pf = record { arL = f ; tr = pf }
  ar-is-mor-dom : (cn : Cn/D.Obj){A : ℂ.Obj}
                      → || ℂ.Hom A (ₒ.Vx cn) || → Cn/D.Obj
  ar-is-mor-dom cn {A} f = if-tr-then-ob {f = λ I → leg I ℂ.∘ f}
                                         λ {I} {J} IJ → ass ⊙ ∘e r (tr IJ)
                         where open ecategory-aux-only ℂ using (_⊙_; ∘e; ass; r)
                               open ₒ cn
  ar-is-mor : (cn : Cn/D.Obj){A : ℂ.Obj}(f : || ℂ.Hom A (ₒ.Vx cn) ||)
                  → || Cn/D.Hom (ar-is-mor-dom cn f) cn ||
  ar-is-mor cn f = if-tr-then-ar ((ar-is-mor-dom cn f)) cn (λ I → r)
                 where open ecategory-aux-only ℂ using (r)                       
  open ecategory-aux (Cone/ D) public


-- An efunctor maps cones into cones
Fcone : {ℓ₁ ℓ₂ ℓ₃ : Level}{ℂ : ecategoryₗₑᵥ ℓ₁ ℓ₂ ℓ₃}{ℓ₄ ℓ₅ ℓ₆ : Level}{𝔻 : ecategoryₗₑᵥ ℓ₄ ℓ₅ ℓ₆}
        (F : efunctorₗₑᵥ ℂ 𝔻){𝕀 : small-ecategory}(D : 𝕀 diag-in ℂ)
            → Cone/.Obj D → Cone/.Obj (F ○ D)
Fcone F {𝕀} D C = Cn/FD.if-tr-then-ob {f = λ I → F.ₐ (C.leg I)} (λ IJ → F.∘ax (C.tr IJ))
                where module F = efunctor-aux F
                      module Cn/FD = Cone/ (F ○ D)
                      module C = Cone/.ₒ D C




-- Category of spans over a family of objects
Span/ : {I : Set}{ℓ₁ ℓ₂ ℓ₃ : Level}(ℂ : ecategoryₗₑᵥ ℓ₁ ℓ₂ ℓ₃)(D : I → ecat.Obj ℂ)
             → ecategoryₗₑᵥ (ecat.ℓₙₒ~ ℂ) (ecat.ℓₕₒₘ ℂ) (ecat.ℓ~ ℂ)
Span/ {I} ℂ D = const-discDiagr I ℂ ↓ₒ D

module Span/ {I : Set}{ℓ₁ ℓ₂ ℓ₃ : Level}(ℂ : ecategoryₗₑᵥ ℓ₁ ℓ₂ ℓ₃)(D : I → ecat.Obj ℂ) where
  private
    module ℂ = ecat ℂ
    module Sp/D = ecat (Span/ ℂ D)
  -- renaming the components of the natural transformation
  module ₒ (span : Sp/D.Obj) = funct-slice-ecat.ₒ (const-discDiagr I ℂ) D span
                             renaming (L to Vx; ar to leg)
  if-tr-then-ar : (cn cn' : Sp/D.Obj){f : || ℂ.Hom (ₒ.Vx cn) (ₒ.Vx cn') ||}
                      → (∀ i → ₒ.leg cn' i ℂ.∘ f ℂ.~ ₒ.leg cn i)
                        → || Sp/D.Hom cn cn' ||
  if-tr-then-ar cn cn' {f} pf = record { arL = f ; tr = pf }
  module ₐ {span span' : Sp/D.Obj}(span-ar : || Sp/D.Hom span span' ||)
         = funct-slice-ecat.ₐ (const-discDiagr I ℂ) D span-ar
         renaming (arL to ar)
  open ecategory-aux (Span/ ℂ D) public

-- underlying family of a cone
cone→span : {𝕀 : small-ecategory}{ℓ₁ ℓ₂ ℓ₃ : Level}{ℂ : ecategoryₗₑᵥ ℓ₁ ℓ₂ ℓ₃}{D : 𝕀 diag-in ℂ}
                     → Cone/.Obj D → Span/.Obj ℂ (efctr.ₒ D)
cone→span {D = D} cone = record
         { L = cone.Vx
         ; ar = cone.leg
         }
         where module cone = Cone/.ₒ D cone


-- an efunctor maps spans into spans
Fspan : {ℓ₁ ℓ₂ ℓ₃ : Level}{ℂ : ecategoryₗₑᵥ ℓ₁ ℓ₂ ℓ₃}{ℓ₄ ℓ₅ ℓ₆ : Level}{𝔻 : ecategoryₗₑᵥ ℓ₄ ℓ₅ ℓ₆}
        (F : efunctorₗₑᵥ ℂ 𝔻){I : Set}(D : I → ecat.Obj ℂ)
            → Span/.Obj ℂ D → Span/.Obj 𝔻 (λ i → efctr.ₒ F (D i))
Fspan F {𝕀} D C = record
  { L = F.ₒ C.Vx
  ; ar = λ i → F.ₐ (C.leg i)
  }
  where module F = efunctor-aux F
        module C = Span/.ₒ _ D C
