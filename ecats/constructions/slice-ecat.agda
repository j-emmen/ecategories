{-# OPTIONS --without-K #-}

module ecats.constructions.slice-ecat where

open import Agda.Primitive
open import tt-basics.basics using (prod; pair)
open import tt-basics.setoids hiding (||_||)
open import ecats.basic-defs.ecat-def&not
open import ecats.functors.defs.efunctor-d&n
open import ecats.functors.defs.natural-transformation




module slice-ecat-defs {ℓ₁ ℓ₂ ℓ₃ : Level}(ℂ : ecategoryₗₑᵥ ℓ₁ ℓ₂ ℓ₃)(X : ecat.Obj ℂ) where
  open ecat ℂ
  private
    module ℂ = ecategory-aux ℂ

  record /Obj : Set ℓₙₒ~ where
    field
      D : Obj
      ar : || Hom D X ||

  record ||/Hom|| (A B : /Obj) : Set ℓₕₒₘ where
    private
      module A = /Obj A
      module B = /Obj B
    field
      ar : || Hom A.D B.D ||
      tr : B.ar ∘ ar ~ A.ar

  /Hom : /Obj → /Obj → setoid {ℓₕₒₘ} {ℓ~}
  /Hom A B = sub-setoid {X = ||/Hom|| A B} (Hom A.D B.D) (||/Hom||.ar {A} {B})
           where module A = /Obj A
                 module B = /Obj B

  /idar :  (A : /Obj) → ||/Hom|| A A
  /idar A = record
    { ar = idar A.D
    ; tr = ℂ.rid
    }
    where module A = /Obj A
  
  /cmp :  {A B C : /Obj}
             → ||/Hom|| B C → ||/Hom|| A B → ||/Hom|| A C
  /cmp {A} {B} {C} g f = record
    { ar = g.ar ∘ f.ar
    ; tr = ~proof C.ar ∘  g.ar ∘ f.ar    ~[ ass ⊙ ∘e r g.tr ] /
                  B.ar ∘ f.ar           ~[ f.tr ]∎
                  A.ar ∎
    }
    where module A = /Obj A
          module B = /Obj B
          module C = /Obj C
          module f = ||/Hom|| f
          module g = ||/Hom|| g
          open ecategory-aux-only ℂ
-- end slice-ecat-defs


slice-ecat : {ℓ₁ ℓ₂ ℓ₃ : Level}(ℂ : ecategoryₗₑᵥ ℓ₁ ℓ₂ ℓ₃)
                 → ecat.Obj ℂ → ecategoryₗₑᵥ (ecat.ℓₙₒ~ ℂ) (ecat.ℓₕₒₘ ℂ) (ecat.ℓ~ ℂ)
slice-ecat ℂ X = record
  { Obj = /Obj
  ; Hom = /Hom
  ; isecat = record
           { _∘_ = /cmp
           ; idar = /idar
           ; ∘ext = λ _ _ _ _ → ∘e
           ; lidax = λ _ → lid
           ; ridax = λ _ → rid
           ; assoc = λ _ _ _ → ass
           }
  }
  where open ecategory-aux ℂ
        open slice-ecat-defs ℂ X

infix 2 _/_
_/_ : {ℓ₁ ℓ₂ ℓ₃ : Level}(ℂ : ecategoryₗₑᵥ ℓ₁ ℓ₂ ℓ₃)
                 → ecat.Obj ℂ → ecategoryₗₑᵥ (ecat.ℓₙₒ~ ℂ) (ecat.ℓₕₒₘ ℂ) (ecat.ℓ~ ℂ)
ℂ / X = slice-ecat ℂ X

module slice-ecat {ℓ₁ ℓ₂ ℓ₃ : Level}(ℂ : ecategoryₗₑᵥ ℓ₁ ℓ₂ ℓ₃)(X : ecat.Obj ℂ) where
  open ecat (ℂ / X)
  open slice-ecat-defs ℂ X
  module ₒ = /Obj
  module ₐ {a b : Obj} = ||/Hom|| {a} {b}


module funct-slice-ecat-defs {ℓ₁ ℓ₂ ℓ₃ ℓ₄ ℓ₅ ℓ₆ : Level}{𝕃 : ecategoryₗₑᵥ ℓ₁ ℓ₂ ℓ₃}{ℝ : ecategoryₗₑᵥ ℓ₄ ℓ₅ ℓ₆}
                             (F : efunctorₗₑᵥ 𝕃 ℝ)
                             where
  private
    module 𝕃 = ecategory-aux 𝕃
    module ℝ = ecategory-aux ℝ
    module F = efunctor-aux F

  record Obj/ (R : ℝ.Obj) : Set (𝕃.ℓₒ ⊔ ℝ.ℓₐᵣᵣ) where
    field
      L : 𝕃.Obj
      ar : || ℝ.Hom (F.ₒ L) R ||

  record ||/Hom|| {R : ℝ.Obj}(A B : Obj/ R) : Set (𝕃.ℓₐᵣᵣ ⊔ ℝ.ℓ~) where
    private
      module A = Obj/ A
      module B = Obj/ B
    field
      arL : || 𝕃.Hom A.L B.L ||
      tr : B.ar ℝ.∘ F.ₐ arL ℝ.~ A.ar

  /Hom : {R : ℝ.Obj} → Obj/ R → Obj/ R → setoid {𝕃.ℓₐᵣᵣ ⊔ ℝ.ℓ~} {𝕃.ℓ~}
  /Hom {R} A B = sub-setoid (𝕃.Hom A.L B.L) (||/Hom||.arL {R} {A} {B})
               where module A = Obj/ A
                     module B = Obj/ B

  /idar :  {R : ℝ.Obj}(A : Obj/ R) → ||/Hom|| A A
  /idar {R} A = record
    { arL = 𝕃.idar A.L
    ; tr = ℝ.ridgg ℝ.r F.id
    }
    where module A = Obj/ A
  
  /cmp :  {R : ℝ.Obj}{A B C : Obj/ R}
             → ||/Hom|| B C → ||/Hom|| A B → ||/Hom|| A C
  /cmp {R} {A} {B} {C} g f = record
    { arL = g.arL 𝕃.∘ f.arL
    ; tr = ~proof C.ar ∘  F.ₐ (g.arL 𝕃.∘ f.arL)    ~[ ∘e (F.cmpˢ f.arL g.arL) r ] /
                   C.ar ∘ F.ₐ g.arL ∘ F.ₐ f.arL     ~[ ass ⊙ ∘e r g.tr ] /
                   B.ar ∘ F.ₐ f.arL                 ~[ f.tr ]∎
                   A.ar ∎
    }
    where module A = Obj/ A
          module B = Obj/ B
          module C = Obj/ C
          module f = ||/Hom|| f
          module g = ||/Hom|| g
          open ecategory-aux ℝ  
-- end funct-slice-ecat-defs


funct-slice-ecat : {ℓ₁ ℓ₂ ℓ₃ ℓ₄ ℓ₅ ℓ₆ : Level}{𝕃 : ecategoryₗₑᵥ ℓ₁ ℓ₂ ℓ₃}{ℝ : ecategoryₗₑᵥ ℓ₄ ℓ₅ ℓ₆}
                   (F : efunctorₗₑᵥ 𝕃 ℝ)
                     → ecat.Obj ℝ → ecategoryₗₑᵥ (ℓ₁ ⊔ ℓ₅) (ℓ₂ ⊔ ℓ₆) ℓ₃
funct-slice-ecat {𝕃 = 𝕃} {ℝ} F X = record
  { Obj = Obj/ X
  ; Hom = /Hom {X}
  ; isecat = record
           { _∘_ = /cmp
           ; idar = /idar
           ; ∘ext = λ _ _ _ _ → 𝕃.∘e
           ; lidax = λ _ → 𝕃.lid
           ; ridax = λ _ → 𝕃.rid
           ; assoc = λ _ _ _ → 𝕃.ass
           }
  }
  where module 𝕃 = ecategory-aux 𝕃
        open funct-slice-ecat-defs F

infix 2 _//_
_//_ : {ℓ₁ ℓ₂ ℓ₃ ℓ₄ ℓ₅ ℓ₆ : Level}{𝕃 : ecategoryₗₑᵥ ℓ₁ ℓ₂ ℓ₃}{ℝ : ecategoryₗₑᵥ ℓ₄ ℓ₅ ℓ₆}
       (F : efunctorₗₑᵥ 𝕃 ℝ)
          → ecat.Obj ℝ → ecategoryₗₑᵥ (ecat.ℓₒ 𝕃 ⊔ ecat.ℓₐᵣᵣ ℝ) (ecat.ℓₐᵣᵣ 𝕃 ⊔ ecat.ℓ~ ℝ) (ecat.ℓ~ 𝕃)
F // R = funct-slice-ecat F R


module funct-slice-ecat {ℓ₁ ℓ₂ ℓ₃ ℓ₄ ℓ₅ ℓ₆ : Level}{𝕃 : ecategoryₗₑᵥ ℓ₁ ℓ₂ ℓ₃}{ℝ : ecategoryₗₑᵥ ℓ₄ ℓ₅ ℓ₆}
                        (F : efunctorₗₑᵥ 𝕃 ℝ)(R : ecat.Obj ℝ) where
  open ecat (F // R)
  open funct-slice-ecat-defs F
  module ₒ = Obj/ {R}
  module ₐ {a b : Obj} = ||/Hom|| {R} {a} {b}
