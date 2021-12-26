{-# OPTIONS --without-K #-}

module ecats.constructions.slice-ecat where

open import Agda.Primitive
open import tt-basics.basics using (prod; pair)
open import tt-basics.setoids hiding (||_||)
open import ecats.basic-defs.ecat-def&not
open import ecats.functors.defs.efunctor-d&n
open import ecats.functors.defs.natural-transformation
open import ecats.constructions.opposite


-- slice over an object

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
