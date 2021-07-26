{-# OPTIONS --without-K #-}

module ecats.constructions.slice-ecat where

open import Agda.Primitive
open import tt-basics.basics using (prod; pair)
open import tt-basics.setoids hiding (||_||)
open import ecats.basic-defs.ecat-def&not
open import ecats.functors.defs.efunctor-d&n
open import ecats.functors.defs.natural-transformation
open import ecats.constructions.opposite



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




module funct-slice-ecat-defs {ℓ₁ ℓ₂ ℓ₃ ℓ₄ ℓ₅ ℓ₆ : Level}{ℂ : ecategoryₗₑᵥ ℓ₁ ℓ₂ ℓ₃}{𝔻 : ecategoryₗₑᵥ ℓ₄ ℓ₅ ℓ₆}
                             (F : efunctorₗₑᵥ ℂ 𝔻)(Y : ecat.Obj 𝔻)
                             where
  private
    module ℂ = ecategory-aux ℂ
    module 𝔻 = ecategory-aux 𝔻
    module F = efunctor-aux F

  record Obj/ : Set (ℂ.ℓₒ ⊔ 𝔻.ℓₐᵣᵣ) where
    field
      L : ℂ.Obj
      ar : || 𝔻.Hom (F.ₒ L) Y ||

  record ||Hom/|| (A B : Obj/) : Set (ℂ.ℓₐᵣᵣ ⊔ 𝔻.ℓ~) where
    private
      module A = Obj/ A
      module B = Obj/ B
    field
      arL : || ℂ.Hom A.L B.L ||
      tr : B.ar 𝔻.∘ F.ₐ arL 𝔻.~ A.ar

  Hom/ :  Obj/ → Obj/ → setoid {ℂ.ℓₐᵣᵣ ⊔ 𝔻.ℓ~} {ℂ.ℓ~}
  Hom/ A B = sub-setoid (ℂ.Hom A.L B.L) (||Hom/||.arL {A} {B})
               where module A = Obj/ A
                     module B = Obj/ B

  idar/ :  (A : Obj/) → ||Hom/|| A A
  idar/ A = record
    { arL = ℂ.idar A.L
    ; tr = 𝔻.ridgg 𝔻.r F.id
    }
    where module A = Obj/ A
  
  cmp/ :  {A B C : Obj/}
             → ||Hom/|| B C → ||Hom/|| A B → ||Hom/|| A C
  cmp/ {A} {B} {C} g f = record
    { arL = g.arL ℂ.∘ f.arL
    ; tr = ~proof C.ar ∘  F.ₐ (g.arL ℂ.∘ f.arL)    ~[ ∘e (F.cmpˢ f.arL g.arL) r ] /
                   C.ar ∘ F.ₐ g.arL ∘ F.ₐ f.arL     ~[ ass ⊙ ∘e r g.tr ] /
                   B.ar ∘ F.ₐ f.arL                 ~[ f.tr ]∎
                   A.ar ∎
    }
    where module A = Obj/ A
          module B = Obj/ B
          module C = Obj/ C
          module f = ||Hom/|| f
          module g = ||Hom/|| g
          open ecategory-aux 𝔻  
-- end funct-slice-ecat-defs


funct-slice-ecat : {ℓ₁ ℓ₂ ℓ₃ ℓ₄ ℓ₅ ℓ₆ : Level}{ℂ : ecategoryₗₑᵥ ℓ₁ ℓ₂ ℓ₃}{𝔻 : ecategoryₗₑᵥ ℓ₄ ℓ₅ ℓ₆}
                   (F : efunctorₗₑᵥ ℂ 𝔻) → ecat.Obj 𝔻
                     → ecategoryₗₑᵥ (ecat.ℓₒ ℂ ⊔ ecat.ℓₐᵣᵣ 𝔻) (ecat.ℓₐᵣᵣ ℂ ⊔ ecat.ℓ~ 𝔻) (ecat.ℓ~ ℂ)
funct-slice-ecat {ℂ = ℂ} {𝔻} F Y = record
  { Obj = Obj/
  ; Hom = Hom/
  ; isecat = record
           { _∘_ = cmp/
           ; idar = idar/
           ; ∘ext = λ _ _ _ _ → ℂ.∘e
           ; lidax = λ _ → ℂ.lid
           ; ridax = λ _ → ℂ.rid
           ; assoc = λ _ _ _ → ℂ.ass
           }
  }
  where module ℂ = ecategory-aux ℂ
        open funct-slice-ecat-defs F Y

infix 2 _↓ₒ_
_↓ₒ_ : {ℓ₁ ℓ₂ ℓ₃ ℓ₄ ℓ₅ ℓ₆ : Level}{ℂ : ecategoryₗₑᵥ ℓ₁ ℓ₂ ℓ₃}{𝔻 : ecategoryₗₑᵥ ℓ₄ ℓ₅ ℓ₆}
       (F : efunctorₗₑᵥ ℂ 𝔻) → ecat.Obj 𝔻
          → ecategoryₗₑᵥ (ecat.ℓₒ ℂ ⊔ ecat.ℓₐᵣᵣ 𝔻) (ecat.ℓₐᵣᵣ ℂ ⊔ ecat.ℓ~ 𝔻) (ecat.ℓ~ ℂ)
F ↓ₒ Y = funct-slice-ecat F Y


module funct-slice-ecat {ℓ₁ ℓ₂ ℓ₃ ℓ₄ ℓ₅ ℓ₆ : Level}{ℂ : ecategoryₗₑᵥ ℓ₁ ℓ₂ ℓ₃}{𝔻 : ecategoryₗₑᵥ ℓ₄ ℓ₅ ℓ₆}
                        (F : efunctorₗₑᵥ ℂ 𝔻)(Y : ecat.Obj 𝔻) where
  open ecat (F ↓ₒ Y) using (Obj; Hom)
  open funct-slice-ecat-defs F Y
  module ₒ = Obj/
  module ₐ {A B : Obj}(f : || Hom A B ||) = ||Hom/|| {A} {B} f


-- the slice under a functor between locally small categories is locally small
funct-slice-ecat-lc : {ℂ 𝔻 : ecategory}(F : efunctor ℂ 𝔻) → ecat.Obj 𝔻
                     → ecategory
funct-slice-ecat-lc = funct-slice-ecat





module slice-funct-ecat-defs {ℓ₁ ℓ₂ ℓ₃ ℓ₄ ℓ₅ ℓ₆ : Level}{ℂ : ecategoryₗₑᵥ ℓ₁ ℓ₂ ℓ₃}{𝔻 : ecategoryₗₑᵥ ℓ₄ ℓ₅ ℓ₆}
                             (F : efunctorₗₑᵥ ℂ 𝔻)(Y : ecat.Obj 𝔻)
                             where
  private
    module ℂ = ecategory-aux ℂ
    module 𝔻 = ecategory-aux 𝔻
    module F = efunctor-aux F

  record /Obj : Set (ℂ.ℓₒ ⊔ 𝔻.ℓₐᵣᵣ) where
    field
      R : ℂ.Obj
      ar : || 𝔻.Hom Y (F.ₒ R) ||

  record ||/Hom|| (A B : /Obj) : Set (ℂ.ℓₐᵣᵣ ⊔ 𝔻.ℓ~) where
    private
      module A = /Obj A
      module B = /Obj B
    field
      arR : || ℂ.Hom A.R B.R ||
      tr : F.ₐ arR 𝔻.∘ A.ar 𝔻.~ B.ar

  /Hom : /Obj → /Obj → setoid {ℂ.ℓₐᵣᵣ ⊔ 𝔻.ℓ~} {ℂ.ℓ~}
  /Hom A B = sub-setoid (ℂ.Hom A.R B.R) (||/Hom||.arR {A} {B})
               where module A = /Obj A
                     module B = /Obj B

  /idar : (A : /Obj) → ||/Hom|| A A
  /idar A = record
    { arR = ℂ.idar A.R
    ; tr = 𝔻.lidgg 𝔻.r F.id
    }
    where module A = /Obj A
  
  /cmp : {A B C : /Obj}
             → ||/Hom|| B C → ||/Hom|| A B → ||/Hom|| A C
  /cmp {A} {B} {C} g f = record
    { arR = g.arR ℂ.∘ f.arR
    ; tr = ~proof F.ₐ (g.arR ℂ.∘ f.arR) ∘ A.ar    ~[ ∘e r (F.cmpˢ f.arR g.arR) ⊙ assˢ ] /
                  F.ₐ g.arR ∘ F.ₐ f.arR ∘ A.ar     ~[ ∘e f.tr r ] /
                  F.ₐ g.arR ∘ B.ar                 ~[ g.tr ]∎
                  C.ar ∎
    }
    where module A = /Obj A
          module B = /Obj B
          module C = /Obj C
          module f = ||/Hom|| f
          module g = ||/Hom|| g
          open ecategory-aux 𝔻  
-- end slice-funct-ecat-defs


slice-funct-ecat : {ℓ₁ ℓ₂ ℓ₃ ℓ₄ ℓ₅ ℓ₆ : Level}{ℂ : ecategoryₗₑᵥ ℓ₁ ℓ₂ ℓ₃}{𝔻 : ecategoryₗₑᵥ ℓ₄ ℓ₅ ℓ₆}
                   (F : efunctorₗₑᵥ ℂ 𝔻) → ecat.Obj 𝔻
                     → ecategoryₗₑᵥ (ecat.ℓₒ ℂ ⊔ ecat.ℓₐᵣᵣ 𝔻) (ecat.ℓₐᵣᵣ ℂ ⊔ ecat.ℓ~ 𝔻) (ecat.ℓ~ ℂ)
slice-funct-ecat {ℂ = ℂ} {𝔻} F Y = record
  { Obj = /Obj
  ; Hom = /Hom
  ; isecat = record
           { _∘_ = /cmp
           ; idar = /idar
           ; ∘ext = λ _ _ _ _ → ℂ.∘e
           ; lidax = λ _ → ℂ.lid
           ; ridax = λ _ → ℂ.rid
           ; assoc = λ _ _ _ → ℂ.ass
           }
  }
  where module ℂ = ecategory-aux ℂ
        open slice-funct-ecat-defs F Y

infix 2 _ₒ↓_
_ₒ↓_ : {ℓ₁ ℓ₂ ℓ₃ ℓ₄ ℓ₅ ℓ₆ : Level}{ℂ : ecategoryₗₑᵥ ℓ₁ ℓ₂ ℓ₃}{𝔻 : ecategoryₗₑᵥ ℓ₄ ℓ₅ ℓ₆}
       (Y : ecat.Obj 𝔻)(F : efunctorₗₑᵥ ℂ 𝔻)
          → ecategoryₗₑᵥ (ecat.ℓₒ ℂ ⊔ ecat.ℓₐᵣᵣ 𝔻) (ecat.ℓₐᵣᵣ ℂ ⊔ ecat.ℓ~ 𝔻) (ecat.ℓ~ ℂ)
Y ₒ↓ F = slice-funct-ecat F Y


module slice-funct-ecat {ℓ₁ ℓ₂ ℓ₃ ℓ₄ ℓ₅ ℓ₆ : Level}{ℂ : ecategoryₗₑᵥ ℓ₁ ℓ₂ ℓ₃}{𝔻 : ecategoryₗₑᵥ ℓ₄ ℓ₅ ℓ₆}
                        (F : efunctorₗₑᵥ ℂ 𝔻)(Y : ecat.Obj 𝔻) where
  open ecat (Y ₒ↓ F) using (Obj; Hom)
  open slice-funct-ecat-defs F Y
  module ₒ = /Obj
  module ₐ {A B : Obj}(f : || Hom A B ||) = ||/Hom|| {A} {B} f
