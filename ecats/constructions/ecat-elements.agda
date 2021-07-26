
{-# OPTIONS --without-K #-}

module ecats.constructions.ecat-elements where

open import tt-basics.setoids using (setoid)
open import ecats.basic-defs.ecat-def&not
open import ecats.basic-defs.isomorphism
open import ecats.functors.defs.efunctor-d&n
open import ecats.functors.defs.id-on-objs
open import ecats.functors.defs.natural-iso
open import ecats.functors.defs.natural-transformation
open import ecats.functors.defs.presheaf
open import ecats.functors.defs.representable
open import ecats.constructions.opposite
open import ecats.constructions.functor-ecat
open import ecats.concr-ecats.Std-lev


-- The category of elements of a copresheaf

module ecat-of-coelements-defs {ℓₒ ℓₐ ℓ~ : Level}(ℂ : ecategoryₗₑᵥ ℓₒ ℓₐ ℓ~)(F : copresheafₗₑᵥ ℂ)
                               where
  private
    module ℂ = ecat ℂ
    module F = copresheafₗₑᵥ F

  record Obj : Set ℂ.ℓₙₒ~ where
    field
      Ob : ℂ.Obj
      el : || F.ₒ Ob ||

  el/ : {A : ℂ.Obj} → || F.ₒ A || → Obj
  el/ {A} x = record
        { Ob = A
        ; el = x
        }

  record Arr (A B : Obj) : Set ℂ.ℓₕₒₘ where
    private
      module A = Obj A
      module B = Obj B
    field
      ar : || ℂ.Hom A.Ob B.Ob ||
      eq : F.ₐ.ap ar A.el F.ₒ~ B.el

  ar/ : {A B : ℂ.Obj}(f : || ℂ.Hom A B ||){x : || F.ₒ A ||}{y : || F.ₒ B ||}
           → F.ₐ.ap f x F.ₒ~ y → Arr (el/ x) (el/ y)
  ar/ f eq = record
    { ar = f
    ; eq = eq
    }

  Hom : (A B : Obj) → setoid {ℂ.ℓₕₒₘ} {ℂ.ℓ~}
  Hom A B = record
    { object = Arr A B
    ; _∼_ = λ f f' → Arr.ar f ℂ.~ Arr.ar f'
    ; istteqrel = record
                { refl = λ _ → r
                ; sym = _ˢ
                ; tra = _⊙_
                }
    }
    where open ecategory-aux-only ℂ

  idar : (A : Obj) → Arr A A
  idar A = record
         { ar = ℂ.idar A.Ob
         ; eq = F.id A.el
         }
         where module A = Obj A

  cmp : {A B C : Obj} → Arr B C → Arr A B → Arr A C
  cmp {A} {B} {C} g f = record
    { ar = g.ar ℂ.∘ f.ar
    ; eq = ~proof F.ₐ.ap (g.ar ℂ.∘ f.ar) A.el      ~[ F.∘ax-rfˢ A.el ] /
                  F.ₐ.ap g.ar (F.ₐ.ap f.ar A.el)   ~[ F.ₐ.ext g.ar f.eq ] /
                  F.ₐ.ap g.ar B.el                 ~[ g.eq ]∎
                  C.el ∎
    }
    where module A = Obj A
          module B = Obj B
          module C = Obj C
          module f = Arr f
          module g = Arr g
          open F.ₒ C.Ob

  ~→iso-ar : {A : ℂ.Obj}{x x' : || F.ₒ A ||} → x F.ₒ~ x' → Arr (el/ x) (el/ x')
  ~→iso-ar {A} {x} {x'} eq = record
    { ar = ℂ.idar A
    ; eq = F.id {A} x FA.⊙ eq
    }
    where module FA = F.ₒ A

  ~→iso-inv : {A : ℂ.Obj}{x x' : || F.ₒ A ||} → x F.ₒ~ x' → Arr (el/ x') (el/ x)
  ~→iso-inv {A} eq = ~→iso-ar (eq FA.ˢ)
                where module FA = F.ₒ A
  
-- end ecat-of-elements-defs


ecat-coelmts : {ℓₒ ℓₐ ℓ~ : Level}{ℂ : ecategoryₗₑᵥ ℓₒ ℓₐ ℓ~}
                   → copresheafₗₑᵥ ℂ → ecategoryₗₑᵥ (ℓₒ ⊔ ℓₐ) (ℓₐ ⊔ ℓ~) ℓ~
ecat-coelmts {ℂ = ℂ} F = record
  { Obj = Obj
  ; Hom = Hom
  ; isecat = record
           { _∘_ = cmp
           ; idar = idar
           ; ∘ext = λ _ _ _ _ → ℂ.∘ext _ _ _ _
           ; lidax = λ _ → ℂ.lidax _
           ; ridax = λ _ → ℂ.ridax _
           ; assoc = λ _ _ _ → ℂ.assoc _ _ _
           }
  }
  where open ecat-of-coelements-defs ℂ F
        module ℂ = ecat ℂ

module ecat-coelmts {ℓₒ ℓₐ ℓ~ : Level}{ℂ : ecategoryₗₑᵥ ℓₒ ℓₐ ℓ~}(F : copresheafₗₑᵥ ℂ) where
  open ecat-of-coelements-defs ℂ F hiding (el/; ar/)
  open ecat-of-coelements-defs ℂ F using (el/; ar/) public
  open iso-defs (ecat-coelmts F)
  private
    module ℂ = ecat ℂ
    module F = copresheafₗₑᵥ F
  module ₒ (A : Obj) where
    open Obj A public
  module ₐ {A B : Obj}(f : Arr A B) where
    open Arr f public
  ~iso : {A : ℂ.Obj}{x x' : || F.ₒ A ||} → x F.ₒ~ x' → (el/ x) ≅ₒ (el/ x')
  ~iso {A} eq = record
    { a12 = ~→iso-ar eq
    ; a21 = ~→iso-inv eq
    ; isop = record
           { iddom = ℂ.ridax (ℂ.idar A)
           ; idcod = ℂ.ridax (ℂ.idar A)
           }
    }
  module ~iso {A : ℂ.Obj}{x x' : || F.ₒ A ||}(eq : x F.ₒ~ x') = _≅ₒ_ (~iso eq)




-- The category of elements of a presheaf

module ecat-of-elements-defs {ℓₒ ℓₐ ℓ~ : Level}(ℂ : ecategoryₗₑᵥ ℓₒ ℓₐ ℓ~)(F : presheafₗₑᵥ ℂ)
                             where
  private
    module ℂ = ecat ℂ
    module F = presheafₗₑᵥ F
  open ecat-of-coelements-defs (ℂ ᵒᵖ) F using (Obj; el/) public

  record Arr (A B : Obj) : Set ℂ.ℓₕₒₘ where
    private
      module A = Obj A
      module B = Obj B
    field
      ar : || ℂ.Hom A.Ob B.Ob ||
      eq : F.ₐ.ap ar B.el F.ₒ~ A.el

  ar/ : {A B : ℂ.Obj}(f : || ℂ.Hom A B ||){x : || F.ₒ A ||}{y : || F.ₒ B ||}
           → F.ₐ.ap f y F.ₒ~ x → Arr (el/ x) (el/ y)
  ar/ f eq = record
    { ar = f
    ; eq = eq
    }

  Hom : (A B : Obj) → setoid {ℂ.ℓₕₒₘ} {ℂ.ℓ~}
  Hom A B = record
    { object = Arr A B
    ; _∼_ = λ f f' → Arr.ar f ℂ.~ Arr.ar f'
    ; istteqrel = record
                { refl = λ _ → r
                ; sym = _ˢ
                ; tra = _⊙_
                }
    }
    where open ecategory-aux-only ℂ

  idar : (A : Obj) → Arr A A
  idar A = record
         { ar = ℂ.idar A.Ob
         ; eq = F.id A.el
         }
         where module A = Obj A

  cmp : {A B C : Obj} → Arr B C → Arr A B → Arr A C
  cmp {A} {B} {C} g f = record
    { ar = g.ar ℂ.∘ f.ar
    ; eq = ~proof F.ₐ.ap (g.ar ℂ.∘ f.ar) C.el      ~[ F.∘ax-rfˢ C.el ] /
                  F.ₐ.ap f.ar (F.ₐ.ap g.ar C.el)   ~[ F.ₐ.ext f.ar g.eq ] /
                  F.ₐ.ap f.ar B.el                 ~[ f.eq ]∎
                  A.el ∎
    }
    where module A = Obj A
          module B = Obj B
          module C = Obj C
          module f = Arr f
          module g = Arr g
          open F.ₒ A.Ob

  ~→iso-ar : {A : ℂ.Obj}{x x' : || F.ₒ A ||} → x F.ₒ~ x' → Arr (el/ x) (el/ x')
  ~→iso-ar {A} {x} {x'} eq = record
    { ar = ℂ.idar A
    ; eq = F.id {A} x' FA.⊙ eq FA.ˢ
    }
    where module FA = F.ₒ A

  ~→iso-inv : {A : ℂ.Obj}{x x' : || F.ₒ A ||} → x F.ₒ~ x' → Arr (el/ x') (el/ x)
  ~→iso-inv {A} eq = ~→iso-ar (eq FA.ˢ)
                where module FA = F.ₒ A

-- end ecat-of-elements-defs


ecat-elmts : {ℓₒ ℓₐ ℓ~ : Level}{ℂ : ecategoryₗₑᵥ ℓₒ ℓₐ ℓ~}
                 → presheafₗₑᵥ ℂ → ecategoryₗₑᵥ (ℓₒ ⊔ ℓₐ) (ℓₐ ⊔ ℓ~) ℓ~
ecat-elmts {ℂ = ℂ} F = record
  { Obj = Obj
  ; Hom = Hom
  ; isecat = record
           { _∘_ = cmp
           ; idar = idar
           ; ∘ext = λ _ _ _ _ → ℂ.∘ext _ _ _ _
           ; lidax = λ _ → ℂ.lidax _
           ; ridax = λ _ → ℂ.ridax _
           ; assoc = λ _ _ _ → ℂ.assoc _ _ _
           }
  }
  where open ecat-of-elements-defs ℂ F
        module ℂ = ecat ℂ


module ecat-elmts {ℓₒ ℓₐ ℓ~ : Level}{ℂ : ecategoryₗₑᵥ ℓₒ ℓₐ ℓ~}(F : presheafₗₑᵥ ℂ) where
  open ecat-of-elements-defs ℂ F hiding (el/; ar/)
  open ecat-of-elements-defs ℂ F using (el/; ar/) public
  open iso-defs (ecat-elmts F)
  private
    module ℂ = ecat ℂ
    module F = presheafₗₑᵥ F
  module ₒ (A : Obj) where
    open Obj A public
  module ₐ {A B : Obj}(f : Arr A B) where
    open Arr f public
  ~iso : {A : ℂ.Obj}{x x' : || F.ₒ A ||} → x F.ₒ~ x' → (el/ x) ≅ₒ (el/ x')
  ~iso {A} eq = record
    { a12 = ~→iso-ar eq
    ; a21 = ~→iso-inv eq
    ; isop = record
           { iddom = ℂ.ridax (ℂ.idar A)
           ; idcod = ℂ.ridax (ℂ.idar A)
           }
    }
  module ~iso {A : ℂ.Obj}{x x' : || F.ₒ A ||}(eq : x F.ₒ~ x') = _≅ₒ_ (~iso eq)


-- The opposite of the category of coelements of a presheaf F is isomorphic
-- to the category of elements of F via an identity on objects functors.
-- (Which is also sort of identity on arrows.)

opel-is-coel : {ℓₒ ℓₐ ℓ~ : Level}{ℂ : ecategoryₗₑᵥ ℓₒ ℓₐ ℓ~}(F : presheafₗₑᵥ ℂ)
                  → ecat.isecat (ecat-elmts F) ≅ᶜᵃᵗ ecat.isecat (ecat-coelmts F ᵒᵖ)
opel-is-coel {ℂ = ℂ} F = record
  { a12 = record
        { ₐ = λ {A} {B} f → record { ar = ∫F.ₐ.ar f ; eq = ∫F.ₐ.eq f }
        ; isfctr = record
                 { ext = λ {A} {B} {f} {f'} → Id∫F.ext {A} {B} {f} {f'}
                 ; id = λ {A} → Id∫F.id {A}
                 ; cmp = Id∫F.cmp
                 }
        }
  ; a21 = record
        { ₐ = λ {A} {B} f → record { ar = ∫Fᵒ.ₐ.ar f ; eq = ∫Fᵒ.ₐ.eq f }
        ; isfctr = record
                 { ext = λ {A} {B} {f} {f'} → Id∫Fᵒ.ext {B} {A} {f} {f'}
                 ; id = λ {A} → Id∫Fᵒ.id {A}
                 ; cmp = λ f g → Id∫Fᵒ.cmp g f
                 }
        }
  ; isisopair = record
              { iddom = λ f → ∫F.r {f = f}
              ; idcod = λ f → ∫Fᵒ.r {f = f}
              }
  }
  where module ∫F where
          open ecat-elmts F public
          open ecategory-aux-only (ecat-elmts F) using (r) public
        module ∫Fᵒ where
          open ecat-coelmts F public
          open ecategory-aux-only (ecat-coelmts F) using (r) public
        module Id∫F = efunctor-aux (IdF {ℂ = ecat-elmts F})
        module Id∫Fᵒ = efunctor-aux (IdF {ℂ = ecat-coelmts F})



-- -- The category of elements of a presheaf on a locally small 

-- module ecat-of-elements-defs {ℂ : ecategory}(F : presheaf ℂ) where
--   private
--     module ℂ = ecat ℂ
--     module F = presheaf F

--   record Obj : Set₁ where
--     field
--       Ob : ℂ.Obj
--       el : || F.ₒ Ob ||

--   record Arr (A B : Obj) : Set where
--     private
--       module A = Obj A
--       module B = Obj B
--       module FA = F.ₒ A.Ob
--       module FB = F.ₒ B.Ob
--     field
--       ar : || ℂ.Hom A.Ob B.Ob ||
--       eq : F.ₐ.ap ar B.el FA.~ A.el


-- -- end ecat-of-elements-defs
