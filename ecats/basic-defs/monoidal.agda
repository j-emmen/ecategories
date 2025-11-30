{-# OPTIONS --without-K #-}

module ecats.basic-defs.monoidal where

open import ecats.basic-defs.ecat-def&not
open import ecats.functors.defs.efunctor-d&n
open import ecats.functors.defs.natural-transformation
open import ecats.functors.defs.natural-iso
open import ecats.concr-ecats.ecat-ecats
open import ecats.constructions.functor-ecat



module tensor-efunctor-not {ℓₒ ℓₐ ℓ~ : Level}{ℂ : ecategoryₗₑᵥ ℓₒ ℓₐ ℓ~}
                           (tenf : efunctorₗₑᵥ ℂ [ ℂ , ℂ ]ᶜᵃᵗ)
                           where
  private
    module ℂ = ecat ℂ
    module Funℂ = ecat [ ℂ , ℂ ]ᶜᵃᵗ

  module fst where
    open efctr tenf public
    module ₐ {A B : ℂ.Obj} (f : || ℂ.Hom A B ||) = natural-transformation (ₐ f)

  l⊗ : ℂ.Obj →  efunctor ℂ ℂ
  l⊗ = fst.ₒ
  module l⊗ (A : ℂ.Obj) = efctr (l⊗ A)
  ⊗r : ℂ.Obj →  efunctor ℂ ℂ
  ⊗r A = record
    { FObj = λ X → l⊗.ₒ X A
    ; FHom = λ {X} {Y} f → fst.ₐ.fnc f {A}
    ; isF = record
          { ext = λ eq → fst.ext eq A
          ; id = λ {X} → fst.id {X} A
          ; cmp = λ f g → fst.cmp f g A
          }
    }
  module ⊗r (A : ℂ.Obj) = efctr (⊗r A)
  ⊗ₐsq : {A₁ B₁ A₂ B₂ : ℂ.Obj} (f₁ : || ℂ.Hom A₁ B₁ ||) (f₂ : || ℂ.Hom A₂ B₂ ||)
             → ⊗r.ₐ B₂ f₁ ℂ.∘ l⊗.ₐ A₁ f₂ ℂ.~ l⊗.ₐ B₁ f₂ ℂ.∘ ⊗r.ₐ A₂ f₁
  ⊗ₐsq f₁ f₂ = fst.ₐ.nat f₁ f₂
  ⊗ₐsqˢ : {A₁ B₁ A₂ B₂ : ℂ.Obj} (f₁ : || ℂ.Hom A₁ B₁ ||) (f₂ : || ℂ.Hom A₂ B₂ ||)
             → l⊗.ₐ B₁ f₂ ℂ.∘ ⊗r.ₐ A₂ f₁ ℂ.~ ⊗r.ₐ B₂ f₁ ℂ.∘ l⊗.ₐ A₁ f₂
  ⊗ₐsqˢ f₁ f₂ = fst.ₐ.natˢ f₁ f₂
  ⊗rₐ : {A B : ℂ.Obj} (f : || ℂ.Hom A B ||) → natural-transformation (⊗r A) (⊗r B)
  ⊗rₐ {A} {B} f = record
    { fnc = λ {X} → l⊗.ₐ X f
    ; nat = λ f₁ → ⊗ₐsqˢ f₁ f
    }

  ⊗ass-lfst : efunctorₗₑᵥ ℂ  [ ℂ , [ ℂ , ℂ ]ᶜᵃᵗ ]ᶜᵃᵗ
  ⊗ass-lfst = record
    { FObj = λ X →  tenf ○ (l⊗ X)
    ; FHom = λ f → natt-fctr-post tenf (fst.ₐ f)
    ; isF = record
          { ext = λ eq X Y → fst.ext (fst.ext eq X) Y
          ; id = λ X Y → fst.ext (fst.id X) Y ⊙ fst.id Y
          ; cmp = λ f g X Y → fst.cmp _ _ Y ⊙ fst.ext (fst.cmp f g X) Y
          }
    }
    where open ecategory-aux-only ℂ using (r; _⊙_)

  ⊗ass-llst : efunctorₗₑᵥ ℂ  [ ℂ , [ ℂ , ℂ ]ᶜᵃᵗ ]ᶜᵃᵗ
  ⊗ass-llst = record
    { FObj = λ X → postcmp-Fctr (l⊗ X) ○ tenf
    ; FHom = λ f → natt-fctr-pre tenf (postcmp-Fctr-natt (fst.ₐ f))
    ; isF = record
          { ext = λ eq _ _ → fst.ext eq _
          ; id = λ _ _ → fst.id _
          ; cmp = λ f g _ _ → fst.cmp f g _
          }
    }
    where open ecategory-aux-only ℂ using (r; _⊙_)


  _⊗ₒ_ : ℂ.Obj → ℂ.Obj → ℂ.Obj
  A ⊗ₒ B = l⊗.ₒ A B
  _⊗ₐ_ : {A₁ B₁ A₂ B₂ : ℂ.Obj} → || ℂ.Hom A₁ B₁ || → || ℂ.Hom A₂ B₂ ||
             → || ℂ.Hom (A₁ ⊗ₒ A₂) (B₁ ⊗ₒ B₂) ||
  _⊗ₐ_ {A₁} {B₁} {A₂} {B₂} f₁ f₂ = l⊗.ₐ B₁ f₂ ℂ.∘ ⊗r.ₐ A₂ f₁
  -- NB:
  -- ℂ.idar X ⊗ₐ f = l⊗.ₐ X f ℂ.∘ ⊗r.ₐ A ℂ.idar X ~ l⊗.ₐ X f ℂ.∘ ℂ.idar (X ⊗ₒ A)
  -- f ⊗ₐ ℂ.idar X = l⊗.ₐ B ℂ.idar X ℂ.∘ ⊗r.ₐ X f ~ ℂ.idar (B ⊗ₒ X) ℂ.∘ ⊗r.ₐ X f
-- end tensor-efunctor-not


module monoidal-defs  {ℓₒ ℓₐ ℓ~ : Level}(ℂ : ecategoryₗₑᵥ ℓₒ ℓₐ ℓ~) where
  private
    module ℂ = ecat ℂ


  record is-tensor-with-unit (I : ℂ.Obj) (tenf : efunctorₗₑᵥ ℂ [ ℂ , ℂ ]ᶜᵃᵗ)
                             : Set ℂ.ℓₐₗₗ where
    open tensor-efunctor-not tenf
    field
      lun : natural-iso (l⊗ I) IdF
      run : natural-iso (⊗r I) IdF
      ass : natural-iso ⊗ass-lfst ⊗ass-llst
    module lun = natural-iso lun
    module run = natural-iso run
    private
      module ass = natural-iso ass
      module ass₂ (M : ℂ.Obj) = natural-transformation (ass.fnc {M})
      module ass₃ (M N : ℂ.Obj) = natural-transformation (ass₂.fnc M {N})    
    field
      trng : {A B : ℂ.Obj}
                → (l⊗.ₐ A (lun.fnc {B})) ℂ.∘ ass₃.fnc A I {B}
                          ℂ.~ ⊗r.ₐ B (run.fnc {A})
      pntg : {A B C D : ℂ.Obj}
                →  l⊗.ₐ A (ass₃.fnc B C {D}) ℂ.∘ ass₃.fnc A (B ⊗ₒ C) {D}
                                            ℂ.∘ ⊗r.ₐ D (ass₃.fnc A B {C})
                      ℂ.~ ass₃.fnc A B {C ⊗ₒ D} ℂ.∘ ass₃.fnc (A ⊗ₒ B) C {D}
-- end monoidal-defs


record is-monoidal {ℓₒ ℓₐ ℓ~ : Level}(ℂ : ecategoryₗₑᵥ ℓₒ ℓₐ ℓ~) : Set (ecat.ℓₐₗₗ ℂ) where
  open ecat ℂ using (Obj)
  open  monoidal-defs ℂ
  field
    I : Obj
    tenf : efunctorₗₑᵥ ℂ [ ℂ , ℂ ]ᶜᵃᵗ
    pf : is-tensor-with-unit I tenf
  open tensor-efunctor-not tenf public
  open is-tensor-with-unit pf public
  module ass where
    module ₁ = natural-iso ass
    module ₂ (X : Obj) = natural-transformation (₁.fnc {X})
    module ₃ (X Y : Obj) = natural-transformation (₂.fnc X {Y})
