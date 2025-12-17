{-# OPTIONS --without-K #-}

module ecats.basic-defs.monoidal where

open import ecats.basic-defs.ecat-def&not
open import ecats.isomorphism
open import ecats.functors.defs.efunctor-d&n
open import ecats.functors.defs.natural-transformation
open import ecats.functors.defs.natural-iso
open import ecats.constructions.functor-ecat



module tensor-efunctor-not {ℓₒ ℓₐ ℓ~ : Level}{ℂ : ecategoryₗₑᵥ ℓₒ ℓₐ ℓ~}
                           (tenf : efunctorₗₑᵥ ℂ [ ℂ , ℂ ]ᶜᵃᵗ)
                           where

  open uncurry-efunctor-into-functor-cat tenf public
       renaming ( rₒ to ⊗rₒ; rl~lr to ⊗ₐsq; lr~rl to ⊗ₐsqˢ
                ; rₐ to ⊗rₐ; ₒ to _⊗ₒ_; ₐ to _⊗ₐ_; ext to ⊗ext; pres-iso-pair to ⊗pres-iso-pair )

  module l⊗ = l
  module l⊗ₒ = lₒ
  module l⊗ₐ = lₐ

  ⊗ass-lfst : efunctorₗₑᵥ ℂ  [ ℂ , [ ℂ , ℂ ]ᶜᵃᵗ ]ᶜᵃᵗ
  ⊗ass-lfst = record
    { FObj = λ X →  tenf ○ (l⊗.ₒ X)
    ; FHom = λ f → natt-fctr-post tenf (l⊗.ₐ f)
    ; isF = record
          { ext = λ eq X Y → l⊗.ext (l.ext eq X) Y
          ; id = λ X Y → l⊗.ext (l.id X) Y ⊙ l⊗.id Y
          ; cmp = λ f g X Y → l⊗.cmp _ _ Y ⊙ l⊗.ext (l⊗.cmp f g X) Y
          }
    }
    where open ecategory-aux-only ℂ using (_⊙_)

  ⊗ass-llst : efunctorₗₑᵥ ℂ  [ ℂ , [ ℂ , ℂ ]ᶜᵃᵗ ]ᶜᵃᵗ
  ⊗ass-llst = record
    { FObj = λ X → postcmp-Fctr (l⊗.ₒ X) ○ tenf
    ; FHom = λ f → natt-fctr-pre tenf (postcmp-Fctr-natt (l⊗.ₐ f))
    ; isF = record
          { ext = λ eq _ _ → l⊗.ext eq _
          ; id = λ _ _ → l⊗.id _
          ; cmp = λ f g _ _ → l⊗.cmp f g _
          }
    }
-- end tensor-efunctor-not


module monoidal-defs  {ℓₒ ℓₐ ℓ~ : Level}(ℂ : ecategoryₗₑᵥ ℓₒ ℓₐ ℓ~) where
  private
    module ℂ = ecat ℂ


  record is-tensor-with-unit (I : ℂ.Obj) (tenf : efunctorₗₑᵥ ℂ [ ℂ , ℂ ]ᶜᵃᵗ)
                             : Set ℂ.ℓₐₗₗ where
    open tensor-efunctor-not tenf
    field
      lun : natural-iso (l⊗.ₒ I) IdF
      run : natural-iso (⊗rₒ I) IdF
      ass : natural-iso ⊗ass-lfst ⊗ass-llst
    module lun = natural-iso lun
    module run = natural-iso run
    private
      module ass₁ = natural-iso ass
      module ass₂ (M : ℂ.Obj) = natural-transformation (ass₁.fnc {M})
      module ass₃ (M N : ℂ.Obj) = natural-transformation (ass₂.fnc M {N})    
    field
      trng : {A B : ℂ.Obj}
                → (l⊗ₒ.ₐ A (lun.fnc {B})) ℂ.∘ ass₃.fnc A I {B}
                          ℂ.~ ⊗rₒ.ₐ B (run.fnc {A})
      pntg : {A B C D : ℂ.Obj}
                →  l⊗ₒ.ₐ A (ass₃.fnc B C {D}) ℂ.∘ ass₃.fnc A (B ⊗ₒ C) {D}
                                            ℂ.∘ ⊗rₒ.ₐ D (ass₃.fnc A B {C})
                      ℂ.~ ass₃.fnc A B {C ⊗ₒ D} ℂ.∘ ass₃.fnc (A ⊗ₒ B) C {D}
    module ass where
      open natural-iso ass public hiding (fnc; fnc⁻¹; nat; nat⁻¹; natˢ; nat⁻¹ˢ)
      open uncurry-natt-into-functor-cat natt public
           renaming (l to lft; nat to lcnat; natˢ to lcnatˢ )
           hiding (fnc; rnat; rnatˢ)
      open module aux1 (X : ℂ.Obj) = uncurry-natt-into-functor-cat (lft {X}) public
                                     renaming ( lnat to cnat; lnatˢ to cnatˢ
                                              ; nat to crnat; natˢ to crnatˢ )
      open natural-transformation natt⁻¹ public
           renaming (fnc to lft⁻¹; nat to lnat⁻¹; natˢ to lnat⁻¹ˢ)
      module ⁻¹ (X : ℂ.Obj) = uncurry-natt-into-functor-cat (lft⁻¹ {X})
                             renaming ( lnat to cnat; lnatˢ to cnatˢ
                                      ; nat to crnat; natˢ to crnatˢ )
      nat :  {A B C A' B' C' : ℂ.Obj} (f : || ℂ.Hom A A' ||)
             (g : || ℂ.Hom B B' ||) (h : || ℂ.Hom C C' ||)
               → fnc A' B' {C'} ℂ.∘ ((f ⊗ₐ g) ⊗ₐ h)
                     ℂ.~ (f ⊗ₐ (g ⊗ₐ h)) ℂ.∘ fnc A B {C}
      nat {A} {B} {C} {A'} {B'} {C'} f g h = ~proof
        fnc A' B' {C'} ℂ.∘ ((f ⊗ₐ g) ⊗ₐ h)   ~[ r ] /
        fnc A' B' {C'} ℂ.∘ ⊗rₒ.ₐ C' (f ⊗ₐ g) ℂ.∘ l⊗ₒ.ₐ (A ⊗ₒ B) h
               ~[ ℂass ⊙ ∘e r (∘e (l⊗.∘ax-rfˢ C') r ⊙ lcnat f g C') ⊙ ℂassˢ ] /
        (f ⊗ₐ (⊗rₒ.ₐ C' g)) ℂ.∘ fnc A B {C'} ℂ.∘ l⊗ₒ.ₐ (A ⊗ₒ B) h
               ~[ ∘e (rnat A B h) r ] /
        (f ⊗ₐ (⊗rₒ.ₐ C' g)) ℂ.∘ l⊗ₒ.ₐ A (l⊗ₒ.ₐ B h) ℂ.∘ fnc A B {C}
               ~[ ℂass ⊙ ∘e r (ℂassˢ ⊙ ∘e (l⊗ₒ.∘ax-rf A) r) ]∎
        (f ⊗ₐ (g ⊗ₐ h)) ℂ.∘ fnc A B {C} ∎
        where open ecategory-aux-only ℂ renaming (ass to ℂass; assˢ to ℂassˢ)
-- end monoidal-defs


record is-monoidal-cat {ℓₒ ℓₐ ℓ~ : Level}(ℂ : ecategoryₗₑᵥ ℓₒ ℓₐ ℓ~) : Set (ecat.ℓₐₗₗ ℂ) where
  open ecat ℂ using (Obj)
  open  monoidal-defs ℂ
  field
    I : Obj
    tenf : efunctorₗₑᵥ ℂ [ ℂ , ℂ ]ᶜᵃᵗ
    pf : is-tensor-with-unit I tenf
  open tensor-efunctor-not tenf public
  open is-tensor-with-unit pf public

module moncat {ℓₒ ℓₐ ℓ~ : Level} {𝕏 : ecategoryₗₑᵥ ℓₒ ℓₐ ℓ~} (𝕏mon : is-monoidal-cat 𝕏) where
  open ecat 𝕏 public
  open iso-d&p 𝕏 public
  open is-monoidal-cat 𝕏mon public renaming (ass to ⊗ass; lun to ⊗lun; run to ⊗run)
