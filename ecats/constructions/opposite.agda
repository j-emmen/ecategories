
{-# OPTIONS --without-K #-}

module ecats.constructions.opposite where

open import tt-basics.setoids using (setoid)
--open import tt-basics.id-type
open import ecats.basic-defs.ecat-def&not
open import ecats.basic-defs.initial
open import ecats.finite-limits.defs.terminal
open import ecats.functors.defs.efunctor
open import ecats.functors.defs.id-on-objs
open import ecats.functors.defs.natural-iso


is-ecat-op : {ℓₒ ℓₐ ℓ~ : Level}{Obj : Set ℓₒ}{Hom : Obj → Obj → setoid {ℓₐ} {ℓ~}}
         → is-ecategory Obj Hom → is-ecategory Obj (λ x y → Hom y x)
is-ecat-op isecat = record
  { _∘_ = λ g f → f ∘ g
  ; idar = idar
  ; ∘ext = λ f f' g g' pff pfg → ∘ext g g' f f' pfg pff
  ; lidax = ridax
  ; ridax = lidax
  ; assoc = λ f g h → assˢ
  }
  where open is-ecategory isecat
        open ecategory-aux-level isecat using (assˢ)

infix 90 _ᵒᵖ
_ᵒᵖ : {ℓ₁ₒ ℓ₁ₕ ℓ₁~ : Level}
           → ecategoryₗₑᵥ ℓ₁ₒ ℓ₁ₕ ℓ₁~ → ecategoryₗₑᵥ ℓ₁ₒ ℓ₁ₕ ℓ₁~
ℂ ᵒᵖ = record
     { Obj = Obj
     ; Hom = λ X Y → Hom Y X
     ; isecat = is-ecat-op isecat
     }
     where open ecat ℂ

op-small : small-ecategory → small-ecategory
op-small ℂ = record
  { Obj = Obj
  ; Hom = λ x y → Hom y x
  ; isecat = is-ecat-op isecat
  }
  where open small-ecategory ℂ using (Obj; Hom; isecat)

op-locsmall : ecategory → ecategory
op-locsmall ℂ = record
  { Obj = Obj
  ; Hom = λ x y → Hom y x
  ; isecat = is-ecat-op isecat
  }
  where open ecategory ℂ using (Obj; Hom; isecat)


-- functor between opposite categories
infix 100 _ᵒ
_ᵒ : {ℓ₁ₒ ℓ₁ₕ ℓ₁~ : Level}{ℂ : ecategoryₗₑᵥ ℓ₁ₒ ℓ₁ₕ ℓ₁~}
     {ℓ₂ₒ ℓ₂ₕ ℓ₂~ : Level}{𝔻 : ecategoryₗₑᵥ ℓ₂ₒ ℓ₂ₕ ℓ₂~}
          → efunctorₗₑᵥ ℂ 𝔻 → efunctorₗₑᵥ (ℂ ᵒᵖ) (𝔻 ᵒᵖ)
F ᵒ = record
  { FObj = F.ₒ
  ; FHom = λ {A} {B} → F.ₐ {B} {A}
  ; isF = record
        { ext = F.ext
        ; id = F.id
        ; cmp = λ f g → F.cmp g f
        }
  }
  where module F = efctr F


-- The two functors in 'opop' have the same action of the identity functor IdF

opop : {ℓ₁ₒ ℓ₁ₕ ℓ₁~ : Level}(ℂ : ecategoryₗₑᵥ ℓ₁ₒ ℓ₁ₕ ℓ₁~)
            → ecat.isecat ((ℂ ᵒᵖ) ᵒᵖ) ≅ᶜᵃᵗ ecat.isecat ℂ
opop ℂ = record
  { a12 = a12
  ; a21 = a21
  ; isisopair = record
              { iddom = λ _ → ℂ.r
              ; idcod = λ _ → ℂ.r
              }
  }
  where module ℂ = ecategory-aux ℂ
        module ℂᵒᵒ = ecat ((ℂ ᵒᵖ) ᵒᵖ)
        module Id = idobj-efunctor (IdFᵢₒ {isecat = ℂ.isecat})
        a12 : idobj-efunctor ℂᵒᵒ.isecat ℂ.isecat
        a12 = record
            { ₐ = λ f → f
            ; isfctr = record
                  { ext = Id.ext
                  ; id = Id.id
                  ; cmp = Id.cmp
                  }
            }
        a21 : idobj-efunctor ℂ.isecat ℂᵒᵒ.isecat
        a21 = record
            { ₐ = λ f → f
            ; isfctr = record
                  { ext = Id.ext
                  ; id = Id.id
                  ; cmp = Id.cmp
                  }
            }



{-
opop : {ℓ₁ₒ ℓ₁ₕ ℓ₁~ : Level}(ℂ : ecategoryₗₑᵥ ℓ₁ₒ ℓ₁ₕ ℓ₁~)
            → efunctor ((ℂ ᵒᵖ) ᵒᵖ) ℂ
opop ℂ = record
  { FObj = λ X → X
  ; FHom = λ f → f
  ; isF = record
        { ext = λ pf → pf
        ; id = r
        ; cmp = λ f g → r
        }
  }
  where open ecategory-aux ℂ

popo : {ℓ₁ₒ ℓ₁ₕ ℓ₁~ : Level}(ℂ : ecategoryₗₑᵥ ℓ₁ₒ ℓ₁ₕ ℓ₁~)
            → efunctor ℂ ((ℂ ᵒᵖ) ᵒᵖ)
popo ℂ = record
  { FObj = λ X → X
  ; FHom = λ f → f
  ; isF = record
        { ext = λ pf → pf
        ; id = r
        ; cmp = λ f g → r
        }
  }
  where open ecategory-aux ℂ

opiso : {ℓ₁ₒ ℓ₁ₕ ℓ₁~ : Level}(ℂ : ecategoryₗₑᵥ ℓ₁ₒ ℓ₁ₕ ℓ₁~)
             → opop ℂ ○ popo ℂ ≅ₐ IdF {ℂ = ℂ}
opiso ℂ = record
  { natt = record
         { fnc = λ {A} → ℂ.idar A
         ; nat = λ f → ℂ.lidgen ℂ.ridˢ
         }
  ; natt⁻¹ = record
         { fnc = λ {A} → ℂ.idar A
         ; nat = λ f → ℂ.lidgen ℂ.ridˢ
         }
  ; isiso = λ {A} → record
          { iddom = ℂ.rid
          ; idcod = ℂ.rid
          }
  }
  where module ℂ = ecategory-aux ℂ


opisoₒ : {ℓ₁ₒ ℓ₁ₕ ℓ₁~ : Level}(ℂ : ecategoryₗₑᵥ ℓ₁ₒ ℓ₁ₕ ℓ₁~)
             → popo ℂ ○ opop ℂ ≅ₐ IdF {ℂ = (ℂ ᵒᵖ) ᵒᵖ}
opisoₒ ℂ = record
  { natt = record
         { fnc = λ {A} → ℂ.idar A
         ; nat = λ f → ℂ.lidgen ℂ.ridˢ
         }
  ; natt⁻¹ = record
         { fnc = λ {A} → ℂ.idar A
         ; nat = λ f → ℂ.lidgen ℂ.ridˢ
         }
  ; isiso = λ {A} → record
          { iddom = ℂ.rid
          ; idcod = ℂ.rid
          }
  }
  where module ℂ = ecategory-aux ℂ
-}


module opposite-props {ℓ₁ₒ ℓ₁ₕ ℓ₁~ : Level}(ℂ : ecategoryₗₑᵥ ℓ₁ₒ ℓ₁ₕ ℓ₁~) where
  private
    module ℂ where
      open ecategory-aux ℂ public
      open initial-defs ℂ public
      open terminal-defs ℂ public
    module ℂᵒ where
      open ecategory-aux (ℂ ᵒᵖ) public
      open initial-defs (ℂ ᵒᵖ) public
      open terminal-defs (ℂ ᵒᵖ) public

  init→termᵒ : {X : ℂ.Obj} → ℂ.is-initial X → ℂᵒ.is-terminal X
  init→termᵒ {X} isinit = record
    { ! = X.ø
    ; !uniq = X.øuq
    }
    where module X = ℂ.is-initial isinit

  term→initᵒ : {X : ℂ.Obj} → ℂ.is-terminal X → ℂᵒ.is-initial X
  term→initᵒ {X} isterm = record
    { ø = X.!
    ; øuq = X.!uniq
    }
    where module X = ℂ.is-terminal isterm

  initᵒ→term : {X : ℂ.Obj} → ℂᵒ.is-initial X → ℂ.is-terminal X
  initᵒ→term {X} isinitᵒ = record
    { ! = X.ø
    ; !uniq = X.øuq
    }
    where module X = ℂᵒ.is-initial isinitᵒ

  termᵒ→init : {X : ℂ.Obj} → ℂᵒ.is-terminal X → ℂ.is-initial X
  termᵒ→init {X} istermᵒ = record
    { ø = X.!
    ; øuq = X.!uniq
    }
    where module X = ℂᵒ.is-terminal istermᵒ
    

-- end opposite-props
