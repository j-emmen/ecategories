
{-# OPTIONS --without-K #-}

module ecats.functors.defs.id-on-objs-full-factorisation where

open import tt-basics.setoids using (setoid)
open import ecats.basic-defs.ecat-def&not
open import ecats.basic-defs.isomorphism
open import ecats.basic-props.isomorphism
open import ecats.functors.defs.efunctor-d&n
open import ecats.functors.defs.basic-defs
open import ecats.functors.defs.natural-transformation
open import ecats.functors.defs.natural-iso
open import ecats.functors.defs.id-on-objs

module id-on-objs-full-fact {ℓ₁ₒ ℓ₁ₕ ℓ₁~ : Level}{ℂ : ecategoryₗₑᵥ ℓ₁ₒ ℓ₁ₕ ℓ₁~}
                            {ℓ₂ₒ ℓ₂ₕ ℓ₂~ : Level}{𝔻 : ecategoryₗₑᵥ ℓ₂ₒ ℓ₂ₕ ℓ₂~}
                            (F : efunctorₗₑᵥ ℂ 𝔻)
                            where
  private    
    module catnot {ℓ₁ ℓ₂ ℓ₃}(ℂ : ecategoryₗₑᵥ ℓ₁ ℓ₂ ℓ₃) where
      open ecat ℂ public
      open iso-defs ℂ public
      open iso-props ℂ public
    module ℂ = catnot ℂ
    module 𝔻 = catnot 𝔻
    module F = efctr F

  I : ecategoryₗₑᵥ ℂ.ℓₒ 𝔻.ℓₐᵣᵣ 𝔻.ℓ~
  I = record
    { Obj = ℂ.Obj
    ; Hom = λ X Y → 𝔻.Hom (F.ₒ X) (F.ₒ Y)
    ; isecat = record
             { _∘_ = λ {X} {Y} {Z} → 𝔻._∘_ {F.ₒ X} {F.ₒ Y} {F.ₒ Z}
             ; idar = λ X → 𝔻.idar (F.ₒ X)
             ; ∘ext = λ {X} {Y} {Z} → 𝔻.∘ext {F.ₒ X} {F.ₒ Y} {F.ₒ Z}
             ; lidax = λ {X} {Y} → 𝔻.lidax {F.ₒ X} {F.ₒ Y}
             ; ridax = λ {X} {Y} → 𝔻.ridax {F.ₒ X} {F.ₒ Y}
             ; assoc = λ {X} {Y} {Z} {W} → 𝔻.assoc {F.ₒ X} {F.ₒ Y} {F.ₒ Z} {F.ₒ W}
             }

    }
  private module I = ecat I
  
  fl : efunctorₗₑᵥ I 𝔻
  fl = record
     { FObj = F.ₒ
     ; FHom = λ {X} {Y} → Id𝔻.ₐ {F.ₒ X} {F.ₒ Y}
     ; isF = record
           { ext = Id𝔻.ext
           ; id = Id𝔻.id
           ; cmp = Id𝔻.cmp
           }
     }
     where module Id𝔻 = efctr (IdF {ℂ = 𝔻})

  flisfull : is-full fl
  flisfull = record
    { ar = λ f → f
    ; pf = r
    }
    where open ecategory-aux-only 𝔻 using (r)

  ioₐ : idobj-efunctor ℂ.isecat I.isecat
  ioₐ = record
      { ₐ = F.ₐ
      ; isfctr = record
               { ext = F.ext
               ; id = F.id
               ; cmp = F.cmp
               }
      }

  io : efunctorₗₑᵥ ℂ I
  io = idobj-efunctor-is-efunctor ioₐ

  tr : fl ○ io ≅ₐ F
  tr = record
     { natt = record
            { fnc = λ {X} → 𝔻.idar (F.ₒ X)
            ; nat = natt-id.nat
            }
     ; natt⁻¹ = record
              { fnc = λ {X} → 𝔻.idar (F.ₒ X)
              ; nat = natt-id.nat
              }
     ; isiso = λ {X} → 𝔻.idar-is-isopair (F.ₒ X)
     }
     where module natt-id = natural-transformation (natt-id {F = F})
  
-- end id-on-objs-full-fact
       
