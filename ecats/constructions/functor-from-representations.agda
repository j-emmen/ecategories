{-# OPTIONS --without-K #-}

module ecats.constructions.functor-from-representations where

open import ecats.basic-defs.ecat-def&not
open import ecats.functors.defs.efunctor-d&n
open import ecats.functors.defs.basic-defs
open import ecats.functors.defs.natural-transformation
open import ecats.functors.defs.natural-iso
open import ecats.functors.defs.presheaf
open import ecats.functors.defs.representable
open import ecats.constructions.functor-ecat
open import ecats.constructions.yoneda
open import ecats.concr-ecats.Std-lev


module functor-defined-by-representations {ℓₒ₁ ℓₐ₁ ℓ~₁}{ℂ : ecategoryₗₑᵥ ℓₒ₁ ℓₐ₁ ℓ~₁}
                                          {ℓₒ₂ ℓₐ₂ ℓ~₂}{𝔻 : ecategoryₗₑᵥ ℓₒ₂ ℓₐ₂ ℓ~₂}
                                          {P : efunctorₗₑᵥ ℂ (PShₗₑᵥ 𝔻)}
                                          (Prepr : (X : ecat.Obj ℂ) → is-represble-psheaf (efctr.ₒ P X))
                                          where
  private
    module ℂ = ecat ℂ
    module 𝔻 = ecat 𝔻
    module P where
      open efunctor-aux P public
      module ₒ (X : ℂ.Obj) where
        --open presheafₗₑᵥ (ₒ X) public
        open is-represble-psheaf (Prepr X) public
        module iso = natiso
      module ₐ {X Y : ℂ.Obj}(f : || ℂ.Hom X Y ||) = psheaf-morₗₑᵥ (ₐ f)
  open yoneda-props 𝔻
  module Yo where
    open is-full Yo-full public
    open is-faithful Yo-faith public
    module full = Yo-full-props

  module Far {X Y : ℂ.Obj}(f : || ℂ.Hom X Y ||) where
    open Lemma (𝔻 [─, P.ₒ.Rob Y ₒ]) (P.ₒ.Rob X) public
    nt : 𝔻 [─, P.ₒ.Rob X ₒ] ⇒ 𝔻 [─, P.ₒ.Rob Y ₒ]
    nt = P.ₒ.iso.natt Y ○ᵥ P.ₐ f ○ᵥ P.ₒ.iso.natt⁻¹ X
    lft : || 𝔻.Hom (P.ₒ.Rob X) (P.ₒ.Rob Y) ||
    lft = Yo.full-ar nt
  -- end Far
      
  F : efunctorₗₑᵥ ℂ 𝔻
  F = record
    { FObj = P.ₒ.Rob
    ; FHom = Far.lft
    ; isF = record
          { ext = λ {X} {Y} {f} {f'} eq → Yo.full.ext {μ = Far.nt f} {Far.nt f'} ( λ A a →
                                P.ₒ.iso.fnc.ext Y A (P.ext eq A (P.ₒ.iso.fnc⁻¹.ap X A a)) )
          ; id = λ {X} → Yo.full.id {P.ₒ.Rob X} {Far.nt (ℂ.idar X)} λ A a → ~proof
               P.ₒ.iso.fnc.ap X A (P.ₐ.ap (ℂ.idar X) (P.ₒ.iso.fnc⁻¹.ap X A a))
                                 ~[ P.ₒ.iso.fnc.ext X A (P.id {X} A (P.ₒ.iso.fnc⁻¹.ap X A a)) ] /
               P.ₒ.iso.fnc.ap X A (P.ₒ.iso.fnc⁻¹.ap X A a)
                                                                        ~[ P.ₒ.iso.idcod X {A} a ]∎
               a ∎
          ; cmp = λ {X} {Y} {Z} f g → Yo.full.cmp {μ = Far.nt f} {Far.nt g} {Far.nt (g ℂ.∘ f)}
                                                  (λ A a → ~proof
                P.ₒ.iso.fnc.ap Z A (P.ₐ.ap g (P.ₒ.iso.fnc⁻¹.ap Y A (
                                      P.ₒ.iso.fnc.ap Y A (P.ₐ.ap f (P.ₒ.iso.fnc⁻¹.ap X A a))
                                      )))
            ~[ P.ₒ.iso.fnc.ext Z A (P.ₐ.ext g (P.ₒ.iso.iddom Y (P.ₐ.ap f (P.ₒ.iso.fnc⁻¹.ap X A a)))) ] /
                P.ₒ.iso.fnc.ap Z A (P.ₐ.ap g (P.ₐ.ap f (P.ₒ.iso.fnc⁻¹.ap X A a)))
            ~[ P.ₒ.iso.fnc.ext Z A (P.∘ax-rf A (P.ₒ.iso.fnc⁻¹.ap X A a)) ]∎
                P.ₒ.iso.fnc.ap Z A (P.ₐ.ap (g ℂ.∘ f) (P.ₒ.iso.fnc⁻¹.ap X A a)) ∎)
          }
    }
    where open ecategory-aux-only 𝔻
-- end functor-defined-by-representations


fctr-from-repr : {ℓₒ₁ ℓₐ₁ ℓ~₁ : Level}{ℂ : ecategoryₗₑᵥ ℓₒ₁ ℓₐ₁ ℓ~₁}
                 {ℓₒ₂ ℓₐ₂ ℓ~₂ : Level}{𝔻 : ecategoryₗₑᵥ ℓₒ₂ ℓₐ₂ ℓ~₂}{P : efunctorₗₑᵥ ℂ (PShₗₑᵥ 𝔻)}
                 (Prepr : (X : ecat.Obj ℂ) → is-represble-psheaf (efctr.ₒ P X))
                   → efunctorₗₑᵥ ℂ 𝔻
fctr-from-repr {P = P} repr = F
                            where open functor-defined-by-representations {P = P} repr
