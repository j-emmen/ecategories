 
-- disable the K axiom:

{-# OPTIONS --without-K #-}

module ecats.functors.defs.basic-defs where

open import Agda.Primitive
open import ecats.basic-defs.ecat-def&not
open import ecats.basic-defs.isomorphism
open import ecats.functors.defs.efunctor-d&n
open import ecats.functors.defs.natural-transformation
open import ecats.functors.defs.natural-iso



-- Adjunctions

record adjunction {ℓ₁ ℓ₂}{ℂ : ecategoryₗₑᵥ ℓ₁ ℓ₂}{ℓ₃ ℓ₄}{𝔻 : ecategoryₗₑᵥ ℓ₃ ℓ₄}
                  (L : efunctorₗₑᵥ ℂ 𝔻) (R : efunctorₗₑᵥ 𝔻 ℂ) : Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄)
                  where
  private
    module ℂ = ecat ℂ
    module 𝔻 = ecat 𝔻
    module L = efunctorₗₑᵥ L
    module R = efunctorₗₑᵥ R
  field
    η : natural-transformation IdF (R ○ L)
    ε : natural-transformation (L ○ R) IdF
  open natural-transformation ε renaming (fnc to ε-f; nat to ε-n)
  open natural-transformation η renaming (fnc to η-f; nat to η-n)
  field
    trid₁ : {X : ℂ.Obj} → ε-f 𝔻.∘ (L.ₐ η-f) 𝔻.~ 𝔻.idar (L.ₒ X)
    trid₂ : {A : 𝔻.Obj} → η-f ℂ.∘ (R.ₐ ε-f) ℂ.~ ℂ.idar (R.ₒ (L.ₒ (R.ₒ A)))

infix 3 _⊣_

_⊣_ : {ℓ₁ ℓ₂ : Level}{ℂ : ecategoryₗₑᵥ ℓ₁ ℓ₂}{ℓ₃ ℓ₄ : Level}{𝔻 : ecategoryₗₑᵥ ℓ₃ ℓ₄}
      (L : efunctorₗₑᵥ ℂ 𝔻)(R : efunctorₗₑᵥ 𝔻 ℂ) → Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄)
L ⊣ R = adjunction L R


-- Equivalences

record is-equivalence-pair {ℓ₁ ℓ₂}{ℂ : ecategoryₗₑᵥ ℓ₁ ℓ₂}
                           {ℓ₃ ℓ₄}{𝔻 : ecategoryₗₑᵥ ℓ₃ ℓ₄}
                           (F : efunctorₗₑᵥ ℂ 𝔻) (G : efunctorₗₑᵥ 𝔻 ℂ) : Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄)
                           where
  field
    ι1 : natural-iso (F ○ G) IdF
    ι2 : natural-iso (G ○ F) IdF


record is-equivalence {ℓ₁ ℓ₂}{ℂ : ecategoryₗₑᵥ ℓ₁ ℓ₂}
                      {ℓ₃ ℓ₄}{𝔻 : ecategoryₗₑᵥ ℓ₃ ℓ₄}
                      (F : efunctorₗₑᵥ ℂ 𝔻) : Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄)
                      where
  field
    invF : efunctorₗₑᵥ 𝔻 ℂ
    iseqv : is-equivalence-pair F invF
  open is-equivalence-pair iseqv public



-- Other properties of funtors

record is-full {ℓ₁ ℓ₂}{ℂ : ecategoryₗₑᵥ ℓ₁ ℓ₂}
               {ℓ₃ ℓ₄}{𝔻 : ecategoryₗₑᵥ ℓ₃ ℓ₄}
               (F : efunctorₗₑᵥ ℂ 𝔻) : Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₄)
               where
  private
    module ℂ = ecat ℂ
    module 𝔻 = ecat 𝔻
    module F = efunctorₗₑᵥ F
  field
    full-ar : {X Y : ℂ.Obj} → || 𝔻.Hom (F.ₒ X) (F.ₒ Y) || → || ℂ.Hom X Y ||
    full-pf : {X Y : ℂ.Obj} {g : || 𝔻.Hom (F.ₒ X) (F.ₒ Y) ||}
                    → F.ₐ (full-ar g) 𝔻.~ g
  full-pfˢ : {X Y : ℂ.Obj} {g : || 𝔻.Hom (F.ₒ X) (F.ₒ Y) ||}
                    → g 𝔻.~ F.ₐ (full-ar g)
  full-pfˢ =  full-pf ˢ
           where open ecategory-aux-only 𝔻
  full-pfg : {X Y : ℂ.Obj} {g g' : || 𝔻.Hom (F.ₒ X) (F.ₒ Y) ||}
                    → g 𝔻.~ g' → F.ₐ (full-ar g) 𝔻.~ g'
  full-pfg pf = full-pf ⊙ pf
              where open ecategory-aux-only 𝔻
  full-pfgˢ : {X Y : ℂ.Obj} {g g' : || 𝔻.Hom (F.ₒ X) (F.ₒ Y) ||}
                    → g 𝔻.~ g' → g' 𝔻.~ F.ₐ (full-ar g)
  full-pfgˢ pf = full-pfg pf ˢ
              where open ecategory-aux-only 𝔻


record is-faithful {ℓ₁ ℓ₂}{ℂ : ecategoryₗₑᵥ ℓ₁ ℓ₂}
                   {ℓ₃ ℓ₄}{𝔻 : ecategoryₗₑᵥ ℓ₃ ℓ₄}
                   (F : efunctorₗₑᵥ ℂ 𝔻) : Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₄)
                   where
  private
    module ℂ = ecat ℂ
    module 𝔻 = ecat 𝔻
    module F = efctr F
  field
    faith-pf : {X Y : ℂ.Obj} {f g : || ℂ.Hom X Y ||}
                  → F.ₐ f 𝔻.~ F.ₐ g → f ℂ.~ g


record is-ess-surjective-ob {ℓ₁ ℓ₂}{ℂ : ecategoryₗₑᵥ ℓ₁ ℓ₂}
                            {ℓ₃ ℓ₄}{𝔻 : ecategoryₗₑᵥ ℓ₃ ℓ₄}
                            (F : efunctorₗₑᵥ ℂ 𝔻) : Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄)
                            where
  private
    module ℂ = ecat ℂ
    module 𝔻 = ecat 𝔻
    module F = efunctorₗₑᵥ F
  open iso-defs 𝔻
  field
    ob : 𝔻.Obj → ℂ.Obj
    ar : (Y : 𝔻.Obj) → || 𝔻.Hom (F.ₒ (ob Y)) Y ||
    iso : (Y : 𝔻.Obj) → is-iso (ar Y)



-- Essential equivalences

record is-ess-equivalence {ℓ₁ ℓ₂}{ℂ : ecategoryₗₑᵥ ℓ₁ ℓ₂}
                          {ℓ₃ ℓ₄}{𝔻 : ecategoryₗₑᵥ ℓ₃ ℓ₄}
                          (F : efunctorₗₑᵥ ℂ 𝔻) : Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄)
                          where
  private
    module ℂ = ecat ℂ
    module 𝔻 = ecat 𝔻
    module F = efunctorₗₑᵥ F
  field
    isfull : is-full F
    isfaithful : is-faithful F
    isesurjobj : is-ess-surjective-ob F
