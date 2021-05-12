
{-# OPTIONS --without-K #-}

module ecats.functors.defs.efunctor where

open import Agda.Primitive
open import ecats.basic-defs.ecat-def&not


-- E-functors

module efunctor-defs {ℓ₁ₒ ℓ₁ₕ ℓ₁~ : Level}(ℂ : ecategoryₗₑᵥ ℓ₁ₒ ℓ₁ₕ ℓ₁~)
                     {ℓ₂ₒ ℓ₂ₕ ℓ₂~ : Level}(𝔻 : ecategoryₗₑᵥ ℓ₂ₒ ℓ₂ₕ ℓ₂~)
                     where
  private
    module ℂ = ecat ℂ
    module 𝔻 = ecat 𝔻

-- Note that the universe level of is-functorial does not depend on ℓ₂ₒ
  record is-functorial {FO : ℂ.Obj → 𝔻.Obj}
                       (FH : {A B : ℂ.Obj} → || ℂ.Hom A B || → || 𝔻.Hom (FO A) (FO B) ||)
                       : Set (ℂ.ℓₐₗₗ ⊔ 𝔻.ℓ~)
                       where
    field
      ext : {A B : ℂ.Obj} {f f' : || ℂ.Hom A B ||}
              → f ℂ.~ f' → FH f 𝔻.~ FH f'
      id : {A : ℂ.Obj}
              → FH (ℂ.idar A) 𝔻.~ 𝔻.idar (FO A)
      cmp : {A B C : ℂ.Obj} (f : || ℂ.Hom A B ||) (g : || ℂ.Hom B C ||)
               → FH g 𝔻.∘ FH f 𝔻.~ FH (g ℂ.∘ f)
-- end efunctor-defs
  

record efunctorₗₑᵥ {ℓ₁ₒ ℓ₁ₕ ℓ₁~ ℓ₂ₒ ℓ₂ₕ ℓ₂~}(ℂ : ecategoryₗₑᵥ ℓ₁ₒ ℓ₁ₕ ℓ₁~)(𝔻 : ecategoryₗₑᵥ ℓ₂ₒ ℓ₂ₕ ℓ₂~)
                  : Set (ecat.ℓₐₗₗ ℂ ⊔ ecat.ℓₐₗₗ 𝔻)
                  where
  private
    module ℂ = ecat ℂ
    module 𝔻 = ecat 𝔻
  open efunctor-defs ℂ 𝔻
  field
    FObj : ℂ.Obj → 𝔻.Obj
    FHom : {A B : ℂ.Obj} → || ℂ.Hom A B ||
              → || 𝔻.Hom (FObj A) (FObj B) ||
    isF : is-functorial FHom
  open is-functorial isF public
  ₒ : ℂ.Obj → 𝔻.Obj
  ₒ = FObj
  ₐ : {A B : ℂ.Obj} → || ℂ.Hom A B || → || 𝔻.Hom (FObj A) (FObj B) ||
  ₐ = FHom
  idˢ : {A : ℂ.Obj} → 𝔻.idar (FObj A) 𝔻.~ FHom (ℂ.idar A)
  idˢ {A} = id {A} ˢ
          where open ecategory-aux-only 𝔻 using (_ˢ)
  cmpˢ : {A B C : ℂ.Obj}(f : || ℂ.Hom A B ||)(g : || ℂ.Hom B C ||)
            → ₐ (g ℂ.∘ f) 𝔻.~ ₐ g 𝔻.∘ ₐ f
  cmpˢ f g = cmp f g ˢ
           where open ecategory-aux-only 𝔻 using (_ˢ)

module efctr {ℓ₁ₒ ℓ₁ₕ ℓ₁~ ℓ₂ₒ ℓ₂ₕ ℓ₂~}{ℂ : ecategoryₗₑᵥ ℓ₁ₒ ℓ₁ₕ ℓ₁~}{𝔻 : ecategoryₗₑᵥ ℓ₂ₒ ℓ₂ₕ ℓ₂~}
             = efunctorₗₑᵥ {ℓ₁ₒ} {ℓ₁ₕ} {ℓ₁~} {ℓ₂ₒ} {ℓ₂ₕ} {ℓ₂~} {ℂ} {𝔻}

efunctor : {ℓₒ ℓₕ ℓ~ : Level}(ℂ 𝔻 : ecategoryₗₑᵥ ℓₒ ℓₕ ℓ~) → Set (ℓₒ ⊔ ℓₕ ⊔ ℓ~)
efunctor ℂ 𝔻 = efunctorₗₑᵥ ℂ 𝔻
module efunctor {ℓₒ ℓₕ ℓ~}{ℂ 𝔻 : ecategoryₗₑᵥ ℓₒ ℓₕ ℓ~}(F : efunctor ℂ 𝔻) = efunctorₗₑᵥ F


diagram _shaped-diagram-in_ : (ℂ : small-ecategory)(𝔻 : ecategory) → Set₁
diagram ℂ 𝔻 = efunctorₗₑᵥ ℂ 𝔻
ℂ shaped-diagram-in 𝔻 = diagram ℂ 𝔻
module diagram {ℂ : small-ecategory}{𝔻 : ecategory}(F : diagram ℂ 𝔻)
               = efunctorₗₑᵥ F


IdF : {ℓₒ ℓₕ ℓ~ : Level}{ℂ : ecategoryₗₑᵥ ℓₒ ℓₕ ℓ~} → efunctorₗₑᵥ ℂ ℂ
IdF {ℂ = ℂ} = record
  { FObj = λ A → A
  ; FHom = λ f → f
  ; isF = record
        { ext = λ pf → pf
        ; id = r
        ; cmp = λ f g → r
        }
  }
  where open ecategory-aux ℂ


efunctor-cmpₗₑᵥ : {ℓ₁ₒ ℓ₁ₕ ℓ₁~ : Level}{ℂ : ecategoryₗₑᵥ ℓ₁ₒ ℓ₁ₕ ℓ₁~}
                 {ℓ₂ₒ ℓ₂ₕ ℓ₂~ : Level}{𝔻 : ecategoryₗₑᵥ ℓ₂ₒ ℓ₂ₕ ℓ₂~}
                 {ℓ₃ₒ ℓ₃ₕ ℓ₃~ : Level}{𝔼 : ecategoryₗₑᵥ ℓ₃ₒ ℓ₃ₕ ℓ₃~}
                      → efunctorₗₑᵥ 𝔻 𝔼 → efunctorₗₑᵥ ℂ 𝔻 → efunctorₗₑᵥ ℂ 𝔼
efunctor-cmpₗₑᵥ {𝔼 = 𝔼} G F = record
  { FObj = λ A → G.ₒ (F.ₒ A)
  ; FHom = λ {A} {B} f → G.ₐ {F.ₒ A} {F.ₒ B} (F.ₐ {A} {B} f)
  ; isF = record
        { ext = λ pf → G.ext (F.ext pf)
        ; id =  (G.ext F.id) 𝔼.⊙ G.id
        ; cmp = λ f g → G.cmp _ _ 𝔼.⊙ (G.ext (F.cmp f g))
        }
  }
  where module 𝔼 = ecategory-aux 𝔼
        module F = efctr F
        module G = efctr G

infixr 10 _○_
_○_ : {ℓ₁ₒ ℓ₁ₕ ℓ₁~ : Level}{ℂ : ecategoryₗₑᵥ ℓ₁ₒ ℓ₁ₕ ℓ₁~}
       {ℓ₂ₒ ℓ₂ₕ ℓ₂~ : Level}{𝔻 : ecategoryₗₑᵥ ℓ₂ₒ ℓ₂ₕ ℓ₂~}
       {ℓ₃ₒ ℓ₃ₕ ℓ₃~ : Level}{𝔼 : ecategoryₗₑᵥ ℓ₃ₒ ℓ₃ₕ ℓ₃~}
          → efunctorₗₑᵥ 𝔻 𝔼 → efunctorₗₑᵥ ℂ 𝔻 → efunctorₗₑᵥ ℂ 𝔼
G ○ F = efunctor-cmpₗₑᵥ G F
