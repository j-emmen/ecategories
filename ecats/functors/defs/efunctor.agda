
{-# OPTIONS --without-K #-}

module ecats.functors.defs.efunctor where

open import Agda.Primitive
open import tt-basics.setoids using (setoid)
open import ecats.basic-defs.ecat-def&not


-- E-functors

module efunctor-defs {ℓ₁ ℓ₂ : Level}(ℂ : ecategoryₗₑᵥ ℓ₁ ℓ₂)
                     {ℓ₃ ℓ₄ : Level}(𝔻 : ecategoryₗₑᵥ ℓ₃ ℓ₄)
                     where
  private
    module ℂ = ecat ℂ
    module 𝔻 = ecat 𝔻

-- Note that the universe level of is-functorial does not depend on ℓ₃
  record is-functorial {FO : ℂ.Obj → 𝔻.Obj}
                       (FH : {A B : ℂ.Obj} → || ℂ.Hom A B || → || 𝔻.Hom (FO A) (FO B) ||)
                       : Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₄)
                       where
    field
      ext : {A B : ℂ.Obj} {f f' : || ℂ.Hom A B ||}
              → f ℂ.~ f' → FH f 𝔻.~ FH f'
      id : {A : ℂ.Obj}
              → FH (ℂ.idar A) 𝔻.~ 𝔻.idar (FO A)
      cmp : {A B C : ℂ.Obj} (f : || ℂ.Hom A B ||) (g : || ℂ.Hom B C ||)
               → FH g 𝔻.∘ FH f 𝔻.~ FH (g ℂ.∘ f)
-- end efunctor-defs
  

record efunctorₗₑᵥ {ℓ₁ ℓ₂ ℓ₃ ℓ₄} (ℂ : ecategoryₗₑᵥ ℓ₁ ℓ₂)(𝔻 : ecategoryₗₑᵥ ℓ₃ ℓ₄)
                  : Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄)
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
          where open ecategory-aux-only 𝔻

module efctr {ℓ₁ ℓ₂ ℓ₃ ℓ₄}{ℂ : ecategoryₗₑᵥ ℓ₁ ℓ₂}{𝔻 : ecategoryₗₑᵥ ℓ₃ ℓ₄}
             = efunctorₗₑᵥ {ℓ₁} {ℓ₂} {ℓ₃} {ℓ₄} {ℂ} {𝔻}

efunctor : (ℂ 𝔻 : ecategory) → Set₁
efunctor ℂ 𝔻 = efunctorₗₑᵥ ℂ 𝔻

diagram _shaped-diagram-in_ : (ℂ : small-ecategory)(𝔻 : ecategory) → Set₁
diagram ℂ 𝔻 = efunctorₗₑᵥ ℂ 𝔻
ℂ shaped-diagram-in 𝔻 = diagram ℂ 𝔻



IdFₗₑᵥ : {ℓₒ ℓₕ : Level}{ℂ : ecategoryₗₑᵥ ℓₒ ℓₕ} → efunctorₗₑᵥ ℂ ℂ
IdFₗₑᵥ {_} {_} {ℂ} = record
  { FObj = λ A → A
  ; FHom = λ f → f
  ; isF = record
        { ext = λ pf → pf
        ; id = r
        ; cmp = λ f g → r
        }
  }
  where open ecategory-aux ℂ


efunctor-cmpₗₑᵥ : {ℓₒ ℓₕ : Level}{ℂ 𝔻 𝔼 : ecategoryₗₑᵥ ℓₒ ℓₕ}
                      → efunctorₗₑᵥ 𝔻 𝔼 → efunctorₗₑᵥ ℂ 𝔻 → efunctorₗₑᵥ ℂ 𝔼
efunctor-cmpₗₑᵥ {_} {_} {ℂ} {𝔻} {𝔼} G F = record
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
_○_ : {ℓₒ ℓₕ : Level}{ℂ 𝔻 𝔼 : ecategoryₗₑᵥ ℓₒ ℓₕ}
          → efunctorₗₑᵥ 𝔻 𝔼 → efunctorₗₑᵥ ℂ 𝔻 → efunctorₗₑᵥ ℂ 𝔼
G ○ F = efunctor-cmpₗₑᵥ G F
