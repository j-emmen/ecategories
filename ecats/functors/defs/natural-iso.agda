
{-# OPTIONS --without-K #-}

module ecats.functors.defs.natural-iso where

open import Agda.Primitive
open import tt-basics.setoids using (setoid) --hiding (||_||; _⇒_)
open import ecats.basic-defs.ecat-def&not
open import ecats.isomorphism
open import ecats.functors.defs.efunctor-d&n
open import ecats.functors.defs.natural-transformation


------------------------
-- Natural isomorphisms
------------------------

record natural-iso {ℓ₁ ℓ₂ ℓ₃}{ℂ : ecategoryₗₑᵥ ℓ₁ ℓ₂ ℓ₃}{ℓ₄ ℓ₅ ℓ₆}{𝔻 : ecategoryₗₑᵥ ℓ₄ ℓ₅ ℓ₆}
                   (F G : efunctorₗₑᵥ ℂ 𝔻) : Set (ecat.ℓₙₒ~ ℂ ⊔ ecat.ℓₕₒₘ 𝔻)
                   where
  private
    module ℂ = ecat ℂ
    module F = efunctorₗₑᵥ F
    module G = efunctorₗₑᵥ G
  field
    natt : natural-transformation F G
    natt⁻¹ : natural-transformation G F
  open natural-transformation natt public
  open natural-transformation natt⁻¹ renaming (fnc to fnc⁻¹; nat to nat⁻¹) public
  open iso-defs 𝔻
  field
    isiso : {A : ℂ.Obj} → is-iso-pair (fnc {A}) (fnc⁻¹ {A})
  module isop {A : ℂ.Obj} = is-iso-pair (isiso {A})
  open isop public


infixr 9 _≅ₐ_
_≅ₐ_ :  {ℓ₁ ℓ₂ ℓ₃ : Level}{ℂ : ecategoryₗₑᵥ ℓ₁ ℓ₂ ℓ₃}{ℓ₄ ℓ₅ ℓ₆ : Level}{𝔻 : ecategoryₗₑᵥ ℓ₄ ℓ₅ ℓ₆}
        (F G : efunctorₗₑᵥ ℂ 𝔻) → Set (ecat.ℓₙₒ~ ℂ ⊔ ecat.ℓₕₒₘ 𝔻)
F ≅ₐ G = natural-iso F G

≅ₐrefl : {ℓ₁ ℓ₂ ℓ₃ : Level}{ℂ : ecategoryₗₑᵥ ℓ₁ ℓ₂ ℓ₃}{ℓ₄ ℓ₅ ℓ₆ : Level}{𝔻 : ecategoryₗₑᵥ ℓ₄ ℓ₅ ℓ₆}
         {F : efunctorₗₑᵥ ℂ 𝔻} → F ≅ₐ F
≅ₐrefl {𝔻 = 𝔻} {F} = record
  { natt = natt-id
  ; natt⁻¹ = natt-id
  ; isiso = λ {A} → record
          { iddom = lid
          ; idcod = lid
          }
  }
  where open ecategory-aux-only 𝔻

≅ₐsym : {ℓ₁ ℓ₂ ℓ₃ : Level}{ℂ : ecategoryₗₑᵥ ℓ₁ ℓ₂ ℓ₃}{ℓ₄ ℓ₅ ℓ₆ : Level}{𝔻 : ecategoryₗₑᵥ ℓ₄ ℓ₅ ℓ₆}
       {F G : efunctorₗₑᵥ ℂ 𝔻} → F ≅ₐ G → G ≅ₐ F
≅ₐsym α = record
  { natt = natt⁻¹
  ; natt⁻¹ = natt
  ; isiso = λ {A} → record
          { iddom = idcod
          ; idcod = iddom
          }
  }
  where open natural-iso α

natiso-vcmp : {ℓ₁ ℓ₂ ℓ₃ : Level}{ℂ : ecategoryₗₑᵥ ℓ₁ ℓ₂ ℓ₃}{ℓ₄ ℓ₅ ℓ₆ : Level}{𝔻 : ecategoryₗₑᵥ ℓ₄ ℓ₅ ℓ₆}
              {F G H : efunctorₗₑᵥ ℂ 𝔻}
                  → G ≅ₐ H → F ≅ₐ G → F ≅ₐ H
natiso-vcmp {𝔻 = 𝔻} {F} {G} {H} β α = record
  { natt = natt-vcmp β.natt α.natt
  ; natt⁻¹ = natt-vcmp α.natt⁻¹ β.natt⁻¹
  ; isiso = λ {A} → record
          { iddom = ass ⊙ ∘e r (assˢ ⊙ ridgg r β.iddom) ⊙ α.iddom
          ; idcod = ass ⊙ ∘e r (assˢ ⊙ ridgg r α.idcod) ⊙ β.idcod
          }
  }
  where open ecategory-aux-only 𝔻
        module α = natural-iso α
        module β = natural-iso β


natiso-hcmp : {ℓ₁ ℓ₂ ℓ₃ : Level}{ℂ : ecategoryₗₑᵥ ℓ₁ ℓ₂ ℓ₃}{ℓ₄ ℓ₅ ℓ₆ : Level}{𝔻 : ecategoryₗₑᵥ ℓ₄ ℓ₅ ℓ₆}
              {ℓ₇ ℓ₈ ℓ₉ : Level}{𝔼 : ecategoryₗₑᵥ ℓ₇ ℓ₈ ℓ₉}{F G : efunctorₗₑᵥ ℂ 𝔻}
              {H K : efunctorₗₑᵥ 𝔻 𝔼}
                  → H ≅ₐ K → F ≅ₐ G → H ○ F ≅ₐ K ○ G
natiso-hcmp {𝔼 = 𝔼} {F} {G} {H} {K} β α = record
  { natt = natt-hcmp β.natt α.natt
  ; natt⁻¹ = natt-hcmp β.natt⁻¹ α.natt⁻¹
  ; isiso = λ {A} → record
          { iddom = ∘e r (β.nat⁻¹ α.fnc⁻¹) ⊙ assˢ ⊙ ∘e (ass ⊙ lidgg r β.iddom) r ⊙ H.∘ax α.iddom ⊙ H.id
          ; idcod = ∘e r (β.nat α.fnc) ⊙ assˢ ⊙ ∘e (ass ⊙ lidgg r β.idcod) r ⊙ K.∘ax α.idcod ⊙ K.id
          }
  }
  where open ecategory-aux-only 𝔼
        module H = efunctor-aux H
        module K = efunctor-aux K
        module α = natural-iso α
        module β = natural-iso β
