
{-# OPTIONS --without-K --show-implicit #-}

module ecats.constructions.functor-ecat where

open import Agda.Primitive
open import ecats.basic-defs.ecat-def&not
open import ecats.functors.defs.efunctor-d&n
open import ecats.functors.defs.natural-transformation


{-
Fctrₗₑᵥ : {ℓ₁ ℓ₂ : Level}(ℂ : ecategoryₗₑᵥ ℓ₁ ℓ₂)
         {ℓ₃ ℓ₄ : Level}(𝔻 : ecategoryₗₑᵥ ℓ₃ ℓ₄) → ecategoryₗₑᵥ (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄) (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₄)
Fctrₗₑᵥ ℂ 𝔻 = record
  { Obj = efunctorₗₑᵥ ℂ 𝔻
  ; Hom = {!Nat {ℂ = ℂ} {𝔻 = 𝔻}!} -- Nat {ℂ = ℂ} {𝔻 = 𝔻}
  ; isecat = {!!} {-record
           { _∘_ = natt-vcmp {ℂ = ℂ} {𝔻 = 𝔻}
           ; idar = λ F → natt-id {ℂ = ℂ} {𝔻 = 𝔻} {F}
           ; ∘ext = λ _ _ _ _ pff pfg X → 𝔻.∘ext _ _ _ _ (pff X) (pfg X)
           ; lidax = λ f X → 𝔻.lidax (fnc f {X})
           ; ridax = λ f X → 𝔻.ridax (fnc f {X})
           ; assoc = λ f g h X → 𝔻.assoc (fnc f {X}) (fnc g) (fnc h)
           }-}
  }
  where module 𝔻 = ecat 𝔻
        open natural-transformation
-}

-- Locally small category of diagrams 

Diagr : (𝕁 : small-ecategory)(ℂ : ecategory) → ecategory
Diagr 𝕁 ℂ = record
  { Obj = diagram 𝕁 ℂ
  ; Hom = NatTr {ℂ = 𝕁} {𝔻 = ℂ}
  ; isecat = record
           { _∘_ = natt-vcmp {ℂ = 𝕁} {𝔻 = ℂ}
           ; idar = λ F → natt-id {ℂ = 𝕁} {𝔻 = ℂ} {F}
           ; ∘ext = λ _ _ _ _ pff pfg X → ℂ.∘ext _ _ _ _ (pff X) (pfg X)
           ; lidax = λ f X → ℂ.lidax (fnc f {X})
           ; ridax = λ f X → ℂ.ridax (fnc f {X})
           ; assoc = λ f g h X → ℂ.assoc (fnc f {X}) (fnc g) (fnc h)
           }
  }
  where module ℂ = ecategory ℂ
        open natural-transformation


-- Large category of functors

Fctr : (ℂ 𝔻 : ecategory) → large-ecategory
Fctr ℂ 𝔻 = record
  { Obj = efunctor ℂ 𝔻
  ; Hom = NatTr {ℂ = ℂ} {𝔻 = 𝔻}
  ; isecat = record
           { _∘_ = natt-vcmp {ℂ = ℂ} {𝔻 = 𝔻}
           ; idar = λ F → natt-id {ℂ = ℂ} {𝔻 = 𝔻} {F}
           ; ∘ext = λ _ _ _ _ pff pfg X → 𝔻.∘ext _ _ _ _ (pff X) (pfg X)
           ; lidax = λ f X → 𝔻.lidax (fnc f {X})
           ; ridax = λ f X → 𝔻.ridax (fnc f {X})
           ; assoc = λ f g h X → 𝔻.assoc (fnc f {X}) (fnc g) (fnc h)
           }
  }
  where module 𝔻 = ecategory 𝔻
        open natural-transformation

