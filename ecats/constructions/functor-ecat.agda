
{-# OPTIONS --without-K #-}

module ecats.constructions.functor-ecat where

open import Agda.Primitive
open import tt-basics.id-type using (=J)
open import ecats.basic-defs.ecat-def&not
open import ecats.functors.defs.efunctor-d&n
open import ecats.functors.defs.natural-transformation
open import ecats.constructions.discrete-ecat

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

const-diagr-on : {𝕁 : small-ecategory}{ℂ : ecategory} → ecat.Obj ℂ → diagram 𝕁 ℂ
const-diagr-on {ℂ = ℂ} X = record
  { FObj = λ i → X
  ; FHom = λ ij → ℂ.idar X
  ; isF = record
        { ext = λ _ → ℂ.r
        ; id = λ {_} → ℂ.r
        ; cmp = λ _ _ → ℂ.lid
        }
  }
  where module ℂ = ecategory-aux ℂ

const-Diagr : (𝕁 : small-ecategory)(ℂ : ecategory) → efunctor ℂ (Diagr 𝕁 ℂ)
const-Diagr 𝕁 ℂ = record
  { FObj = const-diagr-on
  ; FHom = λ f → record
         { fnc = λ {_} → f
         ; nat = λ _ → ℂ.ridgen ℂ.lidˢ
         }
  ; isF = record
        { ext = λ pf _ → pf
        ; id = λ _ → ℂ.r
        ; cmp = λ _ _ _ → ℂ.r
        }
  }
  where module ℂ = ecategory-aux ℂ

-- discrete diagrams

discDiagr : (I : Set)(ℂ : ecategory) → ecategory
discDiagr I ℂ = record
  { Obj = I → ℂ.Obj
  ; Hom = λ D D' → NatTr {ℂ = small-disc-ecat I} {𝔻 = ℂ} (disc-ecat-lift D) (disc-ecat-lift D')
  ; isecat = record
           { _∘_ = natt-vcmp {ℂ = small-disc-ecat I} {𝔻 = ℂ}
           ; idar = λ D → natt-id {ℂ = small-disc-ecat I} {𝔻 = ℂ} {disc-ecat-lift D}
           ; ∘ext = λ _ _ _ _ pff pfg X → ℂ.∘ext _ _ _ _ (pff X) (pfg X)
           ; lidax = λ f X → ℂ.lidax (fnc f {X})
           ; ridax = λ f X → ℂ.ridax (fnc f {X})
           ; assoc = λ f g h X → ℂ.assoc (fnc f {X}) (fnc g) (fnc h)
           }
  }
  where module ℂ = ecategory ℂ
        open natural-transformation


const-discDiagr : (I : Set)(ℂ : ecategory) → efunctor ℂ (discDiagr I ℂ)
const-discDiagr I ℂ = record
  { FObj = λ X _ → X
  ; FHom = λ {A} {B} f → record
         { fnc = λ {_} → f
         ; nat = λ {i} → =J (λ j ij → f ℂ.∘ dl.ₐ A ij ℂ.~ dl.ₐ B ij ℂ.∘ f) (ℂ.ridgen ℂ.lidˢ)
         }
  ; isF = record
        { ext = λ pf _ → pf
        ; id = λ _ → ℂ.r
        ; cmp = λ _ _ _ → ℂ.r
        }
  }
  where module ℂ = ecategory-aux ℂ
        module dl (A : ℂ.Obj) = efunctor-aux {ℂ = small-disc-ecat I} {ℂ}
                                             (disc-ecat-lift (λ _ → A))



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
