{-# OPTIONS --without-K --show-implicit #-}

module ecats.constructions.comma-ecat where

open import Agda.Primitive
open import tt-basics.basics using (prod; pair)
open import tt-basics.setoids hiding (||_||)
open import ecats.basic-defs.ecat-def&not
open import ecats.functors.defs.efunctor-d&n
open import ecats.functors.defs.natural-transformation


-- need ℓ₄ = 0ₗₑᵥ in ℂ : ecategoryₗₑᵥ ℓ₃ ℓ₄ since otherwise ↓Hom A B : setoid {ℓ₂ ⊔ ℓ₄ ⊔ ℓ₆} {ℓ₂ ⊔ ℓ₆}
-- while hom-setoids are currently of the form setoid {ℓ} {ℓ}

module comma-ecat-defs {ℓ₁ ℓ₂ ℓ₃ ℓ₅ ℓ₆ : Level}
                       {𝕃 : ecategoryₗₑᵥ ℓ₁ ℓ₂}{ℂ : ecategoryₗₑᵥ ℓ₃ 0ₗₑᵥ}{ℝ : ecategoryₗₑᵥ ℓ₅ ℓ₆}
                       (F : efunctorₗₑᵥ 𝕃 ℂ)(G : efunctorₗₑᵥ ℝ ℂ)
                       where
  private
    module 𝕃 = ecategory-aux 𝕃
    module ℂ = ecategory-aux ℂ
    module ℝ = ecategory-aux ℝ
    module F = efunctor-aux F
    module G = efunctor-aux G

  record ↓Obj : Set (ℓ₁ ⊔ ℓ₅) where -- ⊔ ℓ₄
    field
      L : 𝕃.Obj
      R : ℝ.Obj
      ar : || ℂ.Hom (F.ₒ L) (G.ₒ R) ||

  record ||↓Hom|| (A B : ↓Obj) : Set (ℓ₂ ⊔ ℓ₆) where -- ⊔ ℓ₄
    private
      module A = ↓Obj A
      module B = ↓Obj B
    field
      arL : || 𝕃.Hom A.L B.L ||
      arR : || ℝ.Hom A.R B.R ||
      sq : B.ar ℂ.∘ F.ₐ arL ℂ.~ G.ₐ arR ℂ.∘ A.ar

  frgt-sq : {A B : ↓Obj} → ||↓Hom|| A B
               → prod || 𝕃.Hom (↓Obj.L A) (↓Obj.L B) || || ℝ.Hom (↓Obj.R A) (↓Obj.R B) ||
  frgt-sq f = pair f.arL f.arR
            where module f = ||↓Hom|| f
      
  ↓Hom : ↓Obj → ↓Obj → setoid {ℓ₂ ⊔ ℓ₆} {ℓ₂ ⊔ ℓ₆} -- ⊔ ℓ₄
  ↓Hom A B = sub-setoid (prod-std (𝕃.Hom A.L B.L) (ℝ.Hom A.R B.R))
                        (frgt-sq {A} {B})
    where module A = ↓Obj A
          module B = ↓Obj B  
-- end comma-ecat-defs

comma-ecat : {ℓ₁ ℓ₂ ℓ₃ ℓ₅ ℓ₆ : Level}
             {𝕃 : ecategoryₗₑᵥ ℓ₁ ℓ₂}{ℂ : ecategoryₗₑᵥ ℓ₃ 0ₗₑᵥ}{ℝ : ecategoryₗₑᵥ ℓ₅ ℓ₆}
             (F : efunctorₗₑᵥ 𝕃 ℂ)(G : efunctorₗₑᵥ ℝ ℂ)
             → ecategoryₗₑᵥ (ℓ₁ ⊔ ℓ₅) (ℓ₂ ⊔ ℓ₆)
comma-ecat {𝕃 = 𝕃} {ℂ} {ℝ} F G = record
  { Obj = ↓Obj
  ; Hom = ↓Hom
  ; isecat = record
           { _∘_ = {!!}
           ; idar = {!!}
           ; ∘ext = {!!}
           ; lidax = {!!}
           ; ridax = {!!}
           ; assoc = {!!}
           }
  }
  where open comma-ecat-defs F G

