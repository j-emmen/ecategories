
{-# OPTIONS --without-K #-}

module ecats.constructions.discrete-ecat where

open import Agda.Primitive
open import tt-basics.all-basics hiding (||_||)
open import ecats.basic-defs.ecat-def&not
open import ecats.functors.defs.efunctor-d&n

discrete-ecat' : {ℓ : Level} → Set ℓ → ecategoryₗₑᵥ ℓ ℓ 0ₗₑᵥ
-- ℓ₁ ≤ ℓ₂ ; 0ₗₑᵥ ≤ ℓ₃
discrete-ecat' A = record
  { Obj = A
  ; Hom = λ x y → codisc-std (x == y)
  ; isecat = record
           { _∘_ = λ q p → =tra p q
           ; idar = λ _ → =rf
           ; ∘ext = λ f f' g g' _ _ → 0₁
           ; lidax = λ f → 0₁
           ; ridax = λ f → 0₁
           ; assoc = λ f g h → 0₁
           }
  }

discrete-ecat : {ℓ : Level} → Set ℓ → ecategoryₗₑᵥ ℓ ℓ ℓ
-- ℓ₁ ≤ ℓ₂ ; 0ₗₑᵥ ≤ ℓ₃
discrete-ecat A = record
  { Obj = A
  ; Hom = λ x y → disc-std (x == y)
  ; isecat = record
           { _∘_ = λ q p → p ■ q
           ; idar = λ _ → =rf
           ; ∘ext = λ p p' q q' → ■ext p q'
           ; lidax = ■idr
           ; ridax = ■idl
           ; assoc = ■ass⁻¹
           }
  }

small-disc-ecat : Set 0ₗₑᵥ → small-ecategory
small-disc-ecat = discrete-ecat {0ₗₑᵥ}

-- there is no discrete locally small category

disc-ecat-lift : {A : Set}{ℓ₁ ℓ₂ ℓ₃ : Level}{ℂ : ecategoryₗₑᵥ ℓ₁ ℓ₂ ℓ₃}(F : A → ecat.Obj ℂ)
                    → efunctorₗₑᵥ (small-disc-ecat A) ℂ
disc-ecat-lift {A} {ℂ = ℂ} F = record
  { FObj = F
  ; FHom = FH 
  ; isF = record
        { ext = λ {_} {_} {p} {_} → =J (λ q _ → FH p ℂ.~ FH q) ℂ.r
        ; id = λ {x} → ℂ.r
        ; cmp = FHcmp
        }
  }
  where module ℂ = ecategory-aux ℂ
        FH : {x y : A} → x == y → || ℂ.Hom (F x) (F y) ||
        FH {x} {_} = =J (λ u _ → || ℂ.Hom (F x) (F u) ||) (ℂ.idar (F x))
        FHcmp : {x y z : A}(p : x == y)(q : y == z)
                   → FH q ℂ.∘ FH p ℂ.~ FH (p ■ q)
        FHcmp p q = =J (λ _ v → ∀ u → FH v ℂ.∘ FH u ℂ.~ FH (u ■ v)) (λ _ → ℂ.lid) q p



codiscrete-ecat : {ℓ : Level} → Set ℓ → ecategoryₗₑᵥ ℓ 0ₗₑᵥ 0ₗₑᵥ
-- ℓ₁ ≤ ℓ₂ ; 0ₗₑᵥ ≤ ℓ₃
codiscrete-ecat A = record
  { Obj = A
  ; Hom = λ x y → disc-std N₁
  ; isecat = record
           { _∘_ = λ g f → f
           ; idar = λ a → 0₁
           ; ∘ext = λ f f' g g' f~f' _ → f~f'
           ; lidax = λ f → =rf
           ; ridax = λ f → =sym (contr= N₁-isContr f)
           ; assoc = λ f g h → =rf
           }
  }


small-codisc-ecat : Set 0ₗₑᵥ → small-ecategory
small-codisc-ecat = codiscrete-ecat {0ₗₑᵥ}

codisc-ecat : Set 1ₗₑᵥ → ecategory
codisc-ecat = codiscrete-ecat {1ₗₑᵥ}
