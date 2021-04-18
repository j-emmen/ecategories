
{-# OPTIONS --without-K #-}

module ecats.functors.defs.natural-transformation where

open import Agda.Primitive
open import tt-basics.setoids using (setoid) --hiding (||_||; _⇒_)
open import ecats.basic-defs.ecat-def&not
open import ecats.isomorphism
open import ecats.functors.defs.efunctor-d&n

---------------------------
-- Natural transformations
---------------------------


module natural-trans-defs {ℓ₁ ℓ₂ : Level}{ObjD : Set ℓ₁}{HomD : ObjD → ObjD → setoid {ℓ₂}}
                          {isecatD : is-ecategory ObjD HomD}
                          {ℓ₃ ℓ₄ : Level}{ObjC : Set ℓ₃}{HomC : ObjC → ObjC → setoid {ℓ₄}}
                          {isecatC : is-ecategory ObjC HomC}
                          {Fobj Gobj : ObjD → ObjC}{Fhom : {x y : ObjD} → || HomD x y || → || HomC (Fobj x) (Fobj y) ||}
                          {Ghom : {x y : ObjD} → || HomD x y || → || HomC (Gobj x) (Gobj y) ||}
                          (isfctrF : efunctor-defs.is-functorial isecatD isecatC Fhom)
                          (isfctrG : efunctor-defs.is-functorial isecatD isecatC Ghom)
                          where
  private
    module Dom = is-ecategory isecatD
    module Cod = is-ecategory isecatC
    module F where
      open efunctor-defs isecatD isecatC
      open is-functorial isfctrF public
      ₒ : ObjD → ObjC
      ₒ = Fobj
      ₐ : {A B : ObjD} → || HomD A B || → || HomC (Fobj A) (Fobj B) ||
      ₐ = Fhom
    module G where
      open efunctor-defs isecatD isecatC
      open is-functorial isfctrG public
      ₒ : ObjD → ObjC
      ₒ = Gobj
      ₐ : {A B : ObjD} → || HomD A B || → || HomC (Gobj A) (Gobj B) ||
      ₐ = Ghom

  is-natural : (fnc : {A : ObjD} → || HomC (F.ₒ A) (G.ₒ A) ||) → Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₄)
  is-natural fnc = {A B : ObjD}(f : || HomD A B ||) → fnc Cod.∘ (F.ₐ f) Cod.~ (G.ₐ f) Cod.∘ fnc


record natural-transformation {ℂ 𝔻 : ecategory} (F G : efunctor ℂ 𝔻) : Set₁ where
  private
    module ℂ = ecategory ℂ
    module 𝔻 = ecategory 𝔻
    module F = efunctor F
    module G = efunctor G
  field
    fnc : {A : ℂ.Obj} → || 𝔻.Hom (F.ₒ A) (G.ₒ A) ||
    nat : {A B : ℂ.Obj} → (f : || ℂ.Hom A B ||)
             → fnc 𝔻.∘ (F.ₐ f) 𝔻.~ (G.ₐ f) 𝔻.∘ fnc

infixr 8 _⇒_
_⇒_ :  {ℂ 𝔻 : ecategory} (F G : efunctor ℂ 𝔻) → Set₁
F ⇒ G = natural-transformation F G


Nat : {ℂ 𝔻 : ecategory} (F G : efunctor ℂ 𝔻) → setoid
Nat {ℂ} {𝔻} F G = record
  { object = natural-transformation F G
  ; _∼_ = λ μ ν → ∀ X → fnc μ {X}  𝔻.~ fnc ν {X}
  ; istteqrel = record
              { refl = λ μ X → 𝔻.r
              ; sym = λ pf X → (pf X) 𝔻.ˢ
              ; tra = λ pf pf' X → pf X 𝔻.⊙ pf' X
              }
  }
  where module 𝔻 = ecategory-aux 𝔻
        open natural-transformation


natt-id : {ℂ 𝔻 : ecategory} {F : efunctor ℂ 𝔻} → F ⇒ F
natt-id {ℂ} {𝔻} {F} = record
                { fnc = λ {A} → 𝔻.idar (F.ₒ A)
                ; nat = λ f → lidgen ridˢ
                }
                where module 𝔻 = ecategory 𝔻
                      module F = efunctor F
                      open ecategory-aux-only 𝔻

natt-vcmp : {ℂ 𝔻 : ecategory} {F G H : efunctor ℂ 𝔻}
               → G ⇒ H → F ⇒ G → F ⇒ H
natt-vcmp {ℂ} {𝔻} {F} {G} {H} β α = record
  { fnc = λ {A} → β.fnc 𝔻.∘ α.fnc
  ; nat = λ f → assˢ ⊙ ∘e (α.nat f) r ⊙ ass ⊙ ∘e r (β.nat f) ⊙ assˢ
  }
  where module 𝔻 = ecategory 𝔻
        module α = natural-transformation α
        module β = natural-transformation β
        open ecategory-aux-only 𝔻


natt-hcmp : {ℂ 𝔻 𝔼 : ecategory} {F G : efunctor ℂ 𝔻} {H K : efunctor 𝔻 𝔼}
               → H ⇒ K → F ⇒ G → H ○ F ⇒ K ○ G
natt-hcmp {𝔼 = 𝔼} {F} {G} {H} {K} β α = record
  { fnc = λ {A} → β.fnc {G.ₒ A} 𝔼.∘ H.ₐ (α.fnc {A})
  ; nat = λ f → ~proof
        (β.fnc 𝔼.∘ H.ₐ α.fnc) 𝔼.∘ H.ₐ (F.ₐ f)   ~[ assˢ ⊙ ∘e (H.∘∘ (α.nat f)) r ] /
        β.fnc 𝔼.∘ H.ₐ (G.ₐ f) 𝔼.∘ H.ₐ α.fnc     ~[ ass ⊙ ∘e r (β.nat (G.ₐ f)) ⊙ assˢ ]∎
        K.ₐ (G.ₐ f) 𝔼.∘ β.fnc 𝔼.∘ H.ₐ α.fnc ∎
  }
  where module 𝔼 = ecategory 𝔼
        module F = efunctor F
        module G = efunctor G
        module H = efunctor-aux H
        module K = efunctor K
        module α = natural-transformation α
        module β = natural-transformation β
        open ecategory-aux-only 𝔼

