
{-# OPTIONS --without-K #-}

module ecats.functors.defs.natural-transformation where

open import tt-basics.setoids using (setoid) --hiding (||_||; _⇒_)
open import ecats.basic-defs.ecat-def&not
open import ecats.functors.defs.efunctor-d&n

---------------------------
-- Natural transformations
---------------------------


module natural-trans-defs {ℓ₁ ℓ₂ ℓ₃ : Level}{D : ecategoryₗₑᵥ ℓ₁ ℓ₂ ℓ₃}
                          {ℓ₄ ℓ₅ ℓ₆ : Level}{C : ecategoryₗₑᵥ ℓ₄ ℓ₅ ℓ₆}
                          (F G : efunctorₗₑᵥ D C)
                          where
  private
    module Dom = ecat D
    module Cod = ecat C
    module F = efunctorₗₑᵥ F
    module G = efunctorₗₑᵥ G
    
  is-natural : (fnc : {A : Dom.Obj} → || Cod.Hom (F.ₒ A) (G.ₒ A) ||) → Set (Dom.ℓₙₒ~ ⊔ Cod.ℓ~)
  is-natural fnc = {A B : Dom.Obj}(f : || Dom.Hom A B ||)
                          → fnc Cod.∘ (F.ₐ f) Cod.~ (G.ₐ f) Cod.∘ fnc
-- end natural-trans-defs

record natural-transformation {ℓ₁ ℓ₂ ℓ₃}{ℂ : ecategoryₗₑᵥ ℓ₁ ℓ₂ ℓ₃}{ℓ₄ ℓ₅ ℓ₆}{𝔻 : ecategoryₗₑᵥ ℓ₄ ℓ₅ ℓ₆}
                              (F G : efunctorₗₑᵥ ℂ 𝔻) : Set (ecat.ℓₙₒ~ ℂ ⊔ ecat.ℓₕₒₘ 𝔻)
                              where
  private
    module ℂ = ecat ℂ
    module 𝔻 = ecat 𝔻
    module F = efctr F
    module G = efctr G
  open natural-trans-defs F G
  field
    fnc : {A : ℂ.Obj} → || 𝔻.Hom (F.ₒ A) (G.ₒ A) ||
    nat : is-natural fnc
  natˢ : {A B : ℂ.Obj}(f : || ℂ.Hom A B ||)
             → G.ₐ f 𝔻.∘ fnc 𝔻.~ fnc 𝔻.∘ F.ₐ f
  natˢ f = nat f ˢ
         where open ecategory-aux-only 𝔻 using (_ˢ)

infixr 60 _⇒_
_⇒_ : {ℓ₁ ℓ₂ ℓ₃ : Level}{ℂ : ecategoryₗₑᵥ ℓ₁ ℓ₂ ℓ₃}{ℓ₄ ℓ₅ ℓ₆ : Level}{𝔻 : ecategoryₗₑᵥ ℓ₄ ℓ₅ ℓ₆}
        (F G : efunctorₗₑᵥ ℂ 𝔻)
           → Set (ecat.ℓₙₒ~ ℂ ⊔ ecat.ℓₕₒₘ 𝔻)
F ⇒ G = natural-transformation F G


NatTr : {ℓ₁ ℓ₂ ℓ₃ : Level}{ℂ : ecategoryₗₑᵥ ℓ₁ ℓ₂ ℓ₃}{ℓ₄ ℓ₅ ℓ₆ : Level}{𝔻 : ecategoryₗₑᵥ ℓ₄ ℓ₅ ℓ₆}
        (F G : efunctorₗₑᵥ ℂ 𝔻)
           → setoid {ecat.ℓₙₒ~ ℂ ⊔ ecat.ℓₕₒₘ 𝔻} {ecat.ℓₒ ℂ ⊔ ecat.ℓ~ 𝔻}
NatTr {ℂ = ℂ} {𝔻 = 𝔻} F G = record
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

module NT {ℓ₁ ℓ₂ ℓ₃ : Level}{ℂ : ecategoryₗₑᵥ ℓ₁ ℓ₂ ℓ₃}{ℓ₄ ℓ₅ ℓ₆ : Level}{𝔻 : ecategoryₗₑᵥ ℓ₄ ℓ₅ ℓ₆}
          {F G : efunctorₗₑᵥ ℂ 𝔻}
          where
  open setoid (NatTr F G) public
  infix 20 _~_
  _~_ : (α β : object) → Set (ℓ₁ ⊔ ℓ₆)
  α ~ β = α ∼ β
-- end NT

natt-id : {ℓ₁ ℓ₂ ℓ₃ : Level}{ℂ : ecategoryₗₑᵥ ℓ₁ ℓ₂ ℓ₃}{ℓ₄ ℓ₅ ℓ₆ : Level}{𝔻 : ecategoryₗₑᵥ ℓ₄ ℓ₅ ℓ₆}
          {F : efunctorₗₑᵥ ℂ 𝔻}
            → F ⇒ F
natt-id {ℂ = ℂ} {𝔻 = 𝔻} {F} = record
                { fnc = λ {A} → 𝔻.idar (F.ₒ A)
                ; nat = λ f → lidgen ridˢ
                }
                where module 𝔻 = ecat 𝔻
                      module F = efctr F
                      open ecategory-aux-only 𝔻

natt-vcmp : {ℓ₁ ℓ₂ ℓ₃ : Level}{ℂ : ecategoryₗₑᵥ ℓ₁ ℓ₂ ℓ₃}{ℓ₄ ℓ₅ ℓ₆ : Level}{𝔻 : ecategoryₗₑᵥ ℓ₄ ℓ₅ ℓ₆}
            {F G H : efunctorₗₑᵥ ℂ 𝔻}
               → G ⇒ H → F ⇒ G → F ⇒ H
natt-vcmp {ℂ = ℂ} {𝔻 = 𝔻} {F} {G} {H} β α = record
  { fnc = λ {A} → β.fnc 𝔻.∘ α.fnc
  ; nat = λ f → assˢ ⊙ ∘e (α.nat f) r ⊙ ass ⊙ ∘e r (β.nat f) ⊙ assˢ
  }
  where module 𝔻 = ecat 𝔻
        module α = natural-transformation α
        module β = natural-transformation β
        open ecategory-aux-only 𝔻


natt-hcmp : {ℓ₁ ℓ₂ ℓ₃ : Level}{ℂ : ecategoryₗₑᵥ ℓ₁ ℓ₂ ℓ₃}{ℓ₄ ℓ₅ ℓ₆ : Level}{𝔻 : ecategoryₗₑᵥ ℓ₄ ℓ₅ ℓ₆}
            {ℓ₇ ℓ₈ ℓ₉ : Level}{𝔼 : ecategoryₗₑᵥ ℓ₇ ℓ₈ ℓ₉}{F G : efunctorₗₑᵥ ℂ 𝔻}{H K : efunctorₗₑᵥ 𝔻 𝔼}
               → H ⇒ K → F ⇒ G → H ○ F ⇒ K ○ G
natt-hcmp {𝔼 = 𝔼} {F} {G} {H} {K} β α = record
  { fnc = λ {A} → β.fnc {G.ₒ A} 𝔼.∘ H.ₐ (α.fnc {A})
  ; nat = λ f → ~proof
        (β.fnc 𝔼.∘ H.ₐ α.fnc) 𝔼.∘ H.ₐ (F.ₐ f)   ~[ assˢ ⊙ ∘e (H.∘∘ (α.nat f)) r ] /
        β.fnc 𝔼.∘ H.ₐ (G.ₐ f) 𝔼.∘ H.ₐ α.fnc     ~[ ass ⊙ ∘e r (β.nat (G.ₐ f)) ⊙ assˢ ]∎
        K.ₐ (G.ₐ f) 𝔼.∘ β.fnc 𝔼.∘ H.ₐ α.fnc ∎
  }
  where module 𝔼 = ecat 𝔼
        module F = efctr F
        module G = efctr G
        module H = efunctor-aux H
        module K = efctr K
        module α = natural-transformation α
        module β = natural-transformation β
        open ecategory-aux-only 𝔼

