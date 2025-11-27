
{-# OPTIONS --without-K #-}

module ecats.constructions.functor-ecat where

open import tt-basics.setoids using (stdsections)
open import ecats.basic-defs.ecat-def&not
open import ecats.functors.defs.efunctor-d&n
open import ecats.functors.defs.natural-transformation
open import ecats.constructions.discrete-ecat



fctr-and-natt-is-ecat : {ℓ₁ₒ ℓ₁ₕ ℓ₁~ : Level}(ℂ : ecategoryₗₑᵥ ℓ₁ₒ ℓ₁ₕ ℓ₁~)
                        {ℓ₂ₒ ℓ₂ₕ ℓ₂~ : Level}(𝔻 : ecategoryₗₑᵥ ℓ₂ₒ ℓ₂ₕ ℓ₂~)
                          → is-ecategory (efunctorₗₑᵥ ℂ 𝔻) (NatTr {ℂ = ℂ} {𝔻 = 𝔻})
fctr-and-natt-is-ecat ℂ 𝔻 = record
  { _∘_ = natt-vcmp {ℂ = ℂ} {𝔻 = 𝔻}
  ; idar = λ F → natt-id {ℂ = ℂ} {𝔻 = 𝔻} {F}
  ; ∘ext = λ _ _ _ _ pff pfg X → 𝔻.∘ext _ _ _ _ (pff X) (pfg X)
  ; lidax = λ f X → 𝔻.lidax (fnc f {X})
  ; ridax = λ f X → 𝔻.ridax (fnc f {X})
  ; assoc = λ f g h X → 𝔻.assoc (fnc f {X}) (fnc g) (fnc h)
  }
  where module ℂ = ecat ℂ
        module 𝔻 = ecat 𝔻
        open natural-transformation

private module fctr {ℓ₁ₒ ℓ₁ₕ ℓ₁~ : Level}(ℂ : ecategoryₗₑᵥ ℓ₁ₒ ℓ₁ₕ ℓ₁~)
                    {ℓ₂ₒ ℓ₂ₕ ℓ₂~ : Level}(𝔻 : ecategoryₗₑᵥ ℓ₂ₒ ℓ₂ₕ ℓ₂~)
                    = is-ecategory (fctr-and-natt-is-ecat ℂ 𝔻)


-------------------------------------------------
-- Category of efunctors between two ecategories
-------------------------------------------------

[_,_]ᶜᵃᵗ Fctrₗₑᵥ : {ℓ₁ₒ ℓ₁ₕ ℓ₁~ : Level}(ℂ : ecategoryₗₑᵥ ℓ₁ₒ ℓ₁ₕ ℓ₁~)
                {ℓ₂ₒ ℓ₂ₕ ℓ₂~ : Level}(𝔻 : ecategoryₗₑᵥ ℓ₂ₒ ℓ₂ₕ ℓ₂~)
                   → ecategoryₗₑᵥ (fctr.ℓₒ ℂ 𝔻) (fctr.ℓₐᵣᵣ ℂ 𝔻) (fctr.ℓ~ ℂ 𝔻)
Fctrₗₑᵥ ℂ 𝔻 = record
  { Obj = efunctorₗₑᵥ ℂ 𝔻
  ; Hom = NatTr {ℂ = ℂ} {𝔻 = 𝔻}
  ; isecat = fctr-and-natt-is-ecat ℂ 𝔻
  }
[_,_]ᶜᵃᵗ = Fctrₗₑᵥ

-- precomposition functor
precmp-Fctr : {ℓ₁ₒ ℓ₁ₕ ℓ₁~ : Level} {ℂ : ecategoryₗₑᵥ ℓ₁ₒ ℓ₁ₕ ℓ₁~}
              {ℓ₂ₒ ℓ₂ₕ ℓ₂~ : Level} {𝔻 : ecategoryₗₑᵥ ℓ₂ₒ ℓ₂ₕ ℓ₂~}
              {ℓ₃ₒ ℓ₃ₐ ℓ₃~ : Level} {𝔼 : ecategoryₗₑᵥ ℓ₃ₒ ℓ₃ₐ ℓ₃~}
               → efunctorₗₑᵥ ℂ 𝔻 → efunctorₗₑᵥ [ 𝔻 , 𝔼 ]ᶜᵃᵗ [ ℂ , 𝔼 ]ᶜᵃᵗ
precmp-Fctr {𝔼 = 𝔼} F = record
  { FObj = λ H → H ○ F
  ; FHom = natt-fctr-pre F
  ; isF = record
        { ext = λ eq X → eq (F.ₒ X)
        ; id = λ _ → r
        ; cmp = λ _ _ _ → r
        }
  }
  where module F = efctr F
        open ecategory-aux 𝔼 using (r; ass; assˢ)

precmp-Fctr-natt : {ℓ₁ₒ ℓ₁ₕ ℓ₁~ : Level} {ℂ : ecategoryₗₑᵥ ℓ₁ₒ ℓ₁ₕ ℓ₁~}
                    {ℓ₂ₒ ℓ₂ₕ ℓ₂~ : Level} {𝔻 : ecategoryₗₑᵥ ℓ₂ₒ ℓ₂ₕ ℓ₂~}
                    {ℓ₃ₒ ℓ₃ₐ ℓ₃~ : Level} {𝔼 : ecategoryₗₑᵥ ℓ₃ₒ ℓ₃ₐ ℓ₃~}
                    {F G : efunctorₗₑᵥ ℂ 𝔻}
                      → F ⇒ G → precmp-Fctr {𝔼 = 𝔼} F ⇒ precmp-Fctr G
precmp-Fctr-natt {𝔼 = 𝔼} {F} {G} α = record
  { fnc = λ {H} → natt-fctr-post H α
  ; nat = λ γ X → nt.natˢ γ (nt.fnc α {X})
  }
  where module nt = natural-transformation

-- postcomposition functor
postcmp-Fctr : {ℓ₁ₒ ℓ₁ₕ ℓ₁~ : Level} {ℂ : ecategoryₗₑᵥ ℓ₁ₒ ℓ₁ₕ ℓ₁~}
               {ℓ₂ₒ ℓ₂ₕ ℓ₂~ : Level} {𝔻 : ecategoryₗₑᵥ ℓ₂ₒ ℓ₂ₕ ℓ₂~}
               {ℓ₃ₒ ℓ₃ₐ ℓ₃~ : Level} {𝔼 : ecategoryₗₑᵥ ℓ₃ₒ ℓ₃ₐ ℓ₃~}
                 → efunctorₗₑᵥ 𝔻 𝔼 → efunctorₗₑᵥ [ ℂ , 𝔻 ]ᶜᵃᵗ [ ℂ , 𝔼 ]ᶜᵃᵗ
postcmp-Fctr {𝔼 = 𝔼} F = record
  { FObj = λ H → F ○ H
  ; FHom = natt-fctr-post F
  ; isF = record
        { ext = λ eq X → F.ext (eq X)
        ; id = λ _ → F.id
        ; cmp = λ _ _ _ → F.cmp _ _
        }
  }
  where module F = efctr F

postcmp-Fctr-natt : {ℓ₁ₒ ℓ₁ₕ ℓ₁~ : Level} {ℂ : ecategoryₗₑᵥ ℓ₁ₒ ℓ₁ₕ ℓ₁~}
                    {ℓ₂ₒ ℓ₂ₕ ℓ₂~ : Level} {𝔻 : ecategoryₗₑᵥ ℓ₂ₒ ℓ₂ₕ ℓ₂~}
                    {ℓ₃ₒ ℓ₃ₐ ℓ₃~ : Level} {𝔼 : ecategoryₗₑᵥ ℓ₃ₒ ℓ₃ₐ ℓ₃~}
                    {F G : efunctorₗₑᵥ 𝔻 𝔼}
                      → F ⇒ G → postcmp-Fctr {ℂ = ℂ} F ⇒ postcmp-Fctr G
postcmp-Fctr-natt {𝔼 = 𝔼} {F} {G} α = record
  { fnc = λ {H} → natt-fctr-pre H α
  ; nat = λ γ X → nt.nat α (nt.fnc γ {X}) 
  }
  where module nt = natural-transformation



-------------------------------------------------------------
-- Small category of efunctors between two small ecategories
-------------------------------------------------------------

Fctrₛₘ : (ℂ 𝔻 : small-ecategory) → small-ecategory
Fctrₛₘ ℂ 𝔻 = Fctrₗₑᵥ ℂ 𝔻

---------------------------------------------------------------------
-- Large category of efunctors between two locally small ecategories
---------------------------------------------------------------------

Fctrₗₛ : (ℂ 𝔻 : ecategory) → large-ecategory
Fctrₗₛ ℂ 𝔻 = Fctrₗₑᵥ ℂ 𝔻



--------------------------------------------------------------
-- Category of diagrams,
-- i.e. the category of functors from a small category.
-- When ℂ is locally small, Diagr 𝕁 ℂ is locally small too.
--------------------------------------------------------------

Diagr : (𝕁 : small-ecategory){ℓₒ ℓₕ ℓ~ : Level}(ℂ : ecategoryₗₑᵥ ℓₒ ℓₕ ℓ~)
            → ecategoryₗₑᵥ (ℓₒ ⊔ ℓₕ ⊔ ℓ~) (ℓₕ ⊔ ℓ~) ℓ~
Diagr 𝕁 ℂ = Fctrₗₑᵥ 𝕁 ℂ


const-diagr-on : {𝕁 : small-ecategory}{ℓₒ ℓₕ ℓ~ : Level}{ℂ : ecategoryₗₑᵥ ℓₒ ℓₕ ℓ~}
                    → ecat.Obj ℂ → 𝕁 diag-in ℂ
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
--Cone/ {𝕀} {ℂ = ℂ} D = const

const-Diagr : (𝕁 : small-ecategory){ℓₒ ℓₕ ℓ~ : Level}(ℂ : ecategoryₗₑᵥ ℓₒ ℓₕ ℓ~)
                 → efunctorₗₑᵥ ℂ (Diagr 𝕁 ℂ)
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

---------------------------------
-- Category of discrete diagrams
---------------------------------

discDiagr : (I : Set){ℓₒ ℓₕ ℓ~ : Level}(ℂ : ecategoryₗₑᵥ ℓₒ ℓₕ ℓ~) → ecategoryₗₑᵥ ℓₒ ℓₕ ℓ~
discDiagr I ℂ = record
  { Obj = I → ℂ.Obj
  ; Hom = λ D D' → stdsections {A = I} (λ i → ℂ.Hom (D i) (D' i))
  ; isecat = record
           { _∘_ = λ g f i → g i ℂ.∘ f i
           ; idar = λ D i → ℂ.idar (D i)
           ; ∘ext = λ _ _ _ _ pff pfg i → ℂ.∘ext _ _ _ _ (pff i) (pfg i)
           ; lidax = λ f i → ℂ.lidax (f i)
           ; ridax = λ f i → ℂ.ridax (f i)
           ; assoc = λ f g h i → ℂ.assoc (f i) (g i) (h i)
           }
  }
  where module ℂ = ecat ℂ


const-discDiagr : (I : Set){ℓₒ ℓₕ ℓ~ : Level}(ℂ : ecategoryₗₑᵥ ℓₒ ℓₕ ℓ~)
                     → efunctorₗₑᵥ ℂ (discDiagr I ℂ)
const-discDiagr I ℂ = record
  { FObj = λ X _ → X
  ; FHom = λ f _ → f
  ; isF = record
        { ext = λ pf _ → pf
        ; id = λ _ → ℂ.r
        ; cmp = λ _ _ _ → ℂ.r
        }
  }
  where module ℂ = ecategory-aux ℂ using (r)



-- functors on functors induced by functors

fctr-precmp : {ℓ₁ₒ ℓ₁ₕ ℓ₁~ : Level}{ℂ : ecategoryₗₑᵥ ℓ₁ₒ ℓ₁ₕ ℓ₁~}
              {ℓ₂ₒ ℓ₂ₕ ℓ₂~ : Level}{𝔻 : ecategoryₗₑᵥ ℓ₂ₒ ℓ₂ₕ ℓ₂~}
              (F : efunctorₗₑᵥ ℂ 𝔻)
              {ℓₒ ℓₕ ℓ~ : Level}(𝕏 : ecategoryₗₑᵥ ℓₒ ℓₕ ℓ~)
                → efunctorₗₑᵥ [ 𝔻 , 𝕏 ]ᶜᵃᵗ [ ℂ , 𝕏 ]ᶜᵃᵗ
fctr-precmp F 𝕏 = record
  { FObj = λ K → K ○ F
  ; FHom = natt-fctr-pre F
  ; isF = record
        { ext = λ eq A → eq (F.ₒ A)
        ; id = λ {_} _ → r
        ; cmp = λ _ _ _ → r
        }
  }
  where module F = efctr F
        open ecategory-aux-only 𝕏 using (r)
