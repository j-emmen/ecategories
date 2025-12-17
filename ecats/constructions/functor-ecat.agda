
{-# OPTIONS --without-K #-}

module ecats.constructions.functor-ecat where

open import tt-basics.setoids using (stdsections)
open import ecats.basic-defs.ecat-def&not
open import ecats.isomorphism
open import ecats.functors.defs.efunctor-d&n
open import ecats.functors.defs.natural-transformation
open import ecats.functors.defs.natural-iso
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
              {ℓ₃ₒ ℓ₃ₐ ℓ₃~ : Level} (𝔼 : ecategoryₗₑᵥ ℓ₃ₒ ℓ₃ₐ ℓ₃~)
               → efunctorₗₑᵥ ℂ 𝔻 → efunctorₗₑᵥ [ 𝔻 , 𝔼 ]ᶜᵃᵗ [ ℂ , 𝔼 ]ᶜᵃᵗ
precmp-Fctr 𝔼 F = record
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
                    {ℓ₃ₒ ℓ₃ₐ ℓ₃~ : Level} (𝔼 : ecategoryₗₑᵥ ℓ₃ₒ ℓ₃ₐ ℓ₃~)
                    {F G : efunctorₗₑᵥ ℂ 𝔻}
                      → F ⇒ G → precmp-Fctr 𝔼 F ⇒ precmp-Fctr 𝔼 G
precmp-Fctr-natt 𝔼 {F} {G} α = record
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
postcmp-Fctr-natt α = record
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



-- functors in two arguments as functors into functor categories

module uncurry-efunctor-into-functor-cat {ℓₒ₁ ℓₐ₁ ℓ~₁ : Level}{ℂ₁ : ecategoryₗₑᵥ ℓₒ₁ ℓₐ₁ ℓ~₁}
                                         {ℓₒ₂ ℓₐ₂ ℓ~₂ : Level}{ℂ₂ : ecategoryₗₑᵥ ℓₒ₂ ℓₐ₂ ℓ~₂}
                                         {ℓₒ₃ ℓₐ₃ ℓ~₃ : Level}{𝔻 : ecategoryₗₑᵥ ℓₒ₃ ℓₐ₃ ℓ~₃}
                                         (F : efunctorₗₑᵥ ℂ₁ [ ℂ₂ , 𝔻 ]ᶜᵃᵗ)
                                         where
  private
    module ℂ₁ = ecat-with-isos ℂ₁
    module ℂ₂ = ecat-with-isos ℂ₂
    module 𝔻 = ecat-with-isos 𝔻

  module l = efunctor-aux F
  module lₒ (A : ℂ₁.Obj) = efunctor-aux (l.ₒ A) -- : efunctor ℂ₂ 𝔻
  module lₐ {X Y : ℂ₁.Obj} (f : || ℂ₁.Hom X Y ||) = natural-transformation (l.ₐ f)
                                                                 -- : l.ₒ X ⇒ l.ₒ Y
  rₒ : ℂ₂.Obj →  efunctorₗₑᵥ ℂ₁ 𝔻
  rₒ A = record
    { FObj = λ X → lₒ.ₒ X A
    ; FHom = λ {X} {Y} f → lₐ.fnc f {A}
    ; isF = record
          { ext = λ eq → l.ext eq A
          ; id = λ {X} → l.id {X} A
          ; cmp = λ f g → l.cmp f g A
          }
    }
  module rₒ (A : ℂ₂.Obj) = efunctor-aux (rₒ A)

  rl~lr : {A₁ B₁ : ℂ₁.Obj} (f₁ : || ℂ₁.Hom A₁ B₁ ||)
          {A₂ B₂ : ℂ₂.Obj} (f₂ : || ℂ₂.Hom A₂ B₂ ||)
             → rₒ.ₐ B₂ f₁ 𝔻.∘ lₒ.ₐ A₁ f₂ 𝔻.~ lₒ.ₐ B₁ f₂ 𝔻.∘ rₒ.ₐ A₂ f₁
  rl~lr f₁ f₂ = lₐ.nat f₁ f₂
  lr~rl : {A₁ B₁ : ℂ₁.Obj} (f₁ : || ℂ₁.Hom A₁ B₁ ||)
          {A₂ B₂ : ℂ₂.Obj} (f₂ : || ℂ₂.Hom A₂ B₂ ||)
             → lₒ.ₐ B₁ f₂ 𝔻.∘ rₒ.ₐ A₂ f₁ 𝔻.~ rₒ.ₐ B₂ f₁ 𝔻.∘ lₒ.ₐ A₁ f₂
  lr~rl f₁ f₂ = lₐ.natˢ f₁ f₂

  rₐ : {A B : ℂ₂.Obj} → || ℂ₂.Hom A B || → natural-transformation (rₒ A) (rₒ B)
  rₐ {A} {B} f = record
    { fnc = λ {X} → lₒ.ₐ X f
    ; nat = λ f₁ → lr~rl f₁ f
    }
  module rₐ {A B : ℂ₂.Obj} (f : || ℂ₂.Hom A B ||) = natural-transformation (rₐ f)

  ₒ : ℂ₁.Obj → ℂ₂.Obj → 𝔻.Obj
  ₒ A B = lₒ.ₒ A B
  ₐ : {A₁ B₁ : ℂ₁.Obj} {A₂ B₂ : ℂ₂.Obj}
           → || ℂ₁.Hom A₁ B₁ || → || ℂ₂.Hom A₂ B₂ || → || 𝔻.Hom (ₒ A₁ A₂) (ₒ B₁ B₂) ||
  ₐ {A₁} {B₁} {A₂} {B₂} f₁ f₂ = rₒ.ₐ B₂ f₁ 𝔻.∘ lₒ.ₐ A₁ f₂
  -- NB:
  -- ₐ (ℂ.idar X) f₂ = lₒ.ₐ X f₂ ℂ.∘ r.ₐ A (ℂ.idar X) ~ lₒ.ₐ X f₂ ℂ.∘ ℂ.idar (ₒ X A)
  -- ₐ f (ℂ.idar X) = lₒ.ₐ B (ℂ.idar X) ℂ.∘ r.ₐ X f ~ ℂ.idar (ₒ B X) ℂ.∘ r.ₐ X f

  ext : {A₁ B₁ : ℂ₁.Obj} {A₂ B₂ : ℂ₂.Obj}
         {f₁ f₁' : || ℂ₁.Hom A₁ B₁ ||} {f₂ f₂' : || ℂ₂.Hom A₂ B₂ ||}
             → f₁ ℂ₁.~ f₁' → f₂ ℂ₂.~ f₂' → ₐ f₁ f₂ 𝔻.~ ₐ f₁' f₂'
  ext eq₁ eq₂ = ∘e (lₒ.ext _ eq₂) (rₒ.ext _ eq₁)
    where open ecategory-aux-only 𝔻 using (∘e)

  pres-iso-pair : {A₁ B₁ : ℂ₁.Obj} {A₂ B₂ : ℂ₂.Obj}
                  {f₁  : || ℂ₁.Hom A₁ B₁ ||} {f₂ : || ℂ₂.Hom A₂ B₂ ||}
                  {g₁  : || ℂ₁.Hom B₁ A₁ ||} {g₂ : || ℂ₂.Hom B₂ A₂ ||}
                    → ℂ₁.is-iso-pair f₁ g₁ → ℂ₂.is-iso-pair f₂ g₂
                      → 𝔻.is-iso-pair (ₐ f₁ f₂) (ₐ g₁ g₂)
  pres-iso-pair {A₁} {B₁} {A₂} {B₂} {f₁} {f₂} {g₁} {g₂} isop₁ isop₂ =
    𝔻.isopair-extr (𝔻.isopair-cmp (lₒ.ᵢₛₒ A₁ isop₂) (rₒ.ᵢₛₒ B₂ isop₁)) (rl~lr g₁ g₂)

-- end uncurry-efunctor-into-functor-cat


module uncurry-natt-into-functor-cat {ℓₒ₁ ℓₐ₁ ℓ~₁ : Level}{ℂ₁ : ecategoryₗₑᵥ ℓₒ₁ ℓₐ₁ ℓ~₁}
                                     {ℓₒ₂ ℓₐ₂ ℓ~₂ : Level}{ℂ₂ : ecategoryₗₑᵥ ℓₒ₂ ℓₐ₂ ℓ~₂}
                                     {ℓₒ₃ ℓₐ₃ ℓ~₃ : Level}{𝔻 : ecategoryₗₑᵥ ℓₒ₃ ℓₐ₃ ℓ~₃}
                                     {F G : efunctorₗₑᵥ ℂ₁ [ ℂ₂ , 𝔻 ]ᶜᵃᵗ}
                                     (φ : F ⇒ G)
                                     where
  private
    module ℂ₁ = ecat ℂ₁
    module ℂ₂ = ecat ℂ₂
    module 𝔻 = ecat 𝔻
    module F = uncurry-efunctor-into-functor-cat F
    module G = uncurry-efunctor-into-functor-cat G

  open natural-transformation φ public renaming (fnc to l; nat to lnat; natˢ to lnatˢ)
  open module l (A : ℂ₁.Obj) = natural-transformation (l {A}) public
                              renaming (nat to rnat; natˢ to rnatˢ)
  nat : {A₁ B₁ : ℂ₁.Obj} (f₁ : || ℂ₁.Hom A₁ B₁ ||)
        {A₂ B₂ : ℂ₂.Obj} (f₂ : || ℂ₂.Hom A₂ B₂ ||)
             → fnc B₁ {B₂} 𝔻.∘ F.ₐ f₁ f₂ 𝔻.~ G.ₐ f₁ f₂ 𝔻.∘ fnc A₁ {A₂}
  nat {A₁} {B₁} f₁ {A₂} {B₂} f₂ = ~proof
    fnc B₁ {B₂} 𝔻.∘ F.ₐ f₁ f₂                         ~[ ass ⊙ ∘e r (lnat f₁ B₂) ⊙ assˢ ] /
    G.rₒ.ₐ B₂ f₁ 𝔻.∘ fnc A₁ {B₂} 𝔻.∘ F.lₒ.ₐ A₁ f₂      ~[ ∘e (rnat A₁ f₂) r ⊙ ass ]∎
    G.ₐ f₁ f₂ 𝔻.∘ fnc A₁ {A₂} ∎
    where open ecategory-aux-only 𝔻
  natˢ : {A₁ B₁ : ℂ₁.Obj} (f₁ : || ℂ₁.Hom A₁ B₁ ||)
         {A₂ B₂ : ℂ₂.Obj} (f₂ : || ℂ₂.Hom A₂ B₂ ||)
             → G.ₐ f₁ f₂ 𝔻.∘ fnc A₁ {A₂} 𝔻.~ fnc B₁ {B₂} 𝔻.∘ F.ₐ f₁ f₂
  natˢ f₁ f₂ = nat f₁ f₂ ˢ
    where open ecategory-aux-only 𝔻 using (_ˢ)
-- end uncurry-natt-into-functor-cat


module uncurry-nat-iso-into-functor-cat {ℓₒ₁ ℓₐ₁ ℓ~₁ : Level}{ℂ₁ : ecategoryₗₑᵥ ℓₒ₁ ℓₐ₁ ℓ~₁}
                                        {ℓₒ₂ ℓₐ₂ ℓ~₂ : Level}{ℂ₂ : ecategoryₗₑᵥ ℓₒ₂ ℓₐ₂ ℓ~₂}
                                        {ℓₒ₃ ℓₐ₃ ℓ~₃ : Level}{𝔻 : ecategoryₗₑᵥ ℓₒ₃ ℓₐ₃ ℓ~₃}
                                        {F G : efunctorₗₑᵥ ℂ₁ [ ℂ₂ , 𝔻 ]ᶜᵃᵗ}
                                        (φ : F ≅ₐ G)
                                        where
  private
    module ℂ₁ = ecat ℂ₁
    module ℂ₂ = ecat ℂ₂
    module 𝔻 where
      open ecat 𝔻 public
      open iso-d&p 𝔻 public
    module F = uncurry-efunctor-into-functor-cat F
    module G = uncurry-efunctor-into-functor-cat G

  open natural-iso φ public hiding (fnc; fnc⁻¹; nat; nat⁻¹; natˢ; nat⁻¹ˢ)
                            renaming (isiso to lisisopair; iddom to liddom; idcod to lidcod)
  open uncurry-natt-into-functor-cat natt public
  module ⁻¹ = uncurry-natt-into-functor-cat natt⁻¹
  open ⁻¹ using () renaming (fnc to fnc⁻¹) public

  isisopair : {M : ℂ₁.Obj} {N : ℂ₂.Obj} → 𝔻.is-iso-pair (fnc M {N}) (fnc⁻¹ M {N})
  isisopair {M} {N} = record
    { iddom = liddom N
    ; idcod = lidcod N
    }  
-- end uncurry-nat-iso-into-functor-cat
