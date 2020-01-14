 
-- disable the K axiom:

{-# OPTIONS --without-K #-}

-- Agda version 2.5.4.1

module ecats.functors.defs.efunctor-not where

open import ecats.basic-defs.ecat-def&not
open import ecats.basic-defs.commut-shapes
open import ecats.functors.defs.efunctor


-- E-functor notation


module efunctor-aux-only {ℂ 𝔻 : ecategory} (F : efunctor ℂ 𝔻) where
  private    
    module macros (ℂ : ecategory) where
      open ecategory ℂ public
      open comm-shapes ℂ public
    module ℂ = macros ℂ
    module 𝔻 = macros 𝔻
    module F = efunctor F
    
  -- apparently only equational reasoning in 𝔻 is needed
  open ecategory-aux-only 𝔻
  

  idax : {A : ℂ.Obj} {f : || ℂ.Hom A A ||} → f ℂ.~ ℂ.idar A → F.ₐ f 𝔻.~ 𝔻.idar (F.ₒ A)
  idax pf = F.ext pf ⊙ F.id

  idaxˢ : {A : ℂ.Obj} {f : || ℂ.Hom A A ||} → f ℂ.~ ℂ.idar A → 𝔻.idar (F.ₒ A) 𝔻.~ F.ₐ f
  idaxˢ pf = idax pf ˢ 

  ∘ax-rf : {A B C : ℂ.Obj} {f : || ℂ.Hom A B ||} {g : || ℂ.Hom B C ||}
                → (F.ₐ g) 𝔻.∘ (F.ₐ f) 𝔻.~ F.ₐ (g ℂ.∘ f)
  ∘ax-rf {f = f} {g} = F.cmp f g

  ∘ax : {A B C : ℂ.Obj} {f : || ℂ.Hom A B ||} {g : || ℂ.Hom B C ||} {h : || ℂ.Hom A C ||}
          → g ℂ.∘ f ℂ.~ h → F.ₐ g 𝔻.∘ F.ₐ f 𝔻.~ F.ₐ h
  ∘ax pf = ∘ax-rf ⊙ F.ext pf

  ∘ax-rfˢ : {A B C : ℂ.Obj} {f : || ℂ.Hom A B ||} {g : || ℂ.Hom B C ||}
                → F.ₐ (g ℂ.∘ f) 𝔻.~ (F.ₐ g) 𝔻.∘ (F.ₐ f)
  ∘ax-rfˢ = ∘ax-rf ˢ

  ∘axˢ : {A B C : ℂ.Obj} {f : || ℂ.Hom A B ||} {g : || ℂ.Hom B C ||} {h : || ℂ.Hom A C ||}
          → g ℂ.∘ f ℂ.~ h → F.ₐ h 𝔻.~ F.ₐ g 𝔻.∘ F.ₐ f
  ∘axˢ pf = ∘ax pf ˢ

  ∘∘ : {A B B' C : ℂ.Obj} {f : || ℂ.Hom A B ||} {g : || ℂ.Hom B C ||}
        {f' : || ℂ.Hom A B' ||}  {g' : || ℂ.Hom B' C ||}
                 → g ℂ.∘ f ℂ.~ g' ℂ.∘ f' → (F.ₐ g) 𝔻.∘ (F.ₐ f) 𝔻.~ (F.ₐ g') 𝔻.∘ (F.ₐ f')
  ∘∘ pf = ∘ax-rf ⊙ F.ext pf ⊙ ∘ax-rfˢ

{-
  F∘tactˢ : {A B C : ℂ.Obj} → {f f' : || ℂ.Hom A B ||} → {g g' : || ℂ.Hom B C ||}
                     → < 𝔻.Hom (F.ₒ A) (F.ₒ C) > (F.ₐ g) 𝔻.∘ (F.ₐ f) ~ (F.ₐ g') 𝔻.∘ (F.ₐ f')
                       → < 𝔻.Hom (F.ₒ A) (F.ₒ C) > F.ₐ (g ℂ.∘ f) ~ F.ₐ (g' ℂ.∘ f')
  F∘tactˢ {A} {B} {C} {f} {f'} {g} {g'} pf = {!!} --F∘ˢ ⊙ pf ⊙ F∘
-}
    

  -- shapes images
  

  span/ : {A B : ℂ.Obj} → ℂ.span/ A B → 𝔻.span/ (F.ₒ A) (F.ₒ B)
  span/ spC = 𝔻.mkspan/ (F.ₐ a1) (F.ₐ a2)
             where open ℂ.span/ spC

  span : ℂ.span → 𝔻.span
  span spC = 𝔻.mkspan (F.ₐ a1) (F.ₐ a2)
            where open ℂ.span spC

  sq : ℂ.comm-square → 𝔻.comm-square
  sq sqC = 𝔻.mksq (𝔻.mksq/ (∘∘ sq-pf))
  -- {F.ₒ dl} {F.ₒ ur} {F.ₒ dr} {F.ₐ down} {F.ₐ right}  --{F.ₒ ul} {F.ₐ left} {F.ₐ up} 
          where open ℂ.comm-square sqC


{-
  isFullΣ : {A B : ℂ.Obj} → (g : || 𝔻.Hom (F.ₒ A) (F.ₒ B) ||) → Set
  isFullΣ {A} {B} g = Σ (|| ℂ.Hom A B ||) (λ f → < 𝔻.Hom (F.ₒ A) (F.ₒ B) > (F.ₐ f) ~ g)

  isFaithfulΣ : {A B : ℂ.Obj} → (f f' : || ℂ.Hom A B ||) → Set
  isFaithfulΣ {A} {B} f f' = < 𝔻.Hom (F.ₒ A) (F.ₒ B) > (F.ₐ f) ~ (F.ₐ f') → < ℂ.Hom A B > f ~ f'

  isESurjObjΣ : (D : 𝔻.Obj) → Set₁
  isESurjObjΣ D = Σ (ℂ.Obj) (λ A → (F.ₒ A) ≅ₒD D)
-}

-- end module efunctor-aux-only



module efunctor-aux {ℂ 𝔻 : ecategory} (F : efunctor ℂ 𝔻) where
  open efunctor F public
  open efunctor-aux-only F public
-- end efunctor-aux
