
{-# OPTIONS --without-K #-}

module ecats.functors.defs.efunctor-not where

open import ecats.basic-defs.ecat-def&not
open import ecats.basic-defs.isomorphism
open import ecats.basic-defs.commut-shapes
open import ecats.functors.defs.efunctor

-- E-functor notation


module efunctor-aux-only {ℓ₁ ℓ₂ ℓ₃ ℓ₄ ℓ₅ ℓ₆}{ℂ : ecategoryₗₑᵥ ℓ₁ ℓ₂ ℓ₃}{𝔻 : ecategoryₗₑᵥ ℓ₄ ℓ₅ ℓ₆}
                         (F : efunctorₗₑᵥ ℂ 𝔻) where
  private    
    module catnot {ℓ₁ ℓ₂ ℓ₃}(ℂ : ecategoryₗₑᵥ ℓ₁ ℓ₂ ℓ₃) where
      open ecat ℂ public
      open comm-shapes ℂ public
    module ℂ where
      open catnot ℂ public
      open iso-defs ℂ public
    module 𝔻 where
      open catnot 𝔻 public
      open iso-defs 𝔻 public
    module F = efctr F
    
  -- only equational reasoning in 𝔻 is needed
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

  
  ᵢₛₒ : {A B : ℂ.Obj}{f : || ℂ.Hom A B ||}{f' : || ℂ.Hom B A ||}
             → ℂ.is-iso-pair f f' → 𝔻.is-iso-pair (F.ₐ f) (F.ₐ f')
  ᵢₛₒ {f = f} {invf} isopair = record
    { iddom = ∘ax iddom ⊙ F.id
    ; idcod = ∘ax idcod ⊙ F.id
    }
    where open ℂ.is-iso-pair isopair


  -- shapes
  
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

-- end module efunctor-aux-only



module efunctor-aux {ℓ₁ ℓ₂ ℓ₃ ℓ₄ ℓ₅ ℓ₆}{ℂ : ecategoryₗₑᵥ ℓ₁ ℓ₂ ℓ₃}{𝔻 : ecategoryₗₑᵥ ℓ₄ ℓ₅ ℓ₆}
                    (F : efunctorₗₑᵥ ℂ 𝔻) where
  open efunctorₗₑᵥ F public
  open efunctor-aux-only F public
-- end efunctor-aux
