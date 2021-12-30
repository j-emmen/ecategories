
{-# OPTIONS --without-K #-}

module ecats.functors.defs.presheaf where

import tt-basics.setoids using (setoid)
open import ecats.basic-defs.ecat-def&not
open import ecats.functors.defs.efunctor-d&n
open import ecats.functors.defs.natural-iso
open import ecats.functors.defs.natural-transformation
open import ecats.constructions.opposite
open import ecats.constructions.functor-ecat
open import ecats.concr-ecats.Std-lev


-- Presheaves in this sense, where the 

presheafₗₑᵥ_at : {ℓₒ ℓₐ ℓ~ : Level}(ℂ : ecategoryₗₑᵥ ℓₒ ℓₐ ℓ~)(ℓo ℓr : Level)
                  → Set (ecat.ℓₐₗₗ ℂ ⊔ Stdₗₑᵥ.ℓₐₗₗ ℓo ℓr)
presheafₗₑᵥ ℂ at ℓo ℓr = efunctorₗₑᵥ (ℂ ᵒᵖ) (Stdₗₑᵥ ℓo ℓr)
                      where module ℂ = ecat ℂ

presheafₗₑᵥ : {ℓₒ ℓₐ ℓ~ : Level}(ℂ : ecategoryₗₑᵥ ℓₒ ℓₐ ℓ~)
                  → Set (ecat.ℓₐₗₗ ℂ ⊔ Stdₗₑᵥ.ℓₐₗₗ ℓₐ ℓ~)
presheafₗₑᵥ ℂ = presheafₗₑᵥ ℂ at ℂ.ℓₐᵣᵣ ℂ.ℓ~
             where module ℂ = ecat ℂ

module presheafₗₑᵥ {ℓₒ ℓₐ ℓ~ : Level}{ℂ : ecategoryₗₑᵥ ℓₒ ℓₐ ℓ~}(F : presheafₗₑᵥ ℂ)
                  where
  open ecat ℂ using (Obj; Hom)
  open efunctor-aux F public
  module ₒ (X : Obj) = StdObj (ₒ X)
  _ₒ~_ : {X : Obj}(x x' : || ₒ X ||) → Set ℓ~
  _ₒ~_ {X} x x' = ₒ._~_ X x x'
  module ₐ {Z Z' : Obj}(g : || Hom Z Z' ||) = StdHom (ₐ g)

copresheafₗₑᵥ_at : {ℓₒ ℓₐ ℓ~ : Level}(ℂ : ecategoryₗₑᵥ ℓₒ ℓₐ ℓ~)(ℓo ℓr : Level)
                    → Set (ecat.ℓₐₗₗ ℂ ⊔ Stdₗₑᵥ.ℓₐₗₗ ℓo ℓr) --ℓₐ ℓ~)
copresheafₗₑᵥ ℂ at ℓo ℓr = efunctorₗₑᵥ ℂ (Stdₗₑᵥ ℓo ℓr)
                        where module ℂ = ecat ℂ

copresheafₗₑᵥ : {ℓₒ ℓₐ ℓ~ : Level}(ℂ : ecategoryₗₑᵥ ℓₒ ℓₐ ℓ~)
                    → Set (ecat.ℓₐₗₗ ℂ ⊔ Stdₗₑᵥ.ℓₐₗₗ ℓₐ ℓ~)
copresheafₗₑᵥ ℂ = copresheafₗₑᵥ ℂ at ℂ.ℓₐᵣᵣ ℂ.ℓ~
               where module ℂ = ecat ℂ

module copresheafₗₑᵥ {ℓₒ ℓₐ ℓ~ : Level}{ℂ : ecategoryₗₑᵥ ℓₒ ℓₐ ℓ~}(F : copresheafₗₑᵥ ℂ)
                    where
  open ecat ℂ using (Obj; Hom)
  open efunctor-aux F public
  module ₒ (X : Obj) = StdObj (ₒ X)
  _ₒ~_ : {X : Obj}(x x' : || ₒ X ||) → Set ℓ~
  _ₒ~_ {X} x x' = ₒ._~_ X x x'
  module ₐ {Z Z' : Obj}(g : || Hom Z Z' ||) = StdHom (ₐ g)

psheaf-morₗₑᵥ : {ℓₒ ℓₐ ℓ~ : Level}{ℂ : ecategoryₗₑᵥ ℓₒ ℓₐ ℓ~}
                 → presheafₗₑᵥ ℂ → presheafₗₑᵥ ℂ → Set (ℓₒ ⊔ ℓₐ ⊔ ℓ~)
psheaf-morₗₑᵥ {ℂ = ℂ} = natural-transformation {ℂ = ℂ ᵒᵖ} {𝔻 = Stdₗₑᵥ ℂ.ℓₐᵣᵣ ℂ.ℓ~}
                     where module ℂ = ecat ℂ

module psheaf-morₗₑᵥ {ℓₒ ℓₐ ℓ~ : Level}{ℂ : ecategoryₗₑᵥ ℓₒ ℓₐ ℓ~}{F G : presheafₗₑᵥ ℂ}(μ : F ⇒ G) where
  open ecat ℂ using (Obj)
  open natural-transformation μ public
  private module ar {Z : Obj} = StdHom (fnc {Z})
  open ar public


-- The category of presheaves

private module PS {ℓₒ ℓₐ ℓ~ : Level}(ℂ : ecategoryₗₑᵥ ℓₒ ℓₐ ℓ~) = ecat (Fctrₗₑᵥ ℂ (Stdₗₑᵥ ℓₐ ℓ~))
PShₗₑᵥ : {ℓₒ ℓₐ ℓ~ : Level}(ℂ : ecategoryₗₑᵥ ℓₒ ℓₐ ℓ~) → ecategoryₗₑᵥ (PS.ℓₒ ℂ) (PS.ℓₐᵣᵣ ℂ) (PS.ℓ~ ℂ)
PShₗₑᵥ ℂ = Fctrₗₑᵥ (ℂ ᵒᵖ) (Stdₗₑᵥ ℂ.ℓₐᵣᵣ ℂ.ℓ~)
        where module ℂ = ecat ℂ
coPShₗₑᵥ : {ℓₒ ℓₐ ℓ~ : Level}(ℂ : ecategoryₗₑᵥ ℓₒ ℓₐ ℓ~) → ecategoryₗₑᵥ (PS.ℓₒ ℂ) (PS.ℓₐᵣᵣ ℂ) (PS.ℓ~ ℂ)
coPShₗₑᵥ ℂ = Fctrₗₑᵥ ℂ (Stdₗₑᵥ ℂ.ℓₐᵣᵣ ℂ.ℓ~)
           where module ℂ = ecat ℂ




-- Presheaves on a locally small category

presheaf : {ℓₒ : Level}(ℂ : ecategoryₗₑᵥ ℓₒ 0ₗₑᵥ 0ₗₑᵥ) → Set (ℓₒ ⊔ 1ₗₑᵥ)
presheaf ℂ = presheafₗₑᵥ ℂ
module presheaf = presheafₗₑᵥ

psheaf-mor : {ℓₒ : Level}{ℂ : ecategoryₗₑᵥ ℓₒ 0ₗₑᵥ 0ₗₑᵥ}
                 → presheaf ℂ → presheaf ℂ → tt-basics.setoids.setoid {ℓₒ} {ℓₒ}
psheaf-mor {ℂ = ℂ} = NatTr {ℂ = ℂ ᵒᵖ} {𝔻 = Std} 

module psheaf-mor {ℂ : ecategory}{F G : presheaf ℂ}(μ : F ⇒ G) where
  open ecat ℂ using (Obj)
  open natural-transformation μ public
  private module ar {Z : Obj} = StdHom (fnc {Z})
  open ar public

PSh : (ℂ : ecategory) → large-ecategory
PSh ℂ = Fctrₗₛ (ℂ ᵒᵖ) Std
