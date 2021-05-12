
{-# OPTIONS --without-K #-}

module ecats.small-limits.defs.small-limit where

open import Agda.Primitive
open import ecats.basic-defs.ecat-def&not
open import ecats.functors.defs.efunctor-d&n
open import ecats.functors.defs.natural-transformation
open import ecats.constructions.functor-ecat
open import ecats.constructions.slice-ecat
open import ecats.finite-limits.defs.terminal


-- Locally-small ecategory of cones over a diagram D

Cone/ : {𝕀 : small-ecategory}{ℂ : ecategory}(D : diagram 𝕀 ℂ) → ecategory
Cone/ {𝕀} {ℂ} D = const-Diagr 𝕀 ℂ // D

private
  module Cone/ {𝕀 : small-ecategory}{ℂ : ecategory}(D : diagram 𝕀 ℂ) where
    private
      module 𝕀 = ecat 𝕀
      module ℂ = ecategory ℂ
      module D = diagram D
      module Cn/D = ecategory (Cone/ D)
    --open ecategory (Cone/ D) using (Obj; Hom)
    -- renaming the components of the natural transformation
    module ₒ (cone : Cn/D.Obj) where
      open funct-slice-ecat.ₒ (const-Diagr 𝕀 ℂ) D cone renaming (L to Vx) public
      module ar = natural-transformation ar
      leg : (i : 𝕀.Obj) → || ℂ.Hom Vx (D.ₒ i) ||
      leg = λ i → ar.fnc {i}
      tr : {i j : 𝕀.Obj}(ij : || 𝕀.Hom i j ||) → D.ₐ ij ℂ.∘ leg i ℂ.~ leg j
      tr = λ ij → ar.nat ij ˢ ⊙ rid
         where open ecategory-aux-only ℂ using (_⊙_; _ˢ; rid)
    if-tr-then-ar : (cn cn' : Cn/D.Obj){f : || ℂ.Hom (ₒ.Vx cn) (ₒ.Vx cn') ||}
                        → (∀ i → ₒ.leg cn' i ℂ.∘ f ℂ.~ ₒ.leg cn i)
                          → || Cn/D.Hom cn cn' ||
    if-tr-then-ar cn cn' {f} pf = record { arL = f ; tr = pf }
    module ₐ {cone cone' : Cn/D.Obj}(cone-ar : || Cn/D.Hom cone cone' ||) where
      open funct-slice-ecat.ₐ (const-Diagr 𝕀 ℂ) D cone-ar renaming (arL to ar) public
    open ecategory-aux (Cone/ D) public
    open terminal-defs (Cone/ D) public


MultiSpan/ : {I : Set}(ℂ : ecategory)(D : I → ecat.Obj ℂ) → ecategory
MultiSpan/ {I} ℂ D = const-discDiagr I ℂ // D


private
  module MSpan/ {I : Set}(ℂ : ecategory)(D : I → ecat.Obj ℂ) where
    private
      module ℂ = ecat ℂ
      module MS/D = ecategory (MultiSpan/ ℂ D)
    -- renaming the components of the natural transformation
    module ₒ (span : MS/D.Obj) where
      open funct-slice-ecat.ₒ (const-discDiagr I ℂ) D span renaming (L to Vx) public
      module ar = natural-transformation ar
      leg : (i : I) → || ℂ.Hom Vx (D i) ||
      leg = λ i → ar.fnc {i}
      --tr : {i j : I}(ij : i == j ||) → D.ₐ ij ℂ.∘ leg i ℂ.~ leg j
      --tr = λ ij → ar.nat ij ˢ ⊙ rid
        -- where open ecategory-aux-only ℂ using (_⊙_; _ˢ; rid)
    if-tr-then-ar : (cn cn' : MS/D.Obj){f : || ℂ.Hom (ₒ.Vx cn) (ₒ.Vx cn') ||}
                        → (∀ i → ₒ.leg cn' i ℂ.∘ f ℂ.~ ₒ.leg cn i)
                          → || MS/D.Hom cn cn' ||
    if-tr-then-ar cn cn' {f} pf = record { arL = f ; tr = pf }
    module ₐ {span span' : MS/D.Obj}(span-ar : || MS/D.Hom span span' ||) where
      open funct-slice-ecat.ₐ (const-discDiagr I ℂ) D span-ar renaming (arL to ar) public
    open ecategory-aux (MultiSpan/ ℂ D) public
    open terminal-defs (MultiSpan/ ℂ D) public




module small-limit-defs (ℂ : ecategory) where

  is-universal-cone-over : {𝕀 : small-ecategory}{D : diagram 𝕀 ℂ}(cone : Cone/.Obj D)
                              → Set₁
  is-universal-cone-over {𝕀} {D} cone = Cone/.is-terminal D cone

  record limit-of {𝕀 : small-ecategory}(D : diagram 𝕀 ℂ) : Set₁ where
    private
      --module 𝕀 = ecategory-aux 𝕀
      module ℂ = ecategory ℂ
      module Cn = Cone/.ₒ D
      --module Cone/D = Cone/ D
    field
      cone : Cone/.Obj D
      islim : is-universal-cone-over cone
    open Cone/.ₒ D cone renaming (leg to π; ar to π-natt) public
    module unv (cn : Cone/.Obj D) where
      private module cn = Cn cn
      open Cone/.is-terminal D islim
      open Cone/.ₐ D (! cn) public
      uq : {f : || ℂ.Hom cn.Vx Vx ||}(trf : ∀ i → π i ℂ.∘ f ℂ.~ cn.leg i)
              → f ℂ.~ ar
      uq {f} tr = !uniq {cn} (Cone/.if-tr-then-ar D cn cone tr)
    π-jm :  (cn : Cone/.Obj D){f g : || ℂ.Hom (Cn.Vx cn) Vx ||}
            (trf : ∀ i → π i ℂ.∘ f ℂ.~ Cn.leg cn i)(trg : ∀ i → π i ℂ.∘ g ℂ.~ Cn.leg cn i)
              → f ℂ.~ g
    π-jm cn trf trg = !uqg {f = Cone/.if-tr-then-ar D cn cone trf}
                           {g = Cone/.if-tr-then-ar D cn cone trg}
                    where open Cone/.is-terminal D islim


  is-product : {I : Set}{ℂ : ecategory}{D : I → ecat.Obj ℂ}(span : MSpan/.Obj ℂ D) → Set₁
  is-product {_} {ℂ} {D} = MSpan/.is-terminal ℂ D
  
  record product-of {I : Set}(D : I → ecat.Obj ℂ) : Set₁ where
    private
      module ℂ = ecategory ℂ
      module MS/D = MSpan/ ℂ D
    field
      ×span/ : MS/D.Obj
      isprd : is-product ×span/
    open MS/D.ₒ ×span/ renaming (leg to π; ar to π-natt) public
    module unv (sp : MS/D.Obj) where
      private module sp = MS/D.ₒ sp
      open MS/D.is-terminal isprd
      open MS/D.ₐ (! sp) public
      uq : {f : || ℂ.Hom sp.Vx Vx ||}(trf : ∀ i → π i ℂ.∘ f ℂ.~ sp.leg i)
              → f ℂ.~ ar
      uq {f} tr = !uniq {sp} (MS/D.if-tr-then-ar sp ×span/ tr)
    π-jm :  (sp : MS/D.Obj){f g : || ℂ.Hom (MS/D.ₒ.Vx sp) Vx ||}
            (trf : ∀ i → π i ℂ.∘ f ℂ.~ MS/D.ₒ.leg sp i)(trg : ∀ i → π i ℂ.∘ g ℂ.~ MS/D.ₒ.leg sp i)
              → f ℂ.~ g
    π-jm sp trf trg = !uqg {f = MS/D.if-tr-then-ar sp ×span/ trf}
                           {g = MS/D.if-tr-then-ar sp ×span/ trg}
                    where open MS/D.is-terminal isprd

-- end small-limit-defs



-- {-
--   record cone-over {𝕀 : small-ecategory}(D : diagram 𝕀 ℂ) : Set₁ where
--     private
--       module 𝕀 = ecategory-aux 𝕀
--       module D = efunctor-aux D
--     field
--       Vx : Obj
--       π : (i : 𝕀.Obj) → || Hom Vx (D.ₒ i) ||
--       tr : {i j : 𝕀.Obj}(ij : || 𝕀.Hom i j ||) → D.ₐ ij ∘ π i ~ π j
-- -}
 
-- {-
--   record is-universal-cone-under {𝕀 : small-ecategory}{D : diagram 𝕀 ℂ}(cone : Cone/.Obj D)
--                                  : Set₁ where
--     private
--       module 𝕀 = ecategory-aux 𝕀
--       module D = efunctor-aux D
--       --module cn = cone-over cone
      
--     field
--       is-term-cone : Cone/.is-terminal D cone
-- -}
