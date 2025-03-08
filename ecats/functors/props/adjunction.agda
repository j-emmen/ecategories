
{-# OPTIONS --without-K #-}

module ecats.functors.props.adjunction where

open import ecats.basic-defs.ecat-def&not
--open import ecats.basic-defs.isomorphism
--open import ecats.basic-props.isomorphism
--open import ecats.basic-defs.initial
--open import ecats.finite-limits.defs.terminal
open import ecats.small-limits.defs.small-limit
open import ecats.functors.defs.efunctor-d&n
--open import ecats.functors.defs.natural-transformation
--open import ecats.functors.defs.natural-iso
--open import ecats.functors.defs.presheaf
--open import ecats.functors.defs.representable
open import ecats.functors.defs.preserves-small-limits
open import ecats.functors.defs.adjunction
--open import ecats.functors.props.representable
--open import ecats.constructions.opposite
--open import ecats.constructions.slice-ecat
--open import ecats.constructions.ecat-elements



module adjunction-bij-props {ℓₒ₁ ℓₐ₁ ℓ~₁}{ℂ : ecategoryₗₑᵥ ℓₒ₁ ℓₐ₁ ℓ~₁}
                            {ℓₒ₂ ℓₐ₂ ℓ~₂}{𝔻 : ecategoryₗₑᵥ ℓₒ₂ ℓₐ₂ ℓ~₂}
                            {F : efunctorₗₑᵥ ℂ 𝔻}{G : efunctorₗₑᵥ 𝔻 ℂ}
                            (adjbij : adjunction-bij F G)
                            where
  private
    module ℂ where
      open ecategory-aux ℂ public
      open small-limit-defs ℂ public
    module 𝔻  where
      open ecategory-aux 𝔻 public
      open small-limit-defs 𝔻 public
    module F = efunctor-aux F
    module G = efunctor-aux G
    module F⊣G where
      open adjunction-bij adjbij public
      open adjunction-bij-equat adjbij public


  module RAPL {𝕀 : small-ecategory}(D : 𝕀 diag-in 𝔻){lC : Cone/.Obj D}
              (lCislim : 𝔻.is-limit-cone lC)(A : Cone/.Obj (G ○ D))
              where
    private
      Cone/D : ecategoryₗₑᵥ (Cone/.ℓₒ D) (Cone/.ℓₐᵣᵣ D) (Cone/.ℓ~ D)
      Cone/GD : ecategoryₗₑᵥ (Cone/.ℓₒ (G ○ D)) (Cone/.ℓₐᵣᵣ (G ○ D)) (Cone/.ℓ~ (G ○ D))
      Cone/D = Cone/ D
      Cone/GD = Cone/ (G ○ D)
      module 𝕀 = ecat 𝕀
      module D = efctr D
      module Cone/D = Cone/ D
      module Cone/GD = Cone/ (G ○ D)
      module A = Cone/GD.ₒ A
      module lC where
        open Cone/D.ₒ lC public
        open 𝔻.is-limit-cone lCislim public
      GlC : Cone/GD.Obj
      GlC = Fcone G D lC
      rlA : Cone/D.Obj
      rlA = Cone/D.if-tr-then-ob {F.ₒ A.Vx} {λ i → F⊣G.rl.ap (A.leg i)}
                                 (λ {i} {j} ij → F⊣G.rl-sq (A.sides.nat ij) 𝔻.ˢ 𝔻.⊙ 𝔻.ridgg 𝔻.r F.id)

      un : || Cone/D.Hom rlA lC ||
      un = lC.unv rlA
      module un = lC.unv rlA

    ar : || Cone/GD.Hom A GlC ||
    ar = Cone/GD.if-tr-then-ar A GlC {F⊣G.lr.ap un.ar}
                               (λ i → (F⊣G.lr-sq (𝔻.ridgg 𝔻.r F.id 𝔻.⊙ un.tr i 𝔻.ˢ) ℂ.ˢ
            ℂ.⊙ ℂ.lidggˢ (ℂ.ridgen (F⊣G.idcod (A.leg i))) G.id) ℂ.⊙ ℂ.lidgg ℂ.r G.id)
    private module ar = Cone/GD.ₐ ar

{-
record
       { arL = F⊣G.lr.ap un.ar
       ; tr = λ I → ( ℂ.ridˢ ℂ.⊙ F⊣G.rl-sq-inv {g = F⊣G.lr.ap un.ar} {A.leg I}
                                                {ℂ.idar A.Vx} {lC.leg I}
                    (𝔻.ridgg 𝔻.r F.id 𝔻.⊙ (un.tr I 𝔻.ˢ 𝔻.⊙ 𝔻.∘e (F⊣G.iddom un.ar 𝔻.ˢ) 𝔻.r)) ) ℂ.ˢ
       }
-}

    uq : (f : || Cone/GD.Hom A GlC ||) → f Cone/GD.~ ar
    uq f = F⊣G.rl-mono (𝔻.~proof F⊣G.rl.ap f.ar
            ~[ un.uq (λ i → F⊣G.rl-sq (ℂ.rid ℂ.⊙ f.tr i ℂ.ˢ) 𝔻.ˢ 𝔻.⊙ 𝔻.ridgg 𝔻.r F.id) ] 𝔻./
                                 un.ar             ~[ F⊣G.iddom un.ar 𝔻.ˢ ]∎
                                 F⊣G.rl.ap ar.ar ∎)
         where module f = Cone/GD.ₐ f

  -- end RAPL
  

  RAPL : preserves-limits G
  RAPL = record
       { pres-lim = λ {_} {D} islim → record
                  { ! = ar D islim
                  ; !uniq = λ {A} → uq D islim A
                  }
       }
       where open RAPL

-- end adjunction-bij-props
