{-# OPTIONS --without-K #-}

module ecats.constructions.functor-from-limits where

open import ecats.basic-defs.ecat-def&not
open import ecats.functors.defs.efunctor-d&n
open import ecats.functors.defs.natural-transformation
open import ecats.constructions.functor-ecat
open import ecats.small-limits.defs.small-limit

module functor-defined-by-limits {ℓₒ₁ ℓₐ₁ ℓ~₁}{ℂ : ecategoryₗₑᵥ ℓₒ₁ ℓₐ₁ ℓ~₁}
                                 {ℓₒ₂ ℓₐ₂ ℓ~₂}{𝔻 : ecategoryₗₑᵥ ℓₒ₂ ℓₐ₂ ℓ~₂}
                                 {𝕀 : small-ecategory}(dgs : efunctorₗₑᵥ ℂ (Diagr 𝕀 𝔻))
                                 where
  private
    module ℂ = ecat ℂ
    module 𝔻 where
      open ecat 𝔻 public
      open small-limit-defs 𝔻 public
    module 𝕀 = ecat 𝕀
    module Dg where
      open ecat (Diagr 𝕀 𝔻) public
      module ₒ (D : Obj) where
        open efunctor-aux D public
      module ₐ {D D' : Obj}(α : || Hom D D' ||) where
        open natural-transformation α public
    module dgs where
      open efunctor-aux dgs public
      module ₒ (X : ℂ.Obj) = Dg.ₒ (ₒ X)
      module ₐ {X Y : ℂ.Obj}(f : || ℂ.Hom X Y ||) = Dg.ₐ (ₐ f)

  module Far (lms : (X : ℂ.Obj) → 𝔻.limit-of (dgs.ₒ X)){X Y : ℂ.Obj}(f : || ℂ.Hom X Y ||) where
    private module lm (X : ℂ.Obj) = 𝔻.limit-of (lms X)

    ind-nt : natural-transformation (const-diagr-on (lm.Vx X)) (dgs.ₒ Y)
    ind-nt = record
      { fnc = λ {I} → dgs.ₐ.fnc f {I} 𝔻.∘ lm.π X I
      ; nat = λ {I} {J} u → ~proof
      (dgs.ₐ.fnc f {J} 𝔻.∘ lm.π X J) 𝔻.∘ 𝔻.idar (lm.Vx X)    ~[ ridgen (∘e (lm.tr X u ˢ) r) ] /
      dgs.ₐ.fnc f {J} 𝔻.∘ dgs.ₒ.ₐ X u 𝔻.∘ lm.π X I            ~[ ass ⊙ ∘e r (dgs.ₐ.nat f u) ⊙ assˢ ]∎
      dgs.ₒ.ₐ Y u 𝔻.∘ dgs.ₐ.fnc f {I} 𝔻.∘ lm.π X I ∎
      }
      where open ecategory-aux-only 𝔻
    ind-cn : Cone/.Obj (dgs.ₒ Y)
    ind-cn = record
      { L = lm.Vx X
      ; ar = ind-nt
      }

    lft : || 𝔻.Hom (lm.Vx X) (lm.Vx Y) ||
    lft = lm.unv.ar Y ind-cn    
  -- end Far
      
  F : (lms : (X : ℂ.Obj) → 𝔻.limit-of (dgs.ₒ X)) → efunctorₗₑᵥ ℂ 𝔻
  F lms = record
    { FObj = lm.Vx
    ; FHom = lft
    ; isF = record
          { ext = λ {X} {Y} {f} {f'} eq → lm.unv.uq Y (ind-cn f') λ I → ~proof
                lm.π Y I 𝔻.∘ lft f               ~[ lm.unv.tr Y (ind-cn f) I ] /
                dgs.ₐ.fnc f {I} 𝔻.∘ lm.π X I     ~[ ∘e r (dgs.ext eq I) ]∎
                dgs.ₐ.fnc f' {I} 𝔻.∘ lm.π X I ∎
          ; id = λ {X} → lm.unv.uq X (ind-cn (ℂ.idar X)) (λ I → ridgen (lidggˢ r (dgs.id I))) ˢ
          ; cmp = λ {X} {Y} {Z} f g → lm.unv.uq Z (ind-cn (g ℂ.∘ f)) λ I → ~proof
                lm.π Z I 𝔻.∘ Far.lft lms g 𝔻.∘ Far.lft lms f
                                               ~[ ass ⊙ ∘e r (lm.unv.tr Z (ind-cn g) I) ⊙ assˢ ] /
                dgs.ₐ.fnc g 𝔻.∘ lm.π Y I 𝔻.∘ Far.lft lms f     ~[ ∘e (lm.unv.tr Y (ind-cn f) I) r ] /
                dgs.ₐ.fnc g 𝔻.∘ dgs.ₐ.fnc f 𝔻.∘ lm.π X I       ~[ ass ⊙ ∘e r (dgs.∘ax-rf I) ]∎
                dgs.ₐ.fnc (g ℂ.∘ f) 𝔻.∘ lm.π X I ∎
          }
    }
    where module lm (X : ℂ.Obj) = 𝔻.limit-of (lms X)
          open ecategory-aux-only 𝔻
          open Far lms
-- end functor-defined-by-limits


fctr-from-lim : {ℓₒ₁ ℓₐ₁ ℓ~₁ : Level}{ℂ : ecategoryₗₑᵥ ℓₒ₁ ℓₐ₁ ℓ~₁}
                {ℓₒ₂ ℓₐ₂ ℓ~₂ : Level}{𝔻 : ecategoryₗₑᵥ ℓₒ₂ ℓₐ₂ ℓ~₂}
                {𝕀 : small-ecategory}(dgs : efunctorₗₑᵥ ℂ (Diagr 𝕀 𝔻))
                (lms : (X : ecat.Obj ℂ) → small-limit-defs.limit-of 𝔻 (efctr.ₒ dgs X))
                     → efunctorₗₑᵥ ℂ 𝔻
fctr-from-lim dgs = F
                  where open functor-defined-by-limits dgs
