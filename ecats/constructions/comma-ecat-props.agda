{-# OPTIONS --without-K #-}

module ecats.constructions.comma-ecat-props where

open import tt-basics.basics using (prod; pair)
open import tt-basics.setoids hiding (||_||)
open import ecats.basic-defs.ecat-def&not
open import ecats.functors.defs.efunctor-d&n
open import ecats.functors.defs.natural-transformation
open import ecats.functors.defs.preserves-small-limits
open import ecats.small-limits.defs.small-limit
open import ecats.constructions.functor-ecat
open import ecats.constructions.comma-ecat


module slice-functor-limits {ℓₒl ℓₐl ℓ~l}{ℂ : ecategoryₗₑᵥ ℓₒl ℓₐl ℓ~l}
                            {ℓₒc ℓₐc ℓ~c}{𝔻 : ecategoryₗₑᵥ ℓₒc ℓₐc ℓ~c}
                            (F : efunctorₗₑᵥ ℂ 𝔻)(Y : ecat.Obj 𝔻)
                            (limℂ : has-small-limits ℂ)(Fpreslim : preserves-limits F)
                            where
  private
    module ℂ where
      open ecat ℂ public
      open small-limit-defs ℂ public
      open has-small-limits limℂ using (lim-of) public
    module 𝔻 where
      open ecat 𝔻 public
      open small-limit-defs 𝔻 public
    module F where
      open efunctor-aux F public
      open preserves-limits Fpreslim public
    module Y↓F where
      open ecat (Y ₒ↓ F) public
      open slice-funct-ecat F Y public
      open small-limit-defs (Y ₒ↓ F) public

  module lim-construction {𝕀 : small-ecategory}(D : 𝕀 diag-in (Y ₒ↓ F)) where
    private
      module 𝕀 = ecat 𝕀
      module Cn/D = Cone/ D
      module cone/D (cn : Cn/D.Obj) where
        open Cn/D.ₒ cn public
        module Vx = Y↓F.ₒ Vx
        module leg (I : 𝕀.Obj) = Y↓F.ₐ (leg I)
      UD : 𝕀 diag-in ℂ
      UD = ₒ↓frgt F Y ○ D
      module UD = efctr UD
      module D where
        open efunctor-aux D public
        module ₒ (I : 𝕀.Obj) = Y↓F.ₒ (ₒ I)
        module ₐ {I J : 𝕀.Obj}(u : || 𝕀.Hom I J ||) = Y↓F.ₐ (ₐ u)
      LUD : ℂ.limit-of UD
      LUD = ℂ.lim-of UD
      module LUD = ℂ.limit-of LUD
      FUD : 𝕀 diag-in 𝔻
      FUD = F ○ UD
      module FUD = efctr FUD
      FLUD : 𝔻.limit-of FUD
      FLUD = F.pres-limof LUD
      module FLUD = 𝔻.limit-of FLUD
      UD-as-cn : Cone/.Obj FUD
      UD-as-cn = record
        { L = Y
        ; ar = record
             { fnc = λ {I} → D.ₒ.ar I
             ; nat = λ {I} {J} u → ridgen (D.ₐ.tr u ˢ)
             }
        }
        where open ecategory-aux-only 𝔻 using (ridgen; _ˢ)
      module Dcn = Cone/.ₒ FUD UD-as-cn

    lim-vx : Y↓F.Obj
    lim-vx = record
      { R = LUD.Vx
      ; ar = FLUD.unv.ar UD-as-cn
      }

    lim-nt : natural-transformation (const-diagr-on {𝕀} lim-vx) D
    lim-nt = record
      { fnc = λ {I} → record
            { arR = LUD.π I
            ; tr = FLUD.unv.tr UD-as-cn I
            }
      ; nat = λ {I} {J} u → ridgen (LUD.tr u ˢ)
      }
      where open ecategory-aux-only ℂ using (ridgen; _ˢ)

    lim-cn : Cn/D.Obj
    lim-cn = record
      { L = lim-vx
      ; ar = lim-nt
      }
    private module lim-cn = cone/D lim-cn

    module lim-islim (cn : Cn/D.Obj) where
      private
        module cn = cone/D cn
        Ucn : Cone/.Obj UD
        Ucn = Fcone (ₒ↓frgt F Y) D cn
        module Ucn = Cone/.ₒ UD Ucn
        uar : || Y↓F.Hom cn.Vx lim-vx ||
        uar = record
          { arR = LUD.unv.ar Ucn
          ; tr = FLUD.unv.uq UD-as-cn (λ I → ~proof
          FLUD.π I 𝔻.∘ F.ₐ (LUD.unv.ar Ucn) 𝔻.∘ cn.Vx.ar  ~[ ass ⊙ ∘e r (F.∘ax (LUD.unv.tr Ucn I)) ] /
          F.ₐ (Ucn.leg I) 𝔻.∘ cn.Vx.ar                     ~[ cn.leg.tr I ]∎
          Dcn.leg I ∎)
          }
          where open ecategory-aux-only 𝔻
        module uar = Y↓F.ₐ uar

      ar : || Cn/D.Hom cn lim-cn ||
      ar = record
        { arL = uar
        ; tr = LUD.unv.tr Ucn
        }
        where open ecategory-aux-only ℂ
      uq : (f : || Cn/D.Hom cn lim-cn ||) → f Cn/D.~ ar
      uq f = LUD.unv.uq Ucn f.tr
           where module f = Cn/D.ₐ f
    -- end lim-islim
    
    lim-islim : Y↓F.is-limit-cone lim-cn
    lim-islim = record
      { ! = ar
      ; !uniq = λ {cn} → uq cn
      }
      where open lim-islim
  
  -- end lim-construction

  Y↓F-has-lim : has-small-limits (Y ₒ↓ F)
  Y↓F-has-lim = record
    { lim-of = λ D → record
             { cone = lim-cn D
             ; islim = lim-islim D
             }
    }
    where open lim-construction
-- end slice-functor-limits


ₒ↓has-limits slice-functor-ecat-has-limits : {ℓₒl ℓₐl ℓ~l : Level}{ℂ : ecategoryₗₑᵥ ℓₒl ℓₐl ℓ~l}
                                             {ℓₒc ℓₐc ℓ~c : Level}{𝔻 : ecategoryₗₑᵥ ℓₒc ℓₐc ℓ~c}
                                             (F : efunctorₗₑᵥ ℂ 𝔻)(Y : ecat.Obj 𝔻)
                                               → has-small-limits ℂ → preserves-limits F
                                                 → has-small-limits (Y ₒ↓ F)
slice-functor-ecat-has-limits F Y limℂ Fpreslim = Y↓F-has-lim
                                                where open slice-functor-limits F Y limℂ Fpreslim
ₒ↓has-limits = slice-functor-ecat-has-limits
                            
