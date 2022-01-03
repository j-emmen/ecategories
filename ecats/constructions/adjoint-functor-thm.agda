{-# OPTIONS --without-K #-}

module ecats.constructions.adjoint-functor-thm where

open import ecats.basic-defs.ecat-def&not
open import ecats.basic-defs.initial
open import ecats.basic-props.initial
open import ecats.functors.defs.efunctor-d&n
open import ecats.functors.defs.natural-transformation
open import ecats.functors.defs.adjunction
open import ecats.functors.defs.preserves-small-limits
open import ecats.constructions.comma-ecat
open import ecats.constructions.comma-ecat-props
open import ecats.small-limits.defs.small-limit
open import ecats.small-limits.props.small-limit



module solution-set-condition-defs {ℓₒ₁ ℓₐ₁ ℓ~₁}{ℂ : ecategoryₗₑᵥ ℓₒ₁ ℓₐ₁ ℓ~₁}
                                   {ℓₒ₂ ℓₐ₂ ℓ~₂}{𝔻 : ecategoryₗₑᵥ ℓₒ₂ ℓₐ₂ ℓ~₂}
                                   (F : efunctorₗₑᵥ ℂ 𝔻)
                                   where
  private
    module ℂ = ecat ℂ
    module 𝔻 = ecat 𝔻
    module F = efctr F

  record families (Y : 𝔻.Obj) : Set (1ₗₑᵥ ⊔ ℂ.ℓₒ ⊔ 𝔻.ℓₐᵣᵣ) where
    field
      Idx : Set
      obs : Idx → ℂ.Obj
      ars : (i : Idx) → || 𝔻.Hom Y (F.ₒ (obs i) ) ||
      
  record unv-prop {Y : 𝔻.Obj}(fams : families Y){X : ℂ.Obj}(g : || 𝔻.Hom Y (F.ₒ X) ||) : Set (ℂ.ℓₐᵣᵣ ⊔ 𝔻.ℓ~) where
    open families fams
    field
      idx : Idx
      ar : || ℂ.Hom (obs idx) X ||
      tr : F.ₐ ar 𝔻.∘ ars idx 𝔻.~ g

  record solution-set-on (Y : 𝔻.Obj) : Set (1ₗₑᵥ ⊔ ℂ.ℓₙₒ~ ⊔ 𝔻.ℓₕₒₘ) where
    field
      fams : families Y
      unv : {X : ℂ.Obj}(g : || 𝔻.Hom Y (F.ₒ X) ||) → unv-prop fams g
    open families fams public
    module unv {X : ℂ.Obj}(g : || 𝔻.Hom Y (F.ₒ X) ||) = unv-prop (unv g)
-- end solution-set-condition-defs


record has-solution-set-condition {ℓₒ₁ ℓₐ₁ ℓ~₁}{ℂ : ecategoryₗₑᵥ ℓₒ₁ ℓₐ₁ ℓ~₁}
                                  {ℓₒ₂ ℓₐ₂ ℓ~₂}{𝔻 : ecategoryₗₑᵥ ℓₒ₂ ℓₐ₂ ℓ~₂}
                                  (F : efunctorₗₑᵥ ℂ 𝔻)
                                  : Set (1ₗₑᵥ ⊔ ecat.ℓₙₒ~ ℂ ⊔ ecat.ℓₐₗₗ 𝔻)
                                  where
  private module 𝔻 = ecat 𝔻
  open solution-set-condition-defs F
  field
    pf : (Y : 𝔻.Obj) → solution-set-on Y
  private module tmp (Y : 𝔻.Obj) = solution-set-on (pf Y)
  open tmp public


----------------------------------------
-- Proof of the Adjoint Functor Theorem
----------------------------------------

module AFT-proof {ℓₒ₁ : Level}{ℂ : ecategoryₗₑᵥ ℓₒ₁ 0ₗₑᵥ 0ₗₑᵥ}
                 {ℓₒ₂ ℓₐ₂ : Level}{𝔻 : ecategoryₗₑᵥ ℓₒ₂ ℓₐ₂ 0ₗₑᵥ}
                 (limℂ : has-small-limits ℂ)
                 {F : efunctorₗₑᵥ ℂ 𝔻}(limF : preserves-limits F)
                 (solset : has-solution-set-condition F)
                 where
  private
    module ℂ where
      open ecat ℂ public
      open small-limit-defs ℂ public
      open small-limit-props ℂ public
      open has-small-products (lim→prod limℂ) using (prd-of) public
      --open has-small-limits limℂ using (lim-of) public
    module 𝔻 where
      open ecat 𝔻 public
      open small-limit-defs 𝔻 public
    module F where
      open efunctor-aux F public
      open preserves-limits limF public
      open preserves-products (pres-lim→pres-prd limF) public
      module ssc = has-solution-set-condition solset
    module 𝔻↓F (Y : 𝔻.Obj) where
      open ecat (Y ₒ↓ F) public
      open slice-funct-ecat F Y public
      open initial-defs (Y ₒ↓ F) public
    module wi2i (Y : 𝔻.Obj) = weak-init2init {ℂ = Y ₒ↓ F} (ₒ↓has-limits F Y limℂ limF)
    W : (Y : 𝔻.Obj) → ℂ.product-of (F.ssc.obs Y)
    W Y = ℂ.prd-of (F.ssc.obs Y)
    module W (Y : 𝔻.Obj) = ℂ.product-of (W Y)
    module FW (Y : 𝔻.Obj) = 𝔻.product-of (F.pres-prdof (W Y))
    ssc-span : (Y : 𝔻.Obj) → Span/.Obj 𝔻 (λ i → F.ₒ (F.ssc.obs Y i))
    ssc-span Y = record
      { L = Y
      ; ar = F.ssc.ars Y
      }
  -- end private
  
  winit-ob : (Y : 𝔻.Obj) → 𝔻↓F.Obj Y
  winit-ob Y = record
    { R = W.Vx Y
    ; ar = FW.unv.ar Y (ssc-span Y)
    }
  private module wo (Y : 𝔻.Obj) = 𝔻↓F.ₒ Y (winit-ob Y)
    
  winit-winit : (Y : 𝔻.Obj) → 𝔻↓F.is-weak-initial Y (winit-ob Y)
  winit-winit Y = record
    { ar = ar
    }
    where ar : (a : 𝔻↓F.Obj Y) → || 𝔻↓F.Hom Y (winit-ob Y) a ||
          ar a = record
            { arR = F.ssc.unv.ar Y a.ar ℂ.∘ W.π Y (F.ssc.unv.idx Y a.ar)
            ; tr = ~proof
                 F.ₐ (F.ssc.unv.ar Y a.ar ℂ.∘ W.π Y (F.ssc.unv.idx Y a.ar)) 𝔻.∘ wo.ar Y
                                   ~[ ∘e r F.∘ax-rfˢ ⊙ assˢ ] /
                 F.ₐ (F.ssc.unv.ar Y a.ar) 𝔻.∘ FW.π Y (F.ssc.unv.idx Y a.ar) 𝔻.∘ wo.ar Y
                                   ~[ ∘e (FW.unv.tr Y (ssc-span Y) (F.ssc.unv.idx Y a.ar)) r ] /
                 F.ₐ (F.ssc.unv.ar Y a.ar) 𝔻.∘ F.ssc.ars Y (F.ssc.unv.idx Y a.ar)
                                   ~[ F.ssc.unv.tr Y a.ar ]∎
                 a.ar ∎
            }
            where module a = 𝔻↓F.ₒ Y a
                  open ecategory-aux-only 𝔻

  has-init-ob : (Y : 𝔻.Obj) → 𝔻↓F.Obj Y
  has-init-ob Y = wi2i.ob Y {winit-ob Y} (winit-winit Y)

  has-init-pf : (Y : 𝔻.Obj) → 𝔻↓F.is-initial Y (has-init-ob Y)
  has-init-pf Y = wi2i.is-init Y {winit-ob Y} (winit-winit Y)


  module left-adjoint-from-initial {inob : (Y : 𝔻.Obj) → 𝔻↓F.Obj Y}
                                   (isin : (Y : 𝔻.Obj) → 𝔻↓F.is-initial Y (inob Y))
                                   where
    private
      module init (Y : 𝔻.Obj) where
        open 𝔻↓F.ₒ Y (inob Y) public
        open 𝔻↓F.is-initial Y (isin Y) public
      module pb {A B : 𝔻.Obj}(g : || 𝔻.Hom A B ||) = efctr (ₒ↓pullback F g)

    module Larr {A B : 𝔻.Obj}(g : || 𝔻.Hom A B ||) where
      g*IB : 𝔻↓F.Obj A
      g*IB = pb.ₒ g (inob B)
      module g*IB = 𝔻↓F.ₒ A g*IB
      ver : || 𝔻↓F.Hom A (inob A) g*IB ||
      ver = init.ø A g*IB
      module ver = 𝔻↓F.ₐ A ver
      Lg : || ℂ.Hom (init.R A) (init.R B) ||
      Lg = ver.arR
    -- end Larr
    L : efunctorₗₑᵥ 𝔻 ℂ
    L = record
      { FObj = init.R
      ; FHom = Larr.Lg
      ; isF = record
            { ext = λ {A} {B} {f} {f'} eq → init.øuq A (ext-aux eq)
            ; id = λ {A} → init.øuq A (id-aux A) ˢ
            ; cmp = λ {A} {B} {C} f g → init.øuq A (cmp-aux f g)
            }
      }
      where ext-aux : {A B : 𝔻.Obj}{f f' : || 𝔻.Hom A B ||}
                         → f 𝔻.~ f' → || 𝔻↓F.Hom A (inob A) (Larr.g*IB f') ||
            ext-aux {A} {B} {f} {f'} eq = record
              { arR = Larr.Lg f
              ; tr = ~proof    F.ₐ (Larr.Lg f) 𝔻.∘ init.ar A    ~[ Larr.ver.tr f ] /
                               init.ar B 𝔻.∘ f                  ~[ ∘e eq r ]∎
                               init.ar B 𝔻.∘ f' ∎
              }
              where open ecategory-aux-only 𝔻
            id-aux : (A : 𝔻.Obj) → || 𝔻↓F.Hom A (inob A) (Larr.g*IB (𝔻.idar A)) ||
            id-aux A = record
              { arR = ℂ.idar (init.R A)
              ; tr = / F.ₐ (ℂ.idar (init.R A)) 𝔻.∘ init.ar A       ~[ lidgg ridˢ F.id ]∎
                       init.ar A 𝔻.∘ 𝔻.idar A ∎
              }
              where open ecategory-aux-only 𝔻
            cmp-aux : {A B C : 𝔻.Obj}(f : || 𝔻.Hom A B ||)(g : || 𝔻.Hom B C ||)
                         → || 𝔻↓F.Hom A (inob A) (Larr.g*IB (g 𝔻.∘ f)) ||
            cmp-aux {A} {B} {C} f g = record
              { arR = Larr.ver.arR g ℂ.∘ Larr.Lg f
              ; tr = ~proof
                   F.ₐ (Larr.ver.arR g ℂ.∘ Larr.Lg f) 𝔻.∘ init.ar A        ~[ ∘e r F.∘ax-rfˢ ⊙ assˢ ] /
                   F.ₐ (Larr.ver.arR g) 𝔻.∘ F.ₐ (Larr.Lg f) 𝔻.∘ init.ar A  ~[ ∘e (Larr.ver.tr f) r ] /
                   F.ₐ (Larr.ver.arR g) 𝔻.∘ init.ar B 𝔻.∘ f         ~[ ass ⊙ ∘e r (Larr.ver.tr g) ] /
                   (init.ar C 𝔻.∘ g) 𝔻.∘ f                                 ~[ assˢ ]∎
                   Larr.g*IB.ar (g 𝔻.∘ f) ∎
              }
              where open ecategory-aux-only 𝔻
            open ecategory-aux-only ℂ using (_ˢ)

    open adjunction-as-universal-props L F
    
    ηnt : natural-transformation IdF (F ○ L)
    ηnt = record
      { fnc = λ {A} → init.ar A
      ; nat = λ f → Larr.ver.tr f ˢ
      }
      where open ecategory-aux-only 𝔻 using (_ˢ)
    ηin : (A : 𝔻.Obj) → 𝔻↓F.is-initial A (RLnt2sl ηnt A)
    ηin = isin
    
    isladj : L ⊣ F
    isladj = unvη→adj ηnt ηin
  -- end left-adjoint-from-initial
-- end AFT-proof


AFT : {ℓₒ₁ : Level}{ℂ : ecategoryₗₑᵥ ℓₒ₁ 0ₗₑᵥ 0ₗₑᵥ}
      {ℓₒ₂ ℓₐ : Level}{𝔻 : ecategoryₗₑᵥ ℓₒ₂ ℓₐ 0ₗₑᵥ}{F : efunctorₗₑᵥ ℂ 𝔻}
        → has-small-limits ℂ → preserves-limits F → has-solution-set-condition F
          → is-right-adjoint F
AFT limℂ limF sscF = record
  { left = left.L
  ; adj = left.isladj
  }
  where open AFT-proof limℂ limF sscF
        module left = left-adjoint-from-initial has-init-pf

