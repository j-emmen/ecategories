-- disable the K axiom:

{-# OPTIONS --without-K #-}

-- Agda version 2.5.4.1

module ecats.finite-limits.not.bin-weak-product where

open import ecats.basic-defs.ecat-def&not
open import ecats.basic-defs.commut-shapes
open import ecats.finite-limits.defs.bin-weak-product
open import ecats.finite-limits.defs.bin-product


  -- notation and basic properties of weak product spans

module bin-wproduct-spans (ℂ : ecategory) where
  open ecategory-aux ℂ
  open comm-shapes ℂ
  open bin-wproduct-defs ℂ


  module wprod-Δ {A : Obj} (wprdof : wproduct-of A A) where
  --{sp : span/ A A} (isprd : is-product (mkspan-c sp)) where
    open wproduct-of wprdof
    --open bin-product (mk× isprd)

    wΔ : || Hom A O12 ||
    wΔ = w< idar A , idar A >

  -- end wprod-Δ


  module bin-wproduct-not-only (wprdsp : bin-wproduct) where
    open bin-wproduct wprdsp --renaming (w×tr₁ to w×tr₁r; w×tr₂ to w×tr₂r)
    --renaming (wπ₁ to wπ₁ₛ; wπ₂ to wπ₂ₛ; <_,_> to <_,_>ₛ; w×tr₁ to w×tr₁ₛ; w×tr₂ to w×tr₂ₛ; w×uq to w×uqₛ)

    w×of : wproduct-of O1 O2
    w×of = mkw×of iswprd

  -- first triangle

    w×tr₁g : {C : Obj} → {f f' : || Hom C O1 ||} → {g : || Hom C O2 ||} → f ~ f'
                     → wπ₁ ∘ w< f , g > ~ f'
    w×tr₁g pf = w×tr₁ ⊙ pf

    w×tr₁ˢ :  {C : Obj} → {f : || Hom C O1 ||} → {g : || Hom C O2 ||}
                 → f ~ wπ₁ ∘ w< f , g >
    w×tr₁ˢ = w×tr₁ ˢ

    w×tr₁gˢ : {C : Obj} → {f f' : || Hom C O1 ||} → {g : || Hom C O2 ||} → f ~ f'
                     → f' ~ wπ₁ ∘ w< f , g >
    w×tr₁gˢ pf = w×tr₁g pf ˢ

  -- second triangle

    w×tr₂g : {C : Obj} → {f : || Hom C O1 ||} → {g g' : || Hom C O2 ||}
                   → g ~ g'
                     → wπ₂ ∘ w< f , g > ~ g'
    w×tr₂g pf = w×tr₂ ⊙ pf

    w×tr₂ˢ :  {C : Obj} → {f : || Hom C O1 ||} → {g : || Hom C O2 ||}
                 → g ~ wπ₂ ∘ w< f , g >
    w×tr₂ˢ = w×tr₂ ˢ

    w×tr₂gˢ : {C : Obj} → {f : || Hom C O1 ||} → {g g' : || Hom C O2 ||}
                   → g ~ g' → g' ~ wπ₂ ∘ w< f , g >
    w×tr₂gˢ pf = w×tr₂g pf ˢ

  -- end bin-wproduct-not-only


  module bin-wproduct-not (prdsp : bin-wproduct) where
    open bin-wproduct prdsp public
    open bin-wproduct-not-only prdsp public
  -- end bin-wproduct-not

  module wproduct-of-not {O1 O2 : Obj} (wprdof : wproduct-of O1 O2) where
    open wproduct-of wprdof public
    open bin-wproduct-not-only wprdsp public
  -- end wproduct-of-not
  

  module w×ₐdef (prdsp prdsp' : bin-wproduct) where
    private
      module w× = bin-wproduct-not prdsp
      module w×' = bin-wproduct-not prdsp'

    infixr 6 _w×ₐ_    
    _w×ₐ_ : || Hom w×'.O1 w×.O1 || → || Hom w×'.O2 w×.O2 || →  || Hom w×'.O12 w×.O12 ||
    f w×ₐ g = w×.w< f ∘ w×'.wπ₁ , g ∘ w×'.wπ₂ >

  -- end w×ₐdef

-- end bin-wproduct-spans






-- notation and basic properties of chosen weak products

module bin-wproducts-aux {ℂ : ecategory} (prod : has-bin-weak-products ℂ) where
  open ecategory-aux ℂ
  open bin-wproduct-defs ℂ
  open bin-wproduct-spans ℂ
  open has-bin-weak-products prod public

  wΔ_ : (A : Obj) → || Hom A (A w× A) ||
  wΔ A = wΔ
      where open wprod-Δ (wprd-of A A) --w×isprd

  module w×ₐᶜdef {A B A' B' : Obj} = w×ₐdef (wprdsp {B} {B'}) (wprdsp {A} {A'})
  open w×ₐᶜdef public

  module w×ᶜnot-only {A B : Obj} = bin-wproduct-not-only (wprdsp {A} {B})
  --module w×ᶜnot {A B : Obj} = bin-wproduct-not (wprdsp {A} {B})
  open w×ᶜnot-only public hiding (w×of)

-- end module bin-wproducts-aux                                                 
