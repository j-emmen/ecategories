-- disable the K axiom:

{-# OPTIONS --without-K #-}

-- Agda version 2.5.4.1

module ecats.finite-limits.not.bin-product where

open import ecats.basic-defs.ecat-def&not
open import ecats.basic-defs.commut-shapes
open import ecats.finite-limits.defs.bin-product



  -- notation and basic properties of product spans

module bin-product-spans (ℂ : ecategory) where
  open ecategory-aux ℂ
  open comm-shapes ℂ
  open bin-product-defs ℂ


  module prod-Δ {A : Obj} (prdof : product-of A A) where --{sp : span/ A A} (isprd : is-product (mkspan-c sp)) where
    open product-of prdof
    --open bin-product (mk× isprd)

    Δ : || Hom A O12 ||
    Δ = < idar A , idar A >

-- end prod-diag


  module bin-product-not-only (prdsp : bin-product) where
    open bin-product prdsp --renaming (×tr₁ to ×tr₁r; ×tr₂ to ×tr₂r)
    --renaming (π₁ to π₁ₛ; π₂ to π₂ₛ; <_,_> to <_,_>ₛ; ×tr₁ to ×tr₁ₛ; ×tr₂ to ×tr₂ₛ; ×uq to ×uqₛ)

    ×of : product-of O1 O2
    ×of = mk×of ×isprd

  -- first triangle

    ×tr₁g : {C : Obj} → {f f' : || Hom C O1 ||} → {g : || Hom C O2 ||} → f ~ f'
                     → π₁ ∘ < f , g > ~ f'
    ×tr₁g pf = ×tr₁ ⊙ pf

    ×tr₁ˢ :  {C : Obj} → {f : || Hom C O1 ||} → {g : || Hom C O2 ||}
                 → f ~ π₁ ∘ < f , g >
    ×tr₁ˢ = ×tr₁ ˢ

    ×tr₁gˢ : {C : Obj} → {f f' : || Hom C O1 ||} → {g : || Hom C O2 ||} → f ~ f'
                     → f' ~ π₁ ∘ < f , g >
    ×tr₁gˢ pf = ×tr₁g pf ˢ

  -- second triangle

    ×tr₂g : {C : Obj} → {f : || Hom C O1 ||} → {g g' : || Hom C O2 ||}
                   → g ~ g'
                     → π₂ ∘ < f , g > ~ g'
    ×tr₂g pf = ×tr₂ ⊙ pf

    ×tr₂ˢ :  {C : Obj} → {f : || Hom C O1 ||} → {g : || Hom C O2 ||}
                 → g ~ π₂ ∘ < f , g >
    ×tr₂ˢ = ×tr₂ ˢ

    ×tr₂gˢ : {C : Obj} → {f : || Hom C O1 ||} → {g g' : || Hom C O2 ||}
                   → g ~ g' → g' ~ π₂ ∘ < f , g >
    ×tr₂gˢ pf = ×tr₂g pf ˢ

    -- universal arrow

    -- ×uq<>
    ar~<> : {C : Obj} → {f : || Hom C O1 ||} → {g : || Hom C O2 ||} → {h : || Hom C O12 ||}
                  → π₁ ∘ h ~ f → π₂ ∘ h ~ g → h ~ < f , g >
    ar~<> pff pfg = ×uq (pff ⊙ ×tr₁ˢ) (pfg ⊙ ×tr₂ˢ)

    ar~<>ˢ : {C : Obj} → {f : || Hom C O1 ||} → {g : || Hom C O2 ||} → {h : || Hom C O12 ||}
                  → π₁ ∘ h ~ f → π₂ ∘ h ~ g → < f , g > ~ h
    ar~<>ˢ pff pfg = (ar~<> pff pfg) ˢ
    
    <π>~id : < π₁ , π₂ > ~ idar O12
    <π>~id = ar~<>ˢ rid rid

    -- <>uq<>
    <>~<> : {C : Obj} → {f f' : || Hom C O1 ||} → {g g' : || Hom C O2 ||}
                  → f ~ f' → g ~ g' → < f , g > ~ < f' , g' >
    <>~<> pff pfg = ar~<> (×tr₁ ⊙ pff) (×tr₂ ⊙ pfg)

    -- distribuitivity over composition

    <>dist : {C D : Obj} → {f : || Hom C O1 ||} → {g : || Hom C O2 ||} → (h : || Hom D C ||)
                 → < f , g > ∘ h ~ < f ∘ h , g ∘ h >
    <>dist h = ar~<> (ass ⊙ ∘e r ×tr₁) (ass ⊙ ∘e r ×tr₂)

    <>distˢ : {C D : Obj} → {f : || Hom C O1 ||} → {g : || Hom C O2 ||} → (h : || Hom D C ||)
               → < f ∘ h , g ∘ h > ~ < f , g > ∘ h
    <>distˢ h = <>dist h ˢ 

    -- <>dist-gen
    <>ar~ar : {C D : Obj} → {f₁ : || Hom C O1 ||} → {f₂ : || Hom C O2 ||} → {h : || Hom D C ||}
                 → {g : || Hom D O12 ||} → π₁ ∘ g ~ f₁ ∘ h → π₂ ∘ g ~ f₂ ∘ h
                     → < f₁ , f₂ > ∘ h ~ g
    <>ar~ar pf₁ pf₂ = <>dist _ ⊙ ar~<>ˢ pf₁ pf₂

    <>ar~arˢ : {C D : Obj} → {f₁ : || Hom C O1 ||} → {f₂ : || Hom C O2 ||} → {h : || Hom D C ||}
                 → {g : || Hom D O12 ||} → π₁ ∘ g ~ f₁ ∘ h → π₂ ∘ g ~ f₂ ∘ h
                     → g ~ < f₁ , f₂ > ∘ h
    <>ar~arˢ pf₁ pf₂ = <>ar~ar pf₁ pf₂ ˢ

    -- <>dist<>
    <>ar~<> : {C D : Obj} → {f₁ : || Hom C O1 ||} → {f₂ : || Hom C O2 ||} → {h : || Hom D C ||}
                 → {g₁ : || Hom D O1 ||} → {g₂ : || Hom D O2 ||} → f₁ ∘ h ~ g₁ → f₂ ∘ h ~ g₂
                     → < f₁ , f₂ > ∘ h ~ < g₁ , g₂ >
    <>ar~<> pf₁ pf₂ = (<>dist _) ⊙ <>~<> pf₁ pf₂

    <>ar~<>ˢ : {C D : Obj} → {f₁ : || Hom C O1 ||} → {f₂ : || Hom C O2 ||} → {h : || Hom D C ||}
                 → {g₁ : || Hom D O1 ||} → {g₂ : || Hom D O2 ||} → f₁ ∘ h ~ g₁ → f₂ ∘ h ~ g₂
                     → < g₁ , g₂ > ~ < f₁ , f₂ > ∘ h
    <>ar~<>ˢ pf₁ pf₂ = <>ar~<> pf₁ pf₂ ˢ

    <>ar~<>ar : {C D E : Obj} {f₁ : || Hom C O1 ||} {f₂ : || Hom C O2 ||} {h : || Hom E C ||}
                {g₁ : || Hom D O1 ||} {g₂ : || Hom D O2 ||} {h' : || Hom E D ||}
                  → f₁ ∘ h ~ g₁ ∘ h' → f₂ ∘ h ~ g₂ ∘ h' → < f₁ , f₂ > ∘ h ~ < g₁ , g₂ > ∘ h'
    <>ar~<>ar pf₁ pf₂ = <>ar~<> pf₁ pf₂ ⊙ <>distˢ _

  -- end bin-product-not-only


  module bin-product-not (prdsp : bin-product) where
    open bin-product prdsp public
    open bin-product-not-only prdsp public
  -- end bin-product-not

  module product-of-not {O1 O2 : Obj} (prdof : product-of O1 O2) where
    open product-of prdof public
    open bin-product-not-only prdsp public
  -- end product-of-not
  

  module ×ₐdef (prdsp prdsp' : bin-product) where
    private
      module × = bin-product-not prdsp
      module ×' = bin-product-not prdsp'
    infixr 6 _×ₐ_    
    _×ₐ_ : || Hom ×'.O1 ×.O1 || → || Hom ×'.O2 ×.O2 || →  || Hom ×'.O12 ×.O12 ||
    f ×ₐ g = ×.< f ∘ ×'.π₁ , g ∘ ×'.π₂ >
  -- end ×ₐdef

  module ×ₐnot1-only (prdsp₁ : bin-product) where
    private
      module ×₁ = bin-product-not prdsp₁
      infixr 6 _×ₐ₁₁_
      _×ₐ₁₁_ = ×ₐdef._×ₐ_ prdsp₁ prdsp₁

    ×ₐid : {f : || Hom ×₁.O1 ×₁.O1 ||} {g : || Hom ×₁.O2 ×₁.O2 ||}
              → f ~ idar ×₁.O1 → g ~ idar ×₁.O2
                → f ×ₐ₁₁ g ~ idar ×₁.O12
    ×ₐid pff pfg = ×₁.ar~<>ˢ (lidggˢ rid pff) (lidggˢ rid pfg)
    
    ×ₐidˢ : {f : || Hom ×₁.O1 ×₁.O1 ||} {g : || Hom ×₁.O2 ×₁.O2 ||}
            → f ~ idar ×₁.O1 → g ~ idar ×₁.O2
              → idar ×₁.O12 ~ f ×ₐ₁₁ g
    ×ₐidˢ pff pfg = ×ₐid pff pfg ˢ

  -- end ×ₐnot1-only

  module ×ₐnot2-only (prdsp₁ prdsp₂ : bin-product) where
    private
      module ×₁ = bin-product-not prdsp₁
      module ×₂ = bin-product-not prdsp₂
      infixr 6 _×ₐ₂₁_
      _×ₐ₂₁_ = ×ₐdef._×ₐ_ prdsp₁ prdsp₂
    
    ×ₐe : {f f' : || Hom ×₂.O1 ×₁.O1 ||} {g g' : || Hom ×₂.O2 ×₁.O2 ||}
              → f ~ f' → g ~ g' → f ×ₐ₂₁ g ~ f' ×ₐ₂₁ g'
    ×ₐe pff pfg = ×₁.<>~<> (∘e r pff) (∘e r pfg)

    -- ×ₐcmp<>gen
    ×ₐ<>~ar : {f₂₁ : || Hom ×₂.O1 ×₁.O1 ||} {g₂₁ : || Hom ×₂.O2 ×₁.O2 ||}
              {A : Obj} {hfst : || Hom A ×₂.O1 ||} {hsnd : || Hom A ×₂.O2 ||} {k : || Hom A ×₁.O12 ||}
                → ×₁.π₁ ∘ k ~ f₂₁ ∘ hfst → ×₁.π₂ ∘ k ~ g₂₁ ∘ hsnd
                  → (f₂₁ ×ₐ₂₁ g₂₁) ∘ ×₂.< hfst , hsnd > ~ k
    ×ₐ<>~ar {hfst = hfst} {hsnd} pffst pfsnd = ×₁.<>ar~ar (pffst ⊙ ∘e (×₂.×tr₁ˢ {g = hsnd}) r ⊙ ass)
                                                          (pfsnd ⊙ ∘e (×₂.×tr₂ˢ {f = hfst}) r ⊙ ass)

    ×ₐ<>~arˢ : {f₂₁ : || Hom ×₂.O1 ×₁.O1 ||} {g₂₁ : || Hom ×₂.O2 ×₁.O2 ||}
               {A : Obj} {hfst : || Hom A ×₂.O1 ||} {hsnd : || Hom A ×₂.O2 ||} {k : || Hom A ×₁.O12 ||}
                 → ×₁.π₁ ∘ k ~ f₂₁ ∘ hfst → ×₁.π₂ ∘ k ~ g₂₁ ∘ hsnd
                   → k ~ (f₂₁ ×ₐ₂₁ g₂₁) ∘ ×₂.< hfst , hsnd >
    ×ₐ<>~arˢ pffst pfsnd = ×ₐ<>~ar pffst pfsnd ˢ

    -- ×ₐcmp<>
    ×ₐ<>~<> : {f₂₁ : || Hom ×₂.O1 ×₁.O1 ||} {g₂₁ : || Hom ×₂.O2 ×₁.O2 ||}
                {A : Obj} {hfst : || Hom A ×₂.O1 ||} {hsnd : || Hom A ×₂.O2 ||}
                {kfst : || Hom A ×₁.O1 ||} {ksnd : || Hom A ×₁.O2 ||}
                 → f₂₁ ∘ hfst ~ kfst → g₂₁ ∘ hsnd ~ ksnd
                   → (f₂₁ ×ₐ₂₁ g₂₁) ∘ ×₂.< hfst , hsnd > ~ ×₁.< kfst , ksnd >
    ×ₐ<>~<> pffst pfsnd = ×ₐ<>~ar (×₁.×tr₁ ⊙ pffst ˢ) (×₁.×tr₂ ⊙ pfsnd ˢ)

    ×ₐ<>~<>ˢ : {f₂₁ : || Hom ×₂.O1 ×₁.O1 ||} {g₂₁ : || Hom ×₂.O2 ×₁.O2 ||}
                {A : Obj} {hfst : || Hom A ×₂.O1 ||} {hsnd : || Hom A ×₂.O2 ||}
                {kfst : || Hom A ×₁.O1 ||} {ksnd : || Hom A ×₁.O2 ||}
                 → f₂₁ ∘ hfst ~ kfst → g₂₁ ∘ hsnd ~ ksnd
                   → ×₁.< kfst , ksnd > ~ (f₂₁ ×ₐ₂₁ g₂₁) ∘ ×₂.< hfst , hsnd >
    ×ₐ<>~<>ˢ pffst pfsnd = ×ₐ<>~<> pffst pfsnd ˢ

    ×ₐ<>~<>ar :  {f₂₁ : || Hom ×₂.O1 ×₁.O1 ||} {g₂₁ : || Hom ×₂.O2 ×₁.O2 ||}
                 {A : Obj} {hfst : || Hom A ×₂.O1 ||} {hsnd : || Hom A ×₂.O2 ||}
                 {B : Obj} {kfst : || Hom B ×₁.O1 ||} {ksnd : || Hom B ×₁.O2 ||} {l : || Hom A B ||}
                   → f₂₁ ∘ hfst ~ kfst ∘ l → g₂₁ ∘ hsnd ~ ksnd ∘ l
                     → (f₂₁ ×ₐ₂₁ g₂₁) ∘ ×₂.< hfst , hsnd > ~ ×₁.< kfst , ksnd > ∘ l
    ×ₐ<>~<>ar {l = l} pffst pfsnd = ×ₐ<>~<> pffst pfsnd ⊙ ×₁.<>distˢ l
  -- end ×ₐnot2-only

  

  module ×ₐnot3-only (prdsp₁ prdsp₂ prdsp₃ : bin-product) where
    private
      module ×₁ = bin-product-not prdsp₁
      module ×₂ = bin-product-not prdsp₂
      module ×₃ = bin-product-not prdsp₃
      infixr 6 _×ₐ₂₁_ _×ₐ₃₂_ _×ₐ₃₁_
      _×ₐ₂₁_ = ×ₐdef._×ₐ_ prdsp₁ prdsp₂
      _×ₐ₃₂_ = ×ₐdef._×ₐ_ prdsp₂ prdsp₃
      _×ₐ₃₁_ = ×ₐdef._×ₐ_ prdsp₁ prdsp₃

    -- ×ₐcmp
    ×ₐcmp : (f₂₁ : || Hom ×₂.O1 ×₁.O1 ||) (g₂₁ : || Hom ×₂.O2 ×₁.O2 ||)
            (f₃₂ : || Hom ×₃.O1 ×₂.O1 ||) (g₃₂ : || Hom ×₃.O2 ×₂.O2 ||)
              →  (f₂₁ ×ₐ₂₁ g₂₁) ∘ (f₃₂ ×ₐ₃₂ g₃₂) ~ (f₂₁ ∘ f₃₂) ×ₐ₃₁ (g₂₁ ∘ g₃₂)
    ×ₐcmp f₂₁ g₂₁ f₃₂ g₃₂ = ×₁.ar~<> (ass ⊙ ( ∘e r ×₁.×tr₁ ⊙ (assˢ ⊙ (∘e ×₂.×tr₁ r ⊙ ass)) ))
                                     (ass ⊙ ( ∘e r ×₁.×tr₂ ⊙ (assˢ ⊙ (∘e ×₂.×tr₂ r ⊙ ass)) ))

    ×ₐcmpˢ : (f₂₁ : || Hom ×₂.O1 ×₁.O1 ||) (g₂₁ : || Hom ×₂.O2 ×₁.O2 ||)
              (f₃₂ : || Hom ×₃.O1 ×₂.O1 ||) (g₃₂ : || Hom ×₃.O2 ×₂.O2 ||)
                →  (f₂₁ ∘ f₃₂) ×ₐ₃₁ (g₂₁ ∘ g₃₂) ~ (f₂₁ ×ₐ₂₁ g₂₁) ∘ (f₃₂ ×ₐ₃₂ g₃₂)
    ×ₐcmpˢ f₂₁ g₂₁ f₃₂ g₃₂ = ×ₐcmp f₂₁ g₂₁ f₃₂ g₃₂ ˢ

    -- ×ₐcmpgg
    ×ₐ×ₐ~ar : {f₂₁ : || Hom ×₂.O1 ×₁.O1 ||} {g₂₁ : || Hom ×₂.O2 ×₁.O2 ||}
            {f₃₂ : || Hom ×₃.O1 ×₂.O1 ||} {g₃₂ : || Hom ×₃.O2 ×₂.O2 ||}
            {h : || Hom ×₃.O12 ×₁.O12 ||}
               → ×₁.π₁ ∘ h ~ (f₂₁ ∘ f₃₂) ∘ ×₃.π₁ → ×₁.π₂ ∘ h ~ (g₂₁ ∘ g₃₂) ∘ ×₃.π₂
                 → (f₂₁ ×ₐ₂₁ g₂₁) ∘ (f₃₂ ×ₐ₃₂ g₃₂) ~ h
    ×ₐ×ₐ~ar {f₂₁ = f₂₁} {g₂₁} {f₃₂} {g₃₂} {h} pffst pfsnd = ×₁.×uq (ass ⊙ ∘e r ×₁.×tr₁ ⊙ assˢ ⊙ ∘e ×₂.×tr₁ r ⊙ ass ⊙ pffst ˢ)
                                                                 (ass ⊙ ∘e r ×₁.×tr₂ ⊙ assˢ ⊙ ∘e ×₂.×tr₂ r ⊙ ass ⊙ pfsnd ˢ)

    ×ₐ×ₐ~arˢ : {f₂₁ : || Hom ×₂.O1 ×₁.O1 ||} {g₂₁ : || Hom ×₂.O2 ×₁.O2 ||}
              {f₃₂ : || Hom ×₃.O1 ×₂.O1 ||} {g₃₂ : || Hom ×₃.O2 ×₂.O2 ||}
              {h : || Hom ×₃.O12 ×₁.O12 ||}
                 → ×₁.π₁ ∘ h ~ (f₂₁ ∘ f₃₂) ∘ ×₃.π₁ → ×₁.π₂ ∘ h ~ (g₂₁ ∘ g₃₂) ∘ ×₃.π₂
                   → h ~ (f₂₁ ×ₐ₂₁ g₂₁) ∘ (f₃₂ ×ₐ₃₂ g₃₂)
    ×ₐ×ₐ~arˢ pffst pfsnd = ×ₐ×ₐ~ar pffst pfsnd ˢ

    -- ×ₐcmpgen
    ×ₐ×ₐ~×ₐ : {f₂₁ : || Hom ×₂.O1 ×₁.O1 ||} {g₂₁ : || Hom ×₂.O2 ×₁.O2 ||}
              {f₃₂ : || Hom ×₃.O1 ×₂.O1 ||} {g₃₂ : || Hom ×₃.O2 ×₂.O2 ||}
              {f₃₁ : || Hom ×₃.O1 ×₁.O1 ||} {g₃₁ : || Hom ×₃.O2 ×₁.O2 ||}
                  → f₂₁ ∘ f₃₂ ~ f₃₁ → g₂₁ ∘ g₃₂ ~ g₃₁ → (f₂₁ ×ₐ₂₁ g₂₁) ∘ (f₃₂ ×ₐ₃₂ g₃₂) ~ f₃₁ ×ₐ₃₁ g₃₁
    ×ₐ×ₐ~×ₐ pffst pfsnd = ×ₐ×ₐ~ar (×₁.×tr₁ ⊙ ∘e r (pffst ˢ)) (×₁.×tr₂ ⊙ ∘e r (pfsnd ˢ))
                                                                  --×ₐcmprr f₂₁ g₂₁ f₃₂ g₃₂ ⊙ ×₁.<>uq<> (∘e r pff) (∘e r pfg)

    ×ₐ×ₐ~×ₐˢ : {f₂₁ : || Hom ×₂.O1 ×₁.O1 ||} {g₂₁ : || Hom ×₂.O2 ×₁.O2 ||}
              {f₃₂ : || Hom ×₃.O1 ×₂.O1 ||} {g₃₂ : || Hom ×₃.O2 ×₂.O2 ||}
              {f₃₁ : || Hom ×₃.O1 ×₁.O1 ||} {g₃₁ : || Hom ×₃.O2 ×₁.O2 ||}
                  → f₂₁ ∘ f₃₂ ~ f₃₁ → g₂₁ ∘ g₃₂ ~ g₃₁ → f₃₁ ×ₐ₃₁ g₃₁ ~ (f₂₁ ×ₐ₂₁ g₂₁) ∘ (f₃₂ ×ₐ₃₂ g₃₂)
    ×ₐ×ₐ~×ₐˢ pffst pfsnd = ×ₐ×ₐ~×ₐ pffst pfsnd ˢ
  -- end ×ₐnot3-only
  

  module ×ₐnot4-only (prdsp₁ prdsp₂ prdsp₃ prdsp₄ : bin-product) where
    private
      module ×₁ = bin-product-not prdsp₁
      module ×₂ = bin-product-not prdsp₂
      module ×₃ = bin-product-not prdsp₃
      module ×₄ = bin-product-not prdsp₄
      infixr 6 _×ₐ₂₁_ _×ₐ₃₂_ _×ₐ₃₁_ _×ₐ₄₁_ _×ₐ₃₄_
      _×ₐ₂₁_ = ×ₐdef._×ₐ_ prdsp₁ prdsp₂
      _×ₐ₃₂_ = ×ₐdef._×ₐ_ prdsp₂ prdsp₃
      _×ₐ₃₁_ = ×ₐdef._×ₐ_ prdsp₁ prdsp₃
      _×ₐ₄₁_ = ×ₐdef._×ₐ_ prdsp₁ prdsp₄
      _×ₐ₃₄_ = ×ₐdef._×ₐ_ prdsp₄  prdsp₃

    ×ₐ×ₐ~×ₐ×ₐ : {f₂₁ : || Hom ×₂.O1 ×₁.O1 ||} {g₂₁ : || Hom ×₂.O2 ×₁.O2 ||}
               {f₃₂ : || Hom ×₃.O1 ×₂.O1 ||} {g₃₂ : || Hom ×₃.O2 ×₂.O2 ||}
               {f₄₁ : || Hom ×₄.O1 ×₁.O1 ||} {g₄₁ : || Hom ×₄.O2 ×₁.O2 ||}
               {f₃₄ : || Hom ×₃.O1 ×₄.O1 ||} {g₃₄ : || Hom ×₃.O2 ×₄.O2 ||}
                   → f₂₁ ∘ f₃₂ ~ f₄₁ ∘ f₃₄ → g₂₁ ∘ g₃₂ ~ g₄₁ ∘ g₃₄
                     → (f₂₁ ×ₐ₂₁ g₂₁) ∘ (f₃₂ ×ₐ₃₂ g₃₂) ~ (f₄₁ ×ₐ₄₁ g₄₁) ∘ (f₃₄ ×ₐ₃₄ g₃₄)
    ×ₐ×ₐ~×ₐ×ₐ pffst pfsnd = ×ₐ<>~<>ar (ass ⊙ ∘e r pffst ⊙ assˢ ⊙ ∘e (×₄.×tr₁ˢ {g = _ ∘ ×₃.π₂}) r ⊙ ass)
                                     (ass ⊙ ∘e r pfsnd ⊙ assˢ ⊙ ∘e (×₄.×tr₂ˢ {f = _ ∘ ×₃.π₁}) r ⊙ ass)
                         where open ×ₐnot2-only prdsp₁ prdsp₂
  -- end ×ₐnot4-only


  module ×ₐnot (prdsp₁ prdsp₂ : bin-product) where
    open ×ₐdef prdsp₁ prdsp₂ public
    open ×ₐnot2-only prdsp₁ prdsp₂ public
  -- end ×ₐnot

-- end bin-product-spans





-- notation and basic properties of chosen products

module bin-products-aux {ℂ : ecategory} (prod : has-bin-products ℂ) where
  open ecategory-aux ℂ
  open bin-product-defs ℂ
  open bin-product-spans ℂ
  open has-bin-products prod public

  -- notation

  Δ_ : (A : Obj) → || Hom A (A × A) ||
  Δ A = Δ
      where open prod-Δ (prd-of A A) --×isprd

  module ×ₐᶜdef {A B A' B' : Obj} = ×ₐdef (prdsp {B} {B'}) (prdsp {A} {A'})
  open ×ₐᶜdef public

  module ×ᶜnot-only {A B : Obj} = bin-product-not-only (prdsp {A} {B})
  open ×ᶜnot-only public hiding (×of)

  module  ×ₐᶜnot1-only {A₁ B₁ : Obj} = ×ₐnot1-only (prdsp {A₁} {B₁})
  open ×ₐᶜnot1-only public
  
  module  ×ₐᶜnot2-only {A₁ B₁ A₂ B₂ : Obj} = ×ₐnot2-only (prdsp {A₁} {B₁}) (prdsp {A₂} {B₂})
  open ×ₐᶜnot2-only public

  module ×ₐᶜnot3-only {A₁ B₁ A₂ B₂ A₃ B₃ : Obj} = ×ₐnot3-only (prdsp {A₁} {B₁}) (prdsp {A₂} {B₂}) (prdsp {A₃} {B₃})
  open ×ₐᶜnot3-only public

  module ×ₐᶜnot4-only {A₁ B₁ A₂ B₂ A₃ B₃ A₄ B₄ : Obj}
                        = ×ₐnot4-only (prdsp {A₁} {B₁}) (prdsp {A₂} {B₂}) (prdsp {A₃} {B₃}) (prdsp {A₄} {B₄})
  open ×ₐᶜnot4-only public
  
-- end module catproducts-aux                                                 
