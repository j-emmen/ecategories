
{-# OPTIONS --without-K #-}

module ecats.basic-defs.epi&mono where

open import ecats.basic-defs.ecat-def&not
open import ecats.basic-defs.commut-shapes
open import ecats.basic-defs.isomorphism



module epi&mono-defs {ℓₒ ℓₐ ℓ~ : Level}(ℂ : ecategoryₗₑᵥ ℓₒ ℓₐ ℓ~) where
  open ecategory-aux ℂ hiding (ℓₒ; ℓ~)
  open iso-defs ℂ
  open comm-shapes ℂ

  record is-monic {A B : Obj} (f : || Hom A B ||) : Set ℓₐₗₗ where
    -- constructor mkmonic
    field
      mono-pf : {C : Obj} → {g g' : || Hom C A ||} → f ∘ g ~ f ∘ g' → g ~ g'


  record is-epic {A B : Obj} (f : || Hom A B ||) : Set ℓₐₗₗ where
    -- constructor mkepic
    field
      epi-pf : {C : Obj} → {g g' : || Hom B C ||} → g ∘ f ~ g' ∘ f → g ~ g'


  record is-cover {A B : Obj} (f : || Hom A B ||) : Set ℓₐₗₗ where
    -- constructor mkcover
    field
      cov-pf : {C : Obj} → {p : || Hom A C ||} → {m : || Hom C B ||} → m ∘ p ~ f
              → is-monic m → is-iso m


  record is-strong-epi {A B : Obj} (f : || Hom A B ||) : Set ℓₐₗₗ where
    ---- constructor mkis-strepi
    field
      lift :  {C D : Obj} → {up : || Hom A C ||} → {down : || Hom B D ||}
                 → {m : || Hom C D ||} → down ∘ f ~ m ∘ up → is-monic m
                   → || Hom B C ||
      tr-up : {C D : Obj} → {up : || Hom A C ||} → {down : || Hom B D ||}
                 → {m : || Hom C D ||} → (pfc : down ∘ f ~ m ∘ up) → (pfm : is-monic m)
                   → lift pfc pfm ∘ f ~ up
      tr-down : {C D : Obj} → {up : || Hom A C ||} → {down : || Hom B D ||}
                 → {m : || Hom C D ||} → (pfc : down ∘ f ~ m ∘ up) → (pfm : is-monic m)
                   → m ∘ lift pfc pfm ~ down


  record is-coeq {R A Q : Obj} (r₁ r₂ : || Hom R A ||) (q : || Hom A Q ||) : Set ℓₐₗₗ where
    -- constructor mkis-coeq
    field
      eq : q ∘ r₁ ~ q ∘ r₂
      univ : {B : Obj} → (f : || Hom A B ||) → f ∘ r₁ ~ f ∘ r₂
                    → || Hom Q B ||
      univ-eq : {B : Obj} → {f : || Hom A B ||} → (pf : f ∘ r₁ ~ f ∘ r₂)
                       → univ f pf ∘ q ~ f
      uniq : is-epic q
    open is-epic uniq public


  record coeq-of {R A : Obj} (r₁ r₂ : || Hom R A ||) : Set ℓₐₗₗ where
    constructor mkcoeq-of
    field
      {Ob} : Obj
      {ar} : || Hom A Ob ||
      iscoeq : is-coeq r₁ r₂ ar
    open is-coeq iscoeq public


  record is-regular-epi {A B : Obj} (f : || Hom A B ||) : Set ℓₐₗₗ where
    -- constructor mkis-repi
    field
      {relOb} : Obj
      {rel₁} {rel₂} : || Hom relOb A ||
      coeq : is-coeq rel₁ rel₂ f
    open is-coeq coeq public


  record is-split-epi {A B : Obj} (f : || Hom A B ||) : Set (ℓₐ ⊔ ℓ~) where
    -- constructor mkis-splepi
    field
      {rinv} : || Hom B A ||
      rinv-ax : f ∘ rinv ~ idar B


  record is-jointly-monic/ {O1 O2 : Obj} (sp/ : span/ O1 O2) : Set ℓₐₗₗ where
    -- constructor mkis-jm/
    open span/ sp/
    field
      jm-pf : {C : Obj} {h h' : || Hom C O12 ||}
                 → a1 ∘ h ~ a1 ∘ h' → a2 ∘ h ~ a2 ∘ h' → h ~ h'


  record is-jointly-monic (sp : span) : Set ℓₐₗₗ where
    -- constructor mkis-jm
    open span sp using (sp/)
    field
      isjm/ : is-jointly-monic/ sp/
    open is-jointly-monic/ isjm/ public                 


  record _covers_ (X Y : Obj) : Set ℓₐₗₗ where
    field
      ar : || Hom X Y ||
      is-repi : is-regular-epi ar
    open is-regular-epi is-repi public


  record reg-cover-of (X : Obj) : Set ℓₐₗₗ where
    field
      Ob : Obj
      cov : Ob covers X
    open _covers_ cov public

 -- end epi&mono-defs
