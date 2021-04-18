 
-- disable the K axiom:

{-# OPTIONS --without-K #-}

-- Agda version 2.5.4.1

module ecats.functors.defs.left-covering where

open import ecats.basic-defs.ecat-def&not
open import ecats.basic-defs.commut-shapes
open import ecats.basic-defs.epi&mono
open import ecats.finite-limits.defs&not
open import ecats.functors.defs.efunctor-d&n
open import ecats.functors.defs.basic-defs




-- Left covering functors

module left-covering-defs (ℂ 𝔻 : ecategory) where
  private
    module ℂ where
      open ecategory ℂ public
      open comm-shapes ℂ public
      open finite-weak-limits ℂ public
    module 𝔻 where
      open ecategory 𝔻 public
      open comm-shapes 𝔻 public
      open finite-limits 𝔻 public
      open epi&mono-defs 𝔻 public
    module wpbof = ℂ.wpullback-of
    module wpbsq = ℂ.wpullback-sq
    module pbof = 𝔻.pullback-of
    module pbsq = 𝔻.pb-square
    module weqlof = ℂ.wequaliser-of
    module eqlof = 𝔻.equaliser-of
    module wbwof = ℂ.wbow-of
    module bwof = 𝔻.bow-of
    module w×of = ℂ.wproduct-of
    module ×of = 𝔻.product-of


  record is-left-covering-trm (F : efunctor ℂ 𝔻) : Set₁ where
    private
      module F = efunctor F
    field
      trmuniv-is-repi : {X : ℂ.Obj} (iswtrm : ℂ.is-wterminal X) {T : 𝔻.Obj} (istrm : 𝔻.is-terminal T)
                        (cov! : || 𝔻.Hom (F.ₒ X) T ||)
                           → 𝔻.is-regular-epi cov!


  record is-left-covering-prd (F : efunctor ℂ 𝔻) : Set₁ where
    private
      module F = efunctor F
    field
      prduniv-is-repi : {X Y : ℂ.Obj} (wprdof : ℂ.wproduct-of X Y) (prdof : 𝔻.product-of (F.ₒ X) (F.ₒ Y))
                        {covprd : || 𝔻.Hom (F.ₒ (w×of.O12 wprdof)) (×of.O12 prdof) ||}
                          → ×of.π₁ prdof 𝔻.∘ covprd 𝔻.~ F.ₐ (w×of.wπ₁ wprdof) → ×of.π₂ prdof 𝔻.∘ covprd 𝔻.~ F.ₐ (w×of.wπ₂ wprdof)
                            → 𝔻.is-regular-epi covprd


  record is-left-covering-isprd (F : efunctor ℂ 𝔻) : Set₁ where
    private
      module F = efunctor F
    field
      prduniv-is-repi : {X Y P : ℂ.Obj} {p₁ : || ℂ.Hom P X ||} {p₂ : || ℂ.Hom P Y ||}
                        (iswprd : ℂ.is-wproduct (ℂ.mkspan p₁ p₂)) (prdof : 𝔻.product-of (F.ₒ X) (F.ₒ Y))
                        {covprd : || 𝔻.Hom (F.ₒ P) (×of.O12 prdof) ||}
                          → ×of.π₁ prdof 𝔻.∘ covprd 𝔻.~ F.ₐ p₁ → ×of.π₂ prdof 𝔻.∘ covprd 𝔻.~ F.ₐ p₂
                            → 𝔻.is-regular-epi covprd


  lc-isprd2lc-prd : {F : efunctor ℂ 𝔻} → is-left-covering-isprd F → is-left-covering-prd F
  lc-isprd2lc-prd {F} Flc = record
    { prduniv-is-repi = λ {X} {Y} wprdof prdof {covpb} tr₁ tr₂ →
                     prduniv-is-repi (w×of.iswprd wprdof) prdof tr₁ tr₂
    }
    where open is-left-covering-isprd Flc


  record is-left-covering-iseql (F : efunctor ℂ 𝔻) : Set₁ where
    private
      module F = efunctor F
    field
      eqluniv-is-repi : {X Y : ℂ.Obj} {f f' : || ℂ.Hom X Y ||}
                        {wE : ℂ.Obj} {we : || ℂ.Hom wE X ||} {we-pfeq : f ℂ.∘ we ℂ.~ f' ℂ.∘ we}
                        (iswe : ℂ.is-wequaliser we-pfeq)
                        {E : 𝔻.Obj} {e : || 𝔻.Hom E (F.ₒ X) ||} {e-pfeq : F.ₐ f 𝔻.∘ e 𝔻.~ F.ₐ f' 𝔻.∘ e}
                        (ise : 𝔻.is-equaliser e-pfeq)
                        {coveql : || 𝔻.Hom (F.ₒ wE) E ||} (tr : e 𝔻.∘ coveql 𝔻.~ F.ₐ we)
                          → 𝔻.is-regular-epi coveql


  record is-left-covering-eql (F : efunctor ℂ 𝔻) : Set₁ where
    private
      module F = efunctor F
    field
      eqluniv-is-repi : {X Y : ℂ.Obj} {f f' : || ℂ.Hom X Y ||}
                        (weqlC : ℂ.wequaliser-of f f') (eqlD : 𝔻.equaliser-of (F.ₐ f) (F.ₐ f'))
                        {coveql : || 𝔻.Hom (F.ₒ (weqlof.wEql weqlC)) (eqlof.Eql eqlD) ||}
                        (tr : eqlof.eqlar eqlD 𝔻.∘ coveql 𝔻.~ F.ₐ (weqlof.weqlar weqlC))
                          → 𝔻.is-regular-epi coveql


  lc-iseql2lc-eql : {F : efunctor ℂ 𝔻} → is-left-covering-iseql F → is-left-covering-eql F
  lc-iseql2lc-eql {F} Flc = record
    { eqluniv-is-repi = λ weqlC eqlD tr → eqluniv-is-repi (weqlof.isweql weqlC) (eqlof.iseql eqlD) tr
    }
    where open is-left-covering-iseql Flc




  record is-left-covering-pb (F : efunctor ℂ 𝔻) : Set₁ where
    private
      module F = efunctor F -- Fext to PC-ex; Fid to PC-id; Fcmp to PC-cmp)
    field
      pbuniv-is-repi : {X Y Z : ℂ.Obj} {f : || ℂ.Hom X Z ||} {g : || ℂ.Hom Y Z ||}
                       (wpbC : ℂ.wpullback-of f g) (pbD : 𝔻.pullback-of (F.ₐ f) (F.ₐ g))
                       --{spanC : square/cosp ℂ f g} (wpbsqC : is-wpb-square (sq/cosp2sq ℂ spanC))
                       --{spanD : square/cosp 𝔻 (F.ₐ f) (F.ₐ g)} (pbsqD : is-pb-square (sq/cosp2sq 𝔻 spanD))
                       {covpb : || 𝔻.Hom (F.ₒ (wpbof.ul wpbC)) (pbof.ul pbD) ||}
                       (tr₁ : pbof.π/₁ pbD 𝔻.∘ covpb 𝔻.~ F.ₐ (wpbof.wπ/₁ wpbC))
                       (tr₂ : pbof.π/₂ pbD 𝔻.∘ covpb 𝔻.~ F.ₐ (wpbof.wπ/₂ wpbC))
                         → 𝔻.is-regular-epi covpb
   {- <>lcov-ar : {X Y Z : ℂ.Obj} {f : || ℂ.Hom X Z ||} {g : || ℂ.Hom Y Z ||}
                {spanC : square/cosp ℂ f g} (wpbsqC : is-wpb-square (sq/cosp2sq ℂ spanC))
                {spanD : square/cosp 𝔻 (F.ₐ f) (F.ₐ g)} (pbsqD : is-pb-square (sq/cosp2sq 𝔻 spanD))
                  → || 𝔻.Hom (F.ₒ (ul spanC)) (ul spanD) ||
    <>lcov-ar = {!!}-}


  record is-left-covering-ispb (F : efunctor ℂ 𝔻) : Set₁ where -- (wpbC : has-weak-pullbacks ℂ) (regR : is-regular ℝ)
    private
      module F = efunctor F -- Fext to PC-ex; Fid to PC-id; Fcmp to PC-cmp)
    field
      pbuniv-is-repi : {X Y Z : ℂ.Obj} {f : || ℂ.Hom X Z ||} {g : || ℂ.Hom Y Z ||}
                       {P : ℂ.Obj} {p₁ : || ℂ.Hom P X ||} {p₂ : || ℂ.Hom P Y ||} {Psqpf : f ℂ.∘ p₁ ℂ.~ g ℂ.∘ p₂}
                       (Pwpbpf : ℂ.is-wpb-square (ℂ.mksq {down = f} {g} (ℂ.mksq/ Psqpf)))
                       (pbD : 𝔻.pullback-of (F.ₐ f) (F.ₐ g))
                       {covpb : || 𝔻.Hom (F.ₒ P) (pbof.ul pbD) ||}
                       (tr₁ : pbof.π/₁ pbD 𝔻.∘ covpb 𝔻.~ F.ₐ p₁) (tr₂ : pbof.π/₂ pbD 𝔻.∘ covpb 𝔻.~ F.ₐ p₂)
                         → 𝔻.is-regular-epi covpb


  lc-ispb2lc-pb : {F : efunctor ℂ 𝔻} → is-left-covering-ispb F → is-left-covering-pb F
  lc-ispb2lc-pb {F} Flc = record
    { pbuniv-is-repi = λ {X} {Y} {Z} {f} {g} wpbC pbD {covpb} tr₁ tr₂ → pbuniv-is-repi (wpbof.w×/iswpbsq wpbC) pbD tr₁ tr₂
    }
    where open is-left-covering-ispb Flc


  record is-left-covering-bw (F : efunctor ℂ 𝔻) : Set₁ where
    private
      module F = efunctor-aux F -- Fext to PC-ex; Fid to PC-id; Fcmp to PC-cmp)
    open efunctor-aux F
    field
      bwuniv-is-repi : {DL DR : ℂ.Obj} {sp₁ sp₂ : ℂ.span/ DL DR} (wbw : ℂ.wbow-of sp₁ sp₂)
                       (bw : 𝔻.bow-of (F.span/ sp₁) (F.span/ sp₂))
                       {covbw : || 𝔻.Hom (F.ₒ (wbwof.Ob wbw)) (bwof.Ob bw) ||}
                         → bwof.π//₁ bw 𝔻.∘ covbw 𝔻.~ F.ₐ (wbwof.wπ//₁ wbw)
                           → bwof.π//₂ bw 𝔻.∘ covbw 𝔻.~ F.ₐ (wbwof.wπ//₂ wbw)
                             → 𝔻.is-regular-epi covbw


--end left-covering-defs


private
  module lcdefs {ℂ 𝔻 : ecategory} = left-covering-defs ℂ 𝔻
open lcdefs public


record is-left-covering {ℂ 𝔻 : ecategory} (F : efunctor ℂ 𝔻) : Set₁ where
  field
    lc! : is-left-covering-trm F
    lc× : is-left-covering-prd F
    lceql : is-left-covering-eql F
    lc×/ : is-left-covering-pb F
    lcbw : is-left-covering-bw F
  open is-left-covering-trm lc! public
  open is-left-covering-prd lc× public
  open is-left-covering-eql lceql public
  open is-left-covering-pb lc×/ public
  open is-left-covering-bw lcbw public
