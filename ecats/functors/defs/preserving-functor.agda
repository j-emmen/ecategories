
{-# OPTIONS --without-K #-}

module ecats.functors.defs.preserving-functor where

open import ecats.basic-defs.ecat-def&not
open import ecats.basic-defs.arrows
open import ecats.basic-props.epi&mono
open import ecats.finite-limits.defs&not
open import ecats.functors.defs.efunctor-d&n
open import ecats.functors.defs.basic-defs


-- Preservation of stuff

private
  module pt-macros (𝕏 : ecategory) where
    open ecategory 𝕏 public
    open terminal-defs 𝕏 public

record preserves-terminal {ℂ 𝔻 : ecategory} (F : efunctor ℂ 𝔻) : Set₁ where
  private
    module ℂ = pt-macros ℂ
    module 𝔻 = pt-macros 𝔻
    module F = efunctor F
  field
    pres-!-pf : {X : ℂ.Obj} → ℂ.is-terminal X → 𝔻.is-terminal (F.ₒ X)



private
  module pbp-macros (𝕏 : ecategory) where
    open ecategory 𝕏 public
    open comm-shapes 𝕏 public
    open bin-product-defs 𝕏 public
    
record preserves-bin-products {ℂ 𝔻 : ecategory} (F : efunctor ℂ 𝔻) : Set₁ where
  private
    module ℂ = pbp-macros ℂ
    module 𝔻 = pbp-macros 𝔻
    module F = efunctor-aux F
  field
    pres-×-pf : {sp : ℂ.span} → ℂ.is-product sp →  𝔻.is-product (F.span sp)

private
  module peql-macros (𝕏 : ecategory) where
    open ecategory 𝕏 public
    open equaliser-defs 𝕏 public
    
record preserves-equalisers {ℂ 𝔻 : ecategory} (F : efunctor ℂ 𝔻) : Set₁ where
  private
    module ℂ = peql-macros ℂ
    module 𝔻 = peql-macros 𝔻
    module F = efunctor-aux F
  field
    pres-eql-pf : {A B E : ℂ.Obj}{f f' : || ℂ.Hom A B ||}{e : || ℂ.Hom E A ||}
                  {pfeq : f ℂ.∘ e ℂ.~ f' ℂ.∘ e} → ℂ.is-equaliser pfeq
                     → 𝔻.is-equaliser (F.∘∘ pfeq)


private
  module peql-macros (𝕏 : ecategory) where
    open ecategory 𝕏 public
    --open comm-shapes 𝕏 public
    open equaliser-defs 𝕏 public
    
record preserves-equalisers {ℂ 𝔻 : ecategory} (F : efunctor ℂ 𝔻) : Set₁ where
  private
    module ℂ = peql-macros ℂ
    module 𝔻 = peql-macros 𝔻
    module F = efunctor-aux F
  field
    pres-eql-pf : {A B E : ℂ.Obj}{f f' : || ℂ.Hom A B ||}{e : || ℂ.Hom E A ||}
                  {pfeq : f ℂ.∘ e ℂ.~ f' ℂ.∘ e} → ℂ.is-equaliser pfeq
                     → 𝔻.is-equaliser (F.∘∘ pfeq)


private
  module ppb-macros (𝕏 : ecategory) where
    open ecategory 𝕏 public
    open comm-shapes 𝕏 public
    open pullback-defs 𝕏 public
    module sq = comm-square
    
record preserves-pullbacks {ℂ 𝔻 : ecategory} (F : efunctor ℂ 𝔻) : Set₁ where
  private
    module ℂ = ppb-macros ℂ
    module 𝔻 = ppb-macros 𝔻
    module F = efunctor-aux F
  field
    pres-ispbof-pf : {I A B : ℂ.Obj}{a : || ℂ.Hom A I ||}{b : || ℂ.Hom B I ||}{sq/ : ℂ.square/cosp a b}
                      → ℂ.is-pullback-of sq/ → 𝔻.is-pullback-of (F.sq/ sq/)

-- pbof-pf :  {I A B : ℂ.Obj}{a : || ℂ.Hom A I ||}{b : || ℂ.Hom B I ||} → ℂ.pullback-of a b → 


{-
    pres-pbsq-pf : {sqC : ℂ.comm-square} → ℂ.is-pb-square sqC → 𝔻.is-pb-square (F.sq sqC)
  pres-pbsq-gen :  {sqC : ℂ.comm-square}
                   {p₁ : || 𝔻.Hom (F.ₒ (ℂ.sq.ul sqC)) (F.ₒ (ℂ.sq.dl sqC)) ||}
                   {p₂ : || 𝔻.Hom (F.ₒ (ℂ.sq.ul sqC)) (F.ₒ (ℂ.sq.ur sqC)) ||}
                   (sqpf : F.ₐ (ℂ.sq.down sqC) 𝔻.∘ p₁ 𝔻.~ F.ₐ (ℂ.sq.right sqC) 𝔻.∘ p₂)
                     → p₁ 𝔻.~ F.ₐ (ℂ.sq.left sqC) → p₂ 𝔻.~ F.ₐ (ℂ.sq.up sqC)
                       → ℂ.is-pb-square sqC → 𝔻.is-pb-square (𝔻.mksq (𝔻.mksq/ sqpf))
  pres-pbsq-gen {sqC} {p₁} {p₂} sqpf pfp₁ pfp₂ ispb = ×/ext-ul sqpf (pres-pbsq-pf ispb) pfp₁ pfp₂
                                                    where open pullback-props 𝔻
-}

record preserves-fin-limits {ℂ 𝔻 : ecategory} (F : efunctor ℂ 𝔻) : Set₁ where
  field
    prestrm : preserves-terminal F
    presprd : preserves-bin-products F
    preseql : preserves-equalisers F
    prespb : preserves-pullbacks F
  open preserves-terminal prestrm public
  open preserves-bin-products presprd public
  open preserves-equalisers preseql public
  open preserves-pullbacks prespb public


private
  module pre-macros (𝕏 : ecategory) where
    open ecategory 𝕏 public
    open epi&mono-defs 𝕏 public

record preserves-regular-epis {ℂ 𝔻 : ecategory} (F : efunctor ℂ 𝔻) : Set₁ where
  private
    module ℂ = pre-macros ℂ
    module 𝔻 = pre-macros 𝔻
    module F = efunctor F
  field
    pres-repi-pf : {A B : ℂ.Obj} {f : || ℂ.Hom A B ||}
                      → ℂ.is-regular-epi f → 𝔻.is-regular-epi (F.ₐ f)



private
  module pm-macros (𝕏 : ecategory) where
    open ecat 𝕏 public
    open epi&mono-defs 𝕏 public
    
record preserves-monic {ℂ 𝔻 : ecategory} (F : efunctor ℂ 𝔻) : Set₁ where
  private
    module ℂ = pm-macros ℂ
    module 𝔻 = pm-macros 𝔻
    module F = efctr F
  field
    pres-monic-pf : {A B : ℂ.Obj} {ar : || ℂ.Hom A B ||}
                       → ℂ.is-monic ar → 𝔻.is-monic (F.ₐ ar)

private
  module pjm-macros (𝕏 : ecategory) where
    open ecategory 𝕏 public
    open comm-shapes 𝕏 public
    open epi&mono-defs 𝕏 public

record preserves-jointly-monic/ {ℂ 𝔻 : ecategory} (F : efunctor ℂ 𝔻) : Set₁ where
  private
    module ℂ = pjm-macros ℂ
    module 𝔻 = pjm-macros 𝔻
    module F = efunctor-aux F
  field
    pres-jm/-pf : {A B : ℂ.Obj} {sp/ : ℂ.span/ A B}
                     → ℂ.is-jointly-monic/ sp/ → 𝔻.is-jointly-monic/ (F.span/ sp/)




-- Exact functor

private
  module ex-macros (𝕏 : ecategory) where
    open ecategory 𝕏 public
    open kernel-pairs-defs 𝕏 public
    open pullback-squares 𝕏 public
    open epi&mono-defs 𝕏 public
    open epi&mono-props-all 𝕏 public
    
record is-exact-functor {ℂ 𝔻 : ecategory} (F : efunctor ℂ 𝔻) : Set₁ where
  private
    module ℂ = ex-macros ℂ
    module 𝔻 = ex-macros 𝔻
    module F = efunctor-aux F
  field
    presfl : preserves-fin-limits F
    presrepi : preserves-regular-epis F
  open preserves-fin-limits presfl public
  open preserves-regular-epis presrepi public
  pres-ex-seq-pf : {R A Q : ℂ.Obj} {r₁ r₂ : || ℂ.Hom R A ||} {q : || ℂ.Hom A Q ||}
                      → ℂ.is-exact-seq r₁ r₂ q → 𝔻.is-exact-seq (F.ₐ r₁) (F.ₐ r₂) (F.ₐ q)
  pres-ex-seq-pf {R} {A} {Q} {r₁} {r₂} {q} isex = record
    { iscoeq = repi-is-coeq-of-ker-pair (pres-repi-pf repi) (𝔻.pbof-is2sq Fpb)
    ; iskerpair = 𝔻.pb-is2sq Fpb.ispb
    }
    where module exs = ℂ.is-exact-seq isex
          repi : ℂ.is-regular-epi q
          repi = record { coeq = exs.iscoeq }
          Fpb : 𝔻.is-pullback-of (F.sq/ exs.sq/)
          Fpb = pres-ispbof-pf (ℂ.mkis-pb-of (ℂ.pb-sq2is exs.iskerpair))
          module Fpb = 𝔻.is-pullback-of Fpb
          open epis&monos-props 𝔻 using (repi-is-coeq-of-ker-pair)

