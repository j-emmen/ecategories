 
-- disable the K axiom:

{-# OPTIONS --without-K #-}

-- Agda version 2.5.4.1

module ecats.functors.defs.preserving-functor where

open import ecats.basic-defs.ecat-def&not
open import ecats.basic-defs.all-arrows
open import ecats.basic-props.epi&mono
open import ecats.finite-limits.all
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
  module pbn-macros (𝕏 : ecategory) where
    open ecategory 𝕏 public
    open comm-shapes 𝕏 public
    open bin-product-defs 𝕏 public
    
record preserves-bin-products {ℂ 𝔻 : ecategory} (F : efunctor ℂ 𝔻) : Set₁ where
  private
    module ℂ = pbn-macros ℂ
    module 𝔻 = pbn-macros 𝔻
    module F = efunctor-aux F
  field
    pres-×-pf : {sp : ℂ.span} → ℂ.is-product sp →  𝔻.is-product (F.span sp)



private
  module ppb-macros (𝕏 : ecategory) where
    open ecategory 𝕏 public
    open comm-shapes 𝕏 public
    open pullback-defs 𝕏 public
    module Csq = comm-square
    
record preserves-pullbacks {ℂ 𝔻 : ecategory} (F : efunctor ℂ 𝔻) : Set₁ where
  private
    module ℂ = ppb-macros ℂ
    module 𝔻 = ppb-macros 𝔻
    module F = efunctor-aux F
  field
    pres-pbsq-pf : {sqC : ℂ.comm-square} → ℂ.is-pb-square sqC → 𝔻.is-pb-square (F.sq sqC)
  pres-pbsq-gen :  {sqC : ℂ.comm-square}
                   {p₁ : || 𝔻.Hom (F.ₒ (ℂ.Csq.ul sqC)) (F.ₒ (ℂ.Csq.dl sqC)) ||}
                   {p₂ : || 𝔻.Hom (F.ₒ (ℂ.Csq.ul sqC)) (F.ₒ (ℂ.Csq.ur sqC)) ||}
                   (sqpf : F.ₐ (ℂ.Csq.down sqC) 𝔻.∘ p₁ 𝔻.~ F.ₐ (ℂ.Csq.right sqC) 𝔻.∘ p₂)
                     → p₁ 𝔻.~ F.ₐ (ℂ.Csq.left sqC) → p₂ 𝔻.~ F.ₐ (ℂ.Csq.up sqC)
                       → ℂ.is-pb-square sqC → 𝔻.is-pb-square (𝔻.mksq (𝔻.mksq/ sqpf))
  pres-pbsq-gen {sqC} {p₁} {p₂} sqpf pfp₁ pfp₂ ispb = ×/ext-ul sqpf (pres-pbsq-pf ispb) pfp₁ pfp₂
                                                    where open pullback-props 𝔻

record preserves-fin-limits {ℂ 𝔻 : ecategory} (F : efunctor ℂ 𝔻) : Set₁ where
  field
    prestrm : preserves-terminal F
    presprd : preserves-bin-products F
    prespb : preserves-pullbacks F
  open preserves-terminal prestrm public
  open preserves-bin-products presprd public
  open preserves-pullbacks prespb public

private
  module pre-macros (𝕏 : ecategory) where
    open ecategory 𝕏 public
    open epis&monos-defs 𝕏 public

record preserves-regular-epis {ℂ 𝔻 : ecategory} (F : efunctor ℂ 𝔻) : Set₁ where
  private
    module ℂ = pre-macros ℂ
    module 𝔻 = pre-macros 𝔻
    module F = efunctor F
  field
    pres-repi-pf : {A B : ℂ.Obj} {f : || ℂ.Hom A B ||}
                      → ℂ.is-regular-epi f → 𝔻.is-regular-epi (F.ₐ f)



private
  module pjm-macros (𝕏 : ecategory) where
    open ecategory 𝕏 public
    open comm-shapes 𝕏 public
    open epis&monos-defs 𝕏 public
    
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
    open epis&monos-defs 𝕏 public
    open epis&monos-props 𝕏 public
    
record is-exact-functor {ℂ 𝔻 : ecategory} (F : efunctor ℂ 𝔻) : Set₁ where
  private
    module ℂ = ex-macros ℂ
    module 𝔻 = ex-macros 𝔻
    module F = efunctor-aux F
  field
    presfl : preserves-fin-limits F
    presre : preserves-regular-epis F
  open preserves-fin-limits presfl public
  open preserves-regular-epis presre public
  pres-ex-seq-pf : {R A Q : ℂ.Obj} {r₁ r₂ : || ℂ.Hom R A ||} {q : || ℂ.Hom A Q ||}
                      → ℂ.is-exact-seq r₁ r₂ q → 𝔻.is-exact-seq (F.ₐ r₁) (F.ₐ r₂) (F.ₐ q)
  pres-ex-seq-pf {R} {A} {Q} {r₁} {r₂} {q} isex = record
    { iscoeq = 𝔻.repi-is-coeq-of-ker-pair (pres-repi-pf repi) Fsq
    ; iskerpair = Fsq.×/ispbsq
    }
    where module exs = ℂ.is-exact-seq isex
          repi : ℂ.is-regular-epi q
          repi = record { coeq = exs.iscoeq }
          Fsq : 𝔻.pullback-of (F.ₐ q) (F.ₐ q)
          Fsq = 𝔻.mkpb-of (pres-pbsq-pf exs.iskerpair)
          module Fsq = 𝔻.pullback-of Fsq
  
