
{-# OPTIONS --without-K #-}

module ecats.functors.props.exact-functor where

--open import setoids
open import ecats.basic-defs.ecat-def&not
--open import ecats.basic-defs.commut-shapes
--open import ecats.basic-defs.isomorphism
open import ecats.basic-defs.kernel-pair
open import ecats.basic-defs.eqv-rel
open import ecats.basic-defs.epi&mono
open import ecats.reg&ex
--open import ecats.basic-defs.regular-ecat
--open import ecats.basic-defs.exact-ecat
open import ecats.basic-props.epi&mono-basic
open import ecats.basic-props.epi&mono
--open import ecats.basic-props.image-fact
open import ecats.finite-limits.d&n-bin-product
open import ecats.finite-limits.d&n-pullback
open import ecats.finite-limits.defs.pullback-is-weak
--open import ecats.finite-limits.all
open import ecats.functors.defs.efunctor-d&n
open import ecats.functors.defs.preserving-functor




-------------------------------------
-- Some properties of exact functors
-------------------------------------

module exact-functor-props {ℂ 𝔻 : ecategory} {F : efunctor ℂ 𝔻} (regC : is-regular ℂ)
                           (regD : is-regular 𝔻) (exF : is-exact-functor F) where
  private
    module ℂ where
      open ecategory ℂ public
      open epi&mono-defs ℂ public
      open image-fact-defs ℂ public
      open kernel-pairs-defs ℂ public
      open pseudo-eq-rel-defs ℂ public
      open eq-rel-defs ℂ public
      open epi&mono-props-all ℂ public
      open image-fact-props ℂ public
      open binary-products ℂ public
      open pullback-squares ℂ public
    module rℂ where
      open is-regular regC public
      open pullbacks-aux haspb public
      open regular-cat-props regC public
      open ℂ.has-pb→has-kerpair haspb public
      open ℂ.has-pb→ker-are-eqr haspb public
    module 𝔻 where
      open ecategory 𝔻 public
      open epi&mono-defs 𝔻 public
      open epi&mono-props 𝔻 public
      open kernel-pairs-defs 𝔻 public
      open eq-rel-defs 𝔻 public
      --open finite-limits-d&p 𝔻 public
    module r𝔻 where
      open is-regular regD public
      open pullbacks-aux haspb public
      open regular-cat-props regD public
      open 𝔻.has-pb→has-kerpair haspb public
      open 𝔻.has-pb→ker-are-eqr haspb public
    module F = efunctor-aux F
    module exF = is-exact-functor exF

  -- exact functors preserve regular epis (this proof only requires existence of kernel pairs in ℂ)
  
  pres-repi-pf : {A B : ℂ.Obj} {f : || ℂ.Hom A B ||}
                     → ℂ.is-regular-epi f → 𝔻.is-regular-epi (F.ₐ f)
  pres-repi-pf {A} {B} {f} repiC = record
    { relOb = F.ₒ kpf.ul
    ; rel₁ = F.ₐ kpf.π/₁
    ; rel₂ = F.ₐ kpf.π/₂
    ; coeq = Fexsq.iscoeq
    }
    where kpf : ℂ.pullback-of f f
          kpf = rℂ.kp-of f
          module kpf = ℂ.pullback-of-not kpf
          kp-is-exC : ℂ.is-exact-seq kpf.π/₁ kpf.π/₂ f
          kp-is-exC = record { iscoeq = ℂ.repi-is-coeq-of-ker-pair repiC kpf
                             ; iskerpair = kpf.×/ispbsq
                             }
                             where open ℂ.epi&mono-pullbacks rℂ.haspb
          module Fexsq = 𝔻.is-exact-seq (exF.pres-ex-seq-pf kp-is-exC)


  pres-repi : preserves-regular-epis F
  pres-repi = record { pres-repi-pf = pres-repi-pf }

{-
  -- exact functors preserve coequalisers of peq's, this proof requires ℂ to be exact

  pres-coeq-of-peq : (exC : is-exact//has-finlim rℂ.hasfl)
                     {R A Q : ℂ.Obj} {r₁ r₂ : || ℂ.Hom R A ||} {q : || ℂ.Hom A Q ||}
                       → ℂ.is-peq-rel r₁ r₂ → ℂ.is-coeq r₁ r₂ q
                         → 𝔻.is-coeq (F.ₐ r₁) (F.ₐ r₂) (F.ₐ q)
  pres-coeq-of-peq exC {A = A} {r₁ = r₁} {r₂} {q} ispeqC iscoeqC = 𝔻.epi/coeq-so-coeq FimgrC-repi.uniq
                                                                                       (F.∘ax imgr.tr₁)
                                                                                       (F.∘ax imgr.tr₂)
                                                                                       Frq-ex.iscoeq
                       where open ecategory-aux-only 𝔻
                             module exℂ where
                               open is-exact (mkexact exC) public
                               open exact-cat-props-only (mkexact exC) public
                             module q = ℂ.is-coeq iscoeqC
                             module imgr where
                               open exℂ.exact-has-quot-peq-rel (ℂ.mkpeq ispeqC) public
                               open ℂ.img-fact-of imgR public
                             imgrC-repi : ℂ.is-regular-epi imgr.C
                             imgrC-repi = rℂ.any-imgC-is-repi imgr.imgR
                             module imgrC = ℂ.is-regular-epi imgrC-repi
                             module r-eqr = ℂ.eqrel-over imgr.eqr/
                             mrq-ex : ℂ.is-exact-seq r-eqr.r₁ r-eqr.r₂ q
                             mrq-ex = exℂ.coeq-of-eqrel-is-eff imgr.eqr/ (ℂ.coeq/epi-so-coeq imgrC.uniq
                                                                                             imgr.tr₁
                                                                                             imgr.tr₂
                                                                                             iscoeqC)
                             Fmrq-ex : 𝔻.is-exact-seq (F.ₐ r-eqr.r₁) (F.ₐ r-eqr.r₂) (F.ₐ q)
                             Fmrq-ex = exF.pres-ex-seq-pf mrq-ex
                             module Frq-ex = 𝔻.is-exact-seq Fmrq-ex
                             FimgrC-repi : 𝔻.is-regular-epi (F.ₐ imgr.C)
                             FimgrC-repi = pres-repi-pf imgrC-repi
                             module FimgrC-repi = 𝔻.is-regular-epi FimgrC-repi
-}
-- end exact-functor-props



-- N.B. the proof of this only requires existence of kernel pairs in ℂ and exactness of F,
-- it may be worth to phrase it weakening assumptions.
exact-functor-pres-repis : {ℂ 𝔻 : ecategory} {F : efunctor ℂ 𝔻} (regC : is-regular ℂ) (regD : is-regular 𝔻)
                              → is-exact-functor F → preserves-regular-epis F
exact-functor-pres-repis regC regD exF = pres-repi
                                       where open exact-functor-props regC regD exF 


