
{-# OPTIONS --without-K #-}

module ecats.functors.props.left-covering.left-covering-basic where

open import ecats.basic-defs.ecat-def&not
open import ecats.basic-defs.all-arrows
open import ecats.basic-defs.eqv-rel
open import ecats.basic-defs.regular-ecat
open import ecats.basic-defs.exact-ecat
open import ecats.basic-props.all
open import ecats.finite-limits.all
open import ecats.functors.defs.efunctor-d&n
open import ecats.functors.defs.natural-transformation
open import ecats.functors.defs.basic-defs
open import ecats.functors.defs.preserving-functor
open import ecats.functors.defs.left-covering


-- A functor that preserves limits is left covering

module efunctor-preslim2lcov {ℂ 𝔻 : ecategory} (F : efunctor ℂ 𝔻) where
  private
    module macros (𝕏 : ecategory) where
        open ecategory-aux 𝕏 public
        open arrows-defs 𝕏 public
        open finite-limits 𝕏 public
        open finite-weak-limits 𝕏 public
    module ℂ = macros ℂ
    module 𝔻 = macros 𝔻
    module F = efunctor-aux F

  pres!→lc! : has-terminal ℂ → preserves-terminal F → is-left-covering-trm F
  pres!→lc! has! pres! = record
    { trmuniv-is-repi = λ {X} wtrm {T}  trm cov! → split-epi-is-repi (med!-sepi wtrm trm cov!)
    }
    where open preserves-terminal pres!
          open epis&monos-props 𝔻
          med!-sepi : {X : ℂ.Obj} {T : 𝔻.Obj} → ℂ.is-wterminal X → 𝔻.is-terminal T → (cov! : || 𝔻.Hom (F.ₒ X) T ||)
                        → 𝔻.is-split-epi cov!
          med!-sepi {X} {T} wtrm trm cov! = record
                                           { rinv = F.ₐ med-ar 𝔻.∘ F!.! T
                                           ; rinv-ax = T!.!uqg
                                           }
                                           where open has-terminal has!
                                                 module X! = ℂ.is-wterminal wtrm
                                                 module F! = 𝔻.is-terminal (pres-!-pf istrm)
                                                 module T! = 𝔻.is-terminal trm
                                                 med-ar : || ℂ.Hom trmOb X ||
                                                 med-ar = X!.w! trmOb


  pres×→lc× : has-bin-products ℂ → preserves-bin-products F → is-left-covering-prd F
  pres×→lc× has× pres× = record
    { prduniv-is-repi = λ wprdof prdof tr₁ tr₂ → split-epi-is-repi (covprd-sepi wprdof prdof tr₁ tr₂)
    }
    where open preserves-bin-products pres×
          open epis&monos-props 𝔻
          open bin-product-props 𝔻
          open product-is-unique-uptoiso
          module ×of = 𝔻.product-of
          module w×of = ℂ.wproduct-of
          covprd-sepi : {X Y : ℂ.Obj} (wprdof : ℂ.wproduct-of X Y) (prdof : 𝔻.product-of (F.ₒ X) (F.ₒ Y))
                        {covprd : || 𝔻.Hom (F.ₒ (w×of.O12 wprdof))
                                            (×of.O12 prdof) ||}
                          → ×of.π₁ prdof 𝔻.∘ covprd 𝔻.~ F.ₐ (w×of.wπ₁ wprdof)
                            → ×of.π₂ prdof 𝔻.∘ covprd 𝔻.~ F.ₐ (w×of.wπ₂ wprdof)
                              → 𝔻.is-split-epi covprd
          covprd-sepi {X} {Y} wprdof prdof {covprd} tr₁ tr₂ = record
            { rinv = F.ₐ med-ar 𝔻.∘ F×c.< ×.π₁ , ×.π₂ >
            ; rinv-ax = ×.×uq (ridgenˢ (ass ⊙ ∘e r tr₁ ⊙ ass ⊙ ∘e r (F.∘ax w×.w×tr₁) ⊙ F×c.×tr₁))
                              (ridgenˢ (ass ⊙ ∘e r tr₂ ⊙ ass ⊙ ∘e r (F.∘ax w×.w×tr₂) ⊙ F×c.×tr₂))
            }
            where open ecategory-aux-only 𝔻
                  module C×c = bin-products-aux has×
                  module C× = binary-products ℂ
                  module w× = ℂ.wproduct-of wprdof
                  module × = 𝔻.product-of prdof
                  module ×c = C×.product-of (C×c.prd-of X Y)
                  module F×c = 𝔻.product-of (𝔻.mk×of (pres-×-pf ×c.×isprd))
                  med-ar : || ℂ.Hom ×c.O12 w×.O12 ||
                  med-ar = w×.w< ×c.π₁ , ×c.π₂ >
                    


  pres×-lcpb→lc-eql : has-bin-products ℂ → preserves-bin-products F
                     → is-left-covering-pb F → is-left-covering-eql F
  pres×-lcpb→lc-eql prdC pres× lcpb = record
    { eqluniv-is-repi = λ {X} {Y} {f} {f'} weqlC eqlD {coveql} tr →
                      pbuniv-is-repi (ℂwl.weqlof→wpbof<> ℂ×.×of weqlC) (eql2pb eqlD) tr (assˢ ⊙ ∘e tr r ⊙ F.∘ax-rf)
    }
    where open ecategory-aux-only 𝔻
          module 𝔻l = relations-among-limit-diagrams 𝔻
          module ℂwl = relations-among-weak-limit-diagrams ℂ
          open preserves-bin-products pres×
          open is-left-covering-pb lcpb
          module ℂ× = bin-products-aux prdC
          F×of : (X Y : ℂ.Obj) → 𝔻.product-of (F.ₒ X) (F.ₒ Y)
          F×of X Y = 𝔻.mk×of (pres-×-pf (ℂ×.×isprd {X} {Y}))
          eql2pb : {X Y : ℂ.Obj} {f f' : || ℂ.Hom X Y ||} (eqlD : 𝔻.equaliser-of (F.ₐ f) (F.ₐ f'))
                      → 𝔻.pullback-of (F.ₐ (ℂ×.< f , f' >)) (F.ₐ (ℂ×.Δ Y))
          eql2pb {_} {Y} {f} {f'} eqlD = 𝔻.mkpb-of ( ×/ext-dr (is-eql→is-pb iseql)
                                                               (F×.ar~<>ˢ (F.∘ax-rf ⊙ F.ext ℂ×.×tr₁) (F.∘ax-rf ⊙ F.ext ℂ×.×tr₂))
                                                               (F×.ar~<>ˢ (F.∘ax-rf ⊙ F.idax ℂ×.×tr₁) (F.∘ax-rf ⊙ F.idax ℂ×.×tr₂)) )
                              where open pullback-props 𝔻
                                    module F× = 𝔻.product-of-not (F×of Y Y)
                                    open 𝔻.equaliser-of eqlD
                                    open 𝔻l.equaliser↔pullback-of-diag (F×of Y Y) eqleq {F.ₐ f 𝔻.∘ eqlar}
                                                                         (F×.<>ar~<>ar lidˢ (lidgenˢ (eqleq ˢ)))
-- end efunctor-preslim2lcov
