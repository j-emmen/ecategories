
{-# OPTIONS --without-K #-}

module ecats.functors.props.basic-props where

open import ecats.basic-defs.ecat-def&not
open import ecats.basic-defs.arrows
open import ecats.basic-props.epi&mono-basic
open import ecats.basic-props.isomorphism
open import ecats.finite-limits.all
open import ecats.functors.defs.efunctor-d&n
open import ecats.functors.defs.natural-transformation
open import ecats.functors.defs.basic-defs
open import ecats.functors.defs.preserving-functor
open import ecats.functors.defs.left-covering



module efunctor-props {ℂ 𝔻 : ecategory} (F : efunctor ℂ 𝔻) where
  private
    module macros (𝕏 : ecategory) where
        open ecategory-aux 𝕏 public
        open arrows-defs 𝕏 public
        open iso-props 𝕏 public
        open finite-limits 𝕏 public
        open finite-weak-limits 𝕏 public
    module ℂ = macros ℂ
    module 𝔻 = macros 𝔻
    module F = efunctor-aux F

  Fiso :  {A B : ℂ.Obj} {f : || ℂ.Hom A B ||} {invf : || ℂ.Hom B A ||}
             → ℂ.is-iso-pair f invf → 𝔻.is-iso-pair (F.ₐ f) (F.ₐ invf)
  Fiso {f = f} {invf} isopair = record
    { iddom = F.∘ax iddom ⊙ F.id
    ; idcod = F.∘ax idcod ⊙ F.id
    }
    where open ℂ.is-iso-pair isopair
          open ecategory-aux 𝔻
  

  Fpres-iso : {A B : ℂ.Obj} {f : || ℂ.Hom A B ||}
                 → ℂ.is-iso f → 𝔻.is-iso (F.ₐ f)
  Fpres-iso isof = record
    { invf = F.ₐ invf
    ; isisopair = Fiso isisopair
    }
    where open ℂ.is-iso isof



  pres!→lc! : has-terminal ℂ → preserves-terminal F → is-left-covering-trm F
  pres!→lc! has! pres! = record
    { trmuniv-is-repi = λ {X} wtrm {T}  trm cov! → split-epi-is-repi (med!-sepi wtrm trm cov!)
    }
    where open preserves-terminal pres!
          open epi&mono-props 𝔻
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
          open epi&mono-props 𝔻
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




  -- Essential equivalences are equivalences

  module eeqv-is-eqv (eeqv : is-ess-equivalence F) where
    open is-ess-equivalence eeqv
    open is-full isfull
    open is-faithful isfaithful
    private module essrj = is-ess-surjective-ob isesurjobj
    
    invFₒ : 𝔻.Obj → ℂ.Obj
    invFₒ = essrj.ob

    σ : (Y : 𝔻.Obj) → || 𝔻.Hom (F.ₒ (invFₒ Y)) Y ||
    σ = essrj.ar

    private
      module σ (Y : 𝔻.Obj) = 𝔻.is-iso (essrj.iso Y)
    --open σ-tmp renaming (invf to σ⁻¹; isisopair to σ-isopair; iddom to σ⁻¹σ=id; idcod to σσ⁻¹=id)

    invFₐ : {Y Y' : 𝔻.Obj} → || 𝔻.Hom Y Y' || → || ℂ.Hom (invFₒ Y) (invFₒ Y') ||
    invFₐ {Y} {Y'} g = full-ar (σ.⁻¹ Y' 𝔻.∘ g 𝔻.∘ σ Y)


    τ : (X : ℂ.Obj) → || ℂ.Hom (invFₒ (F.ₒ X)) X ||
    τ X = full-ar (σ (F.ₒ X))

    τ⁻¹ : (X : ℂ.Obj) → || ℂ.Hom X (invFₒ (F.ₒ X)) ||
    τ⁻¹ X = full-ar (σ.⁻¹ (F.ₒ X))

    τ-isopair : (X : ℂ.Obj) → ℂ.is-iso-pair (τ X) (τ⁻¹ X)
    τ-isopair X = record
      { iddom = faith-pf (~proof F.ₐ (τ⁻¹ X ℂ.∘ τ X)               ~[ F.∘ax-rfˢ ] /
                                 F.ₐ (τ⁻¹ X) 𝔻.∘ F.ₐ (τ X)          ~[ ∘e full-pf full-pf ] /
                                 σ.⁻¹ (F.ₒ X) 𝔻.∘ σ (F.ₒ X)          ~[ σ.iddom (F.ₒ X) ⊙ F.idˢ ]∎
                                 F.ₐ (ℂ.idar (invFₒ (F.ₒ X)))      ∎)
      ; idcod = faith-pf (~proof F.ₐ (τ X ℂ.∘ τ⁻¹ X)               ~[ F.∘ax-rfˢ ] /
                                 F.ₐ (τ X) 𝔻.∘ F.ₐ (τ⁻¹ X)          ~[ ∘e full-pf full-pf ] /
                                 σ (F.ₒ X) 𝔻.∘ σ.⁻¹ (F.ₒ X)          ~[ σ.idcod (F.ₒ X) ⊙ F.idˢ ]∎
                                 F.ₐ (ℂ.idar X)                  ∎)
      }
      where open ecategory-aux-only 𝔻

    module τ-tmp (X : ℂ.Obj) = ℂ.is-iso-pair (τ-isopair X)
    open τ-tmp renaming (iddom to τ⁻¹τ=id; idcod to ττ⁻¹=id)


    invF : efunctor 𝔻 ℂ
    invF = record
         { FObj = invFₒ
         ; FHom = invFₐ
         ; isF = record
               { ext = λ {Y} {Y'} {g} {g'} pf → faith-pf (~proof
                     F.ₐ (invFₐ g)                       ~[ full-pf ] /
                     σ.⁻¹ Y' 𝔻.∘ g 𝔻.∘ σ Y              ~[ ∘e (∘e r pf) r ] /
                     σ.⁻¹ Y' 𝔻.∘ g' 𝔻.∘ σ Y             ~[ full-pf ˢ ]∎
                     F.ₐ (invFₐ g')         ∎)
               ; id = λ {Y} → faith-pf (~proof
                    F.ₐ (invFₐ (𝔻.idar Y))              ~[ full-pf ] /
                    σ.⁻¹ Y 𝔻.∘ (𝔻.idar Y) 𝔻.∘ σ Y      ~[ ∘e lid r ⊙ σ.iddom Y ⊙ F.idˢ ]∎
                    F.ₐ (ℂ.idar (invFₒ Y))          ∎)
               ; cmp = λ {Y₁} {Y₂} {Y₃} g₁ g₂ → faith-pf (~proof
                     F.ₐ (invFₐ g₂ ℂ.∘ invFₐ g₁)                                 ~[ F.∘ax-rfˢ ] /
                     F.ₐ (invFₐ g₂) 𝔻.∘ F.ₐ (invFₐ g₁)                          ~[ ∘e full-pf full-pf ] /
                     (σ.⁻¹ Y₃ 𝔻.∘ g₂ 𝔻.∘ σ Y₂) 𝔻.∘ (σ.⁻¹ Y₂ 𝔻.∘ g₁ 𝔻.∘ σ Y₁)  ~[ assˢ ⊙ ∘e ass r ] /
                     σ.⁻¹ Y₃ 𝔻.∘ ((g₂ 𝔻.∘ σ Y₂) 𝔻.∘ σ.⁻¹ Y₂) 𝔻.∘ g₁ 𝔻.∘ σ Y₁  ~[ ∘e (∘e r (assˢ ⊙ ridgg r (σ.idcod Y₂))) r ] /
                     σ.⁻¹ Y₃ 𝔻.∘ g₂ 𝔻.∘ g₁ 𝔻.∘ σ Y₁                            ~[ ∘e ass r ⊙ full-pf ˢ ]∎
                     F.ₐ (invFₐ (g₂ 𝔻.∘ g₁))                             ∎)
               }
         }
         where open ecategory-aux-only 𝔻


    σnat : natural-transformation (F ○ invF) IdF
    σnat = record
      { fnc = λ {Y} → σ Y
      ; nat = λ {Y} {Y'} g → ~proof σ Y' 𝔻.∘ F.ₐ (invFₐ g)           ~[ ∘e full-pf r ⊙ ass ] /
                                     (σ Y' 𝔻.∘ σ.⁻¹ Y') 𝔻.∘ g 𝔻.∘ σ Y   ~[ lidgg r (σ.idcod Y') ]∎
                                     g 𝔻.∘ σ Y                      ∎
      }
      where open ecategory-aux-only 𝔻


    σ⁻¹nat : natural-transformation IdF (F ○ invF)
    σ⁻¹nat = record { fnc = λ {Y} → σ.⁻¹ Y
                    ;  nat = λ {Y} {Y'} g → 𝔻.iso-sq (σ.isisopair Y) (σ.isisopair Y') (nat g)
                    }
                   where open natural-transformation σnat



    τnat : natural-transformation (invF ○ F) IdF
    τnat = record
      { fnc = λ {X} → τ X
      ; nat = λ {X} {X'} f →
            faith-pf (~proof F.ₐ (τ X' ℂ.∘ invFₐ (F.ₐ f))                           ~[ F.∘ax-rfˢ ] /
                             F.ₐ (τ X') 𝔻.∘ F.ₐ (invFₐ (F.ₐ f))                     ~[ ∘e full-pf full-pf ] /
                             σ (F.ₒ X') 𝔻.∘ σ.⁻¹ (F.ₒ X') 𝔻.∘ F.ₐ f 𝔻.∘ σ (F.ₒ X)   ~[ ass ⊙ lidgg r (σ.idcod (F.ₒ X')) ] /
                             F.ₐ f 𝔻.∘ σ (F.ₒ X)                                   ~[ ∘e (full-pf ˢ) r ⊙ F.∘ax-rf ]∎
                             F.ₐ (f ℂ.∘ τ X)                                   ∎)
      }
      where open ecategory-aux-only 𝔻


    τ⁻¹nat : natural-transformation IdF (invF ○ F)
    τ⁻¹nat = record { fnc = λ {X} → τ⁻¹ X
                    ; nat = λ {X} {X'} f → ℂ.iso-sq (τ-isopair X) (τ-isopair X') (nat f)
                    }
                    where open natural-transformation τnat


    eqv : is-equivalence-pair F invF
    eqv = record
      { ι1 = record { natt = σnat
                    ; natt⁻¹ = σ⁻¹nat
                    ; isiso = record
                            { iddom = σ.iddom _
                            ; idcod = σ.idcod _
                            }
                    }
      ; ι2 = record { natt = τnat
                    ; natt⁻¹ = τ⁻¹nat
                    ; isiso = record
                            { iddom = τ⁻¹τ=id _
                            ; idcod = ττ⁻¹=id _
                            }
                    }
      }
  -- end eeqv-is-eqv
-- end efunctor-props


ess-equiv-is-equiv : {ℂ 𝔻 : ecategory} {F : efunctor ℂ 𝔻}
                        → is-ess-equivalence F → is-equivalence F
ess-equiv-is-equiv {F = F} eeqv = record
  { invF = invF
  ; iseqv = eqv
  }
  where open efunctor-props F
        open eeqv-is-eqv eeqv
