
{-# OPTIONS --without-K #-}

module ecats.functors.props.basic-props where

open import ecats.basic-defs.ecat-def&not
open import ecats.basic-defs.all-arrows
open import ecats.basic-props.all
open import ecats.finite-limits.all
open import ecats.functors.defs.efunctor-d&n
open import ecats.functors.defs.natural-transformation
open import ecats.functors.defs.basic-defs
open import ecats.functors.defs.preserving-functor
open import ecats.functors.defs.left-covering



module efunctor-basic-props {ℂ 𝔻 : ecategory} (F : efunctor ℂ 𝔻) where
  private
    module macros (𝕏 : ecategory) where
        open ecategory-aux 𝕏 public
        open arrows-defs 𝕏 public
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
          open ecategory-aux 𝔻 using (_⊙_)

  ᵢₛₒ : {A B : ℂ.Obj}{f : || ℂ.Hom A B ||}{f' : || ℂ.Hom B A ||}
           → ℂ.is-iso-pair f f' → 𝔻.is-iso-pair (F.ₐ f) (F.ₐ f')
  ᵢₛₒ = Fiso

  Fpres-iso : {A B : ℂ.Obj} {f : || ℂ.Hom A B ||}
                 → ℂ.is-iso f → 𝔻.is-iso (F.ₐ f)
  Fpres-iso isof = record
    { invf = F.ₐ invf
    ; isisopair = Fiso isisopair
    }
    where open ℂ.is-iso isof

  Fpres-natt : {𝔹 : ecategory}{H K : efunctor 𝔹 ℂ}(α : natural-transformation H K)
                  → natural-transformation (F ○ H) (F ○ K)
  Fpres-natt {𝔹} {H} {K} α = record
    { fnc = λ {B} → F.ₐ (α.fnc {B})
    ; nat = λ f → F.∘∘ (α.nat f)
    }
    where module α = natural-transformation α

  Fridx-natt : {𝔼 : ecategory}{H K : efunctor 𝔻 𝔼}(α : natural-transformation H K)
                  → natural-transformation (H ○ F) (K ○ F)
  Fridx-natt {𝔹} {H} {K} α = record
    { fnc = λ {A} → α.fnc {F.ₒ A}
    ; nat = λ f → α.nat (F.ₐ f)
    }
    where module α = natural-transformation α

  ₙₜ : {𝔹 : ecategory}{H K : efunctor 𝔹 ℂ}(α : natural-transformation H K)
                  → natural-transformation (F ○ H) (F ○ K)
  ₙₜ = Fpres-natt

  ⋆ₙₜ : {𝔼 : ecategory}{H K : efunctor 𝔻 𝔼}(α : natural-transformation H K)
                  → natural-transformation (H ○ F) (K ○ F)
  ⋆ₙₜ = Fridx-natt
  
-- end efunctor-basic-props

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


module efunctor-props {ℂ 𝔻 : ecategory}(F : efunctor ℂ 𝔻) where
  open efunctor-basic-props F public
  open efunctor-preslim2lcov F public
-- end efunctor-props


-- Essential equivalences are equivalences

module eeqv-is-eqv {ℂ 𝔻 : ecategory}{F : efunctor ℂ 𝔻}(eeqv : is-ess-equivalence F) where
  open is-ess-equivalence eeqv
  open is-full isfull
  open is-faithful isfaithful
  private
    module macros (𝕏 : ecategory) where
        open ecategory 𝕏 public
        open arrows-defs 𝕏 public
        --open finite-limits 𝕏 public
        --open finite-weak-limits 𝕏 public
    module ℂ = macros ℂ
    module 𝔻 = macros 𝔻
    module F = efunctor-aux F
    module essrj = is-ess-surjective-ob isesurjobj

  invFₒ : 𝔻.Obj → ℂ.Obj
  invFₒ = essrj.ob
  γ : (Y : 𝔻.Obj) → || 𝔻.Hom (F.ₒ (invFₒ Y)) Y ||
  γ = essrj.ar
  private
    module γ (Y : 𝔻.Obj) = 𝔻.is-iso (essrj.iso Y)
  --open γ-tmp renaming (invf to γ⁻¹; isisopair to γ-isopair; iddom to γ⁻¹γ=id; idcod to γγ⁻¹=id)

  invFₐ : {Y Y' : 𝔻.Obj} → || 𝔻.Hom Y Y' || → || ℂ.Hom (invFₒ Y) (invFₒ Y') ||
  invFₐ {Y} {Y'} g = full-ar (γ.⁻¹ Y' 𝔻.∘ g 𝔻.∘ γ Y)

  δ : (X : ℂ.Obj) → || ℂ.Hom (invFₒ (F.ₒ X)) X ||
  δ X = full-ar (γ (F.ₒ X))
  δ⁻¹ : (X : ℂ.Obj) → || ℂ.Hom X (invFₒ (F.ₒ X)) ||
  δ⁻¹ X = full-ar (γ.⁻¹ (F.ₒ X))
  δ-isopair : (X : ℂ.Obj) → ℂ.is-iso-pair (δ X) (δ⁻¹ X)
  δ-isopair X = record
    { iddom = faith-pf (~proof F.ₐ (δ⁻¹ X ℂ.∘ δ X)               ~[ F.∘ax-rfˢ ] /
                               F.ₐ (δ⁻¹ X) 𝔻.∘ F.ₐ (δ X)          ~[ ∘e full-pf full-pf ] /
                               γ.⁻¹ (F.ₒ X) 𝔻.∘ γ (F.ₒ X)          ~[ γ.iddom (F.ₒ X) ⊙ F.idˢ ]∎
                               F.ₐ (ℂ.idar (invFₒ (F.ₒ X)))      ∎)
    ; idcod = faith-pf (~proof F.ₐ (δ X ℂ.∘ δ⁻¹ X)               ~[ F.∘ax-rfˢ ] /
                               F.ₐ (δ X) 𝔻.∘ F.ₐ (δ⁻¹ X)          ~[ ∘e full-pf full-pf ] /
                               γ (F.ₒ X) 𝔻.∘ γ.⁻¹ (F.ₒ X)          ~[ γ.idcod (F.ₒ X) ⊙ F.idˢ ]∎
                               F.ₐ (ℂ.idar X)                  ∎)
    }
    where open ecategory-aux-only 𝔻
  private module δ-tmp (X : ℂ.Obj) = ℂ.is-iso-pair (δ-isopair X)
  open δ-tmp renaming (iddom to δ⁻¹δ=id; idcod to δδ⁻¹=id)

  invF : efunctor 𝔻 ℂ
  invF = record
       { FObj = invFₒ
       ; FHom = invFₐ
       ; isF = record
             { ext = λ {Y} {Y'} {g} {g'} pf → faith-pf (~proof
                   F.ₐ (invFₐ g)                       ~[ full-pf ] /
                   γ.⁻¹ Y' 𝔻.∘ g 𝔻.∘ γ Y              ~[ ∘e (∘e r pf) r ] /
                   γ.⁻¹ Y' 𝔻.∘ g' 𝔻.∘ γ Y             ~[ full-pf ˢ ]∎
                   F.ₐ (invFₐ g')         ∎)
             ; id = λ {Y} → faith-pf (~proof
                  F.ₐ (invFₐ (𝔻.idar Y))              ~[ full-pf ] /
                  γ.⁻¹ Y 𝔻.∘ (𝔻.idar Y) 𝔻.∘ γ Y      ~[ ∘e lid r ⊙ γ.iddom Y ⊙ F.idˢ ]∎
                  F.ₐ (ℂ.idar (invFₒ Y))          ∎)
             ; cmp = λ {Y₁} {Y₂} {Y₃} g₁ g₂ → faith-pf (~proof
                   F.ₐ (invFₐ g₂ ℂ.∘ invFₐ g₁)                                 ~[ F.∘ax-rfˢ ] /
                   F.ₐ (invFₐ g₂) 𝔻.∘ F.ₐ (invFₐ g₁)                          ~[ ∘e full-pf full-pf ] /
                   (γ.⁻¹ Y₃ 𝔻.∘ g₂ 𝔻.∘ γ Y₂) 𝔻.∘ (γ.⁻¹ Y₂ 𝔻.∘ g₁ 𝔻.∘ γ Y₁)  ~[ assˢ ⊙ ∘e ass r ] /
                   γ.⁻¹ Y₃ 𝔻.∘ ((g₂ 𝔻.∘ γ Y₂) 𝔻.∘ γ.⁻¹ Y₂) 𝔻.∘ g₁ 𝔻.∘ γ Y₁  ~[ ∘e (∘e r (assˢ ⊙ ridgg r (γ.idcod Y₂))) r ] /
                   γ.⁻¹ Y₃ 𝔻.∘ g₂ 𝔻.∘ g₁ 𝔻.∘ γ Y₁                            ~[ ∘e ass r ⊙ full-pf ˢ ]∎
                   F.ₐ (invFₐ (g₂ 𝔻.∘ g₁))                             ∎)
             }
       }
       where open ecategory-aux-only 𝔻

  γnat : natural-transformation (F ○ invF) IdF
  γnat = record
    { fnc = λ {Y} → γ Y
    ; nat = λ {Y} {Y'} g → ~proof γ Y' 𝔻.∘ F.ₐ (invFₐ g)           ~[ ∘e full-pf r ⊙ ass ] /
                                   (γ Y' 𝔻.∘ γ.⁻¹ Y') 𝔻.∘ g 𝔻.∘ γ Y   ~[ lidgg r (γ.idcod Y') ]∎
                                   g 𝔻.∘ γ Y                      ∎
    }
    where open ecategory-aux-only 𝔻
  γ⁻¹nat : natural-transformation IdF (F ○ invF)
  γ⁻¹nat = record { fnc = λ {Y} → γ.⁻¹ Y
                  ;  nat = λ {Y} {Y'} g → 𝔻.invIsNat (γ.isisopair Y) (γ.isisopair Y') (nat g)
                  }
                 where open natural-transformation γnat

  δnat : natural-transformation (invF ○ F) IdF
  δnat = record
    { fnc = λ {X} → δ X
    ; nat = λ {X} {X'} f →
          faith-pf (~proof F.ₐ (δ X' ℂ.∘ invFₐ (F.ₐ f))                           ~[ F.∘ax-rfˢ ] /
                           F.ₐ (δ X') 𝔻.∘ F.ₐ (invFₐ (F.ₐ f))                     ~[ ∘e full-pf full-pf ] /
                           γ (F.ₒ X') 𝔻.∘ γ.⁻¹ (F.ₒ X') 𝔻.∘ F.ₐ f 𝔻.∘ γ (F.ₒ X)   ~[ ass ⊙ lidgg r (γ.idcod (F.ₒ X')) ] /
                           F.ₐ f 𝔻.∘ γ (F.ₒ X)                                   ~[ ∘e (full-pf ˢ) r ⊙ F.∘ax-rf ]∎
                           F.ₐ (f ℂ.∘ δ X)                                   ∎)
    }
    where open ecategory-aux-only 𝔻
  δ⁻¹nat : natural-transformation IdF (invF ○ F)
  δ⁻¹nat = record { fnc = λ {X} → δ⁻¹ X
                  ; nat = λ {X} {X'} f → ℂ.invIsNat (δ-isopair X) (δ-isopair X') (nat f)
                  }
                  where open natural-transformation δnat


  eqv : is-equivalence-pair F invF
  eqv = record
    { ι1 = record { natt = γnat
                  ; natt⁻¹ = γ⁻¹nat
                  ; isiso = record
                          { iddom = γ.iddom _
                          ; idcod = γ.idcod _
                          }
                  }
    ; ι2 = record { natt = δnat
                  ; natt⁻¹ = δ⁻¹nat
                  ; isiso = record
                          { iddom = δ⁻¹δ=id _
                          ; idcod = δδ⁻¹=id _
                          }
                  }
    }
-- end eeqv-is-eqv

ess-equiv-is-equiv : {ℂ 𝔻 : ecategory} {F : efunctor ℂ 𝔻}
                        → is-ess-equivalence F → is-equivalence F
ess-equiv-is-equiv {F = F} eeqv = record
  { invF = invF
  ; iseqvp = eqv
  }
  where open eeqv-is-eqv eeqv

module equivalence-props {ℂ 𝔻 : ecategory}{F : efunctor ℂ 𝔻}{G : efunctor 𝔻 ℂ}
--{E : efunctor ℂ 𝔻}(eqvE : is-equivalence E)
                         where
  private
    module ℂ where
      open ecategory ℂ public
      open iso-defs ℂ public
      open finite-limits-d&p ℂ public
    module 𝔻 where
      open ecategory 𝔻 public
      open iso-defs 𝔻 public
      open finite-limits-d&p 𝔻 public
    module F where
      open efunctor-aux F public
      open efunctor-basic-props F public
    module G where
      open efunctor-aux G public
      open efunctor-basic-props G public
    module G○F where
      open efunctor-aux (G ○ F) public
      open efunctor-basic-props (G ○ F) public
    module F○G where
      open efunctor-aux (F ○ G) public
      open efunctor-basic-props (F ○ G) public


  eqv-is-adj-eqv-ι1 : is-equivalence-pair F G → is-adj-equivalence-pair F G
  eqv-is-adj-eqv-ι1 eqvp = record
    { ι1 = ι1
    ; ι2 = ιη
    ; trid₁ = η-tr₁
    ; trid₂ = η-tr₂
    }
    where open is-equivalence-pair eqvp
          η-fnc : {A : ℂ.Obj} → || ℂ.Hom A (G.ₒ (F.ₒ A)) ||
          η-fnc {A} = ι2.fnc {G.ₒ (F.ₒ A)} ℂ.∘ G.ₐ (ι1.fnc⁻¹ {F.ₒ A}) ℂ.∘ ι2.fnc⁻¹ {A}
          η : natural-transformation IdF (G ○ F)
          η = record
             { fnc = η-fnc
             ; nat = λ {A} {B} f → ~proof
                   η-fnc ℂ.∘ f              ~[ assˢ ⊙ ∘e (assˢ ⊙ ∘e (ι2.natt⁻¹.nat f) r) r ] /
                   ι2.fnc {G.ₒ (F.ₒ B)} ℂ.∘ G.ₐ (ι1.fnc⁻¹ {F.ₒ B}) ℂ.∘ G○F.ₐ f ℂ.∘ ι2.fnc⁻¹ {A}
                                            ~[ ∘e (ass ⊙ ∘e r (G.∘∘ (ι1.natt⁻¹.nat (F.ₐ f))) ⊙ assˢ) r ] /
                   ι2.fnc {G.ₒ (F.ₒ B)} ℂ.∘ G.ₐ (F○G.ₐ (F.ₐ f)) ℂ.∘ G.ₐ (ι1.fnc⁻¹ {F.ₒ A}) ℂ.∘ ι2.fnc⁻¹ {A}
                                            ~[ ass ⊙ ∘e r (ι2.natt.nat (G○F.ₐ f)) ⊙ assˢ ]∎
                   G○F.ₐ f ℂ.∘ η-fnc ∎
             }
             where open ecategory-aux-only ℂ
          module η = natural-transformation η
          
          η⁻¹-fnc : {A : ℂ.Obj} → || ℂ.Hom (G.ₒ (F.ₒ A)) A ||
          η⁻¹-fnc {A} = ι2.fnc {A} ℂ.∘ G.ₐ (ι1.fnc {F.ₒ A}) ℂ.∘ ι2.fnc⁻¹ {G.ₒ (F.ₒ A)}
          ηiso : (A : ℂ.Obj) → ℂ.is-iso-pair (η.fnc {A}) (η⁻¹-fnc {A})
          ηiso A = ℂ.iso-pair-tricmp (ℂ.inv-iso-pair (ι2.isiso {A}))
                                       (G.ᵢₛₒ (𝔻.inv-iso-pair ι1.isiso))
                                       (ι2.isiso {G.ₒ (F.ₒ A)})
          η⁻¹ : natural-transformation (G ○ F) IdF
          η⁻¹ = record
            { fnc = η⁻¹-fnc
            ; nat = λ f → ℂ.invIsNat (ηiso _) (ηiso _) (η.nat f)
            }
          --module η⁻¹ = natural-transformation η⁻¹
          ιη : natural-iso (G ○ F) IdF
          ιη = record
             { natt = η⁻¹
             ; natt⁻¹ = η
             ; isiso = λ {A} → ℂ.inv-iso-pair (ηiso A)
             }
          module ιη = natural-iso ιη
            
          η-tr₂ : {B : 𝔻.Obj} → G.ₐ ι1.fnc ℂ.∘ η.fnc {G.ₒ B} ℂ.~ ℂ.idar (G.ₒ B)
          η-tr₂ {B} = ~proof
            G.ₐ ι1.fnc ℂ.∘ ι2.fnc {G○F.ₒ (G.ₒ B)} ℂ.∘ G.ₐ (ι1.fnc⁻¹ {F.ₒ (G.ₒ B)}) ℂ.∘ ι2.fnc⁻¹ {G.ₒ B}
                       ~[ ass ⊙ ∘e r (ι2.natt.nat (G.ₐ ι1.fnc) ˢ) ⊙ assˢ ] /
            ι2.fnc {G.ₒ B} ℂ.∘ G.ₐ (F○G.ₐ ι1.fnc) ℂ.∘  G.ₐ (ι1.fnc⁻¹ {F.ₒ (G.ₒ B)}) ℂ.∘ ι2.fnc⁻¹ {G.ₒ B}
                       ~[ ∘e (ass ⊙ ∘e r (G.∘∘ (ι1.natt⁻¹.nat ι1.fnc) ˢ)) r ] /
            ι2.fnc {G.ₒ B} ℂ.∘ (G.ₐ (ι1.fnc⁻¹ {B}) ℂ.∘ G.ₐ ι1.fnc) ℂ.∘ ι2.fnc⁻¹ {G.ₒ B}
                       ~[ ∘e (lidgg r (G.∘ax ι1.iddom ⊙ G.id)) r ] /
            ι2.fnc {G.ₒ B} ℂ.∘ ι2.fnc⁻¹ {G.ₒ B}          ~[ ι2.idcod ]∎
            ℂ.idar (G.ₒ B) ∎
            where open ecategory-aux-only ℂ
            -- η-unv-uq (ridgg r F.id) ˢ
                    --using (_ˢ)
                          --open ecategory-aux-only 𝔻 using (r; ridgg)
          ηG-inv : {B : 𝔻.Obj} → η.fnc {G.ₒ B} ℂ.~ G.ₐ ι1.fnc⁻¹
          ηG-inv {B} = lidggˢ r Gι1.iddom ⊙ assˢ ⊙ ridgg r (η-tr₂ {B})
                     where open ecategory-aux-only ℂ
                           module Gι1 = ℂ.is-iso-pair (G.ᵢₛₒ ι1.isiso)
          η-tr₁ : {A : ℂ.Obj} → ι1.fnc {F.ₒ A} 𝔻.∘ F.ₐ (η.fnc {A}) 𝔻.~ 𝔻.idar (F.ₒ A)
          η-tr₁ {A} = ~proof
            ι1.fnc {F.ₒ A} 𝔻.∘ F.ₐ (η.fnc {A})
                           ~[ ∘e (lidggˢ r (F.∘ax (G○F.∘ax ι2.idcod) ⊙ F.idax G○F.id) ⊙ assˢ) r ] /
            ι1.fnc {F.ₒ A} 𝔻.∘ F.ₐ (G○F.ₐ ι2.fnc) 𝔻.∘ F.ₐ (G○F.ₐ ι2.fnc⁻¹) 𝔻.∘ F.ₐ (η.fnc {A})
                           ~[ ass ⊙ ∘e (F.∘∘ (η.nat ι2.fnc⁻¹) ˢ) r ] /
            (ι1.fnc {F.ₒ A} 𝔻.∘ F.ₐ (G○F.ₐ ι2.fnc)) 𝔻.∘ F.ₐ (η.fnc {G○F.ₒ A}) 𝔻.∘ F.ₐ ι2.fnc⁻¹
                           ~[ ∘e (∘e r (F.ext ηG-inv)) (ι1.natt.nat (F.ₐ ι2.fnc)) ⊙ assˢ ] /
            F.ₐ ι2.fnc 𝔻.∘ ι1.fnc {F○G.ₒ (F.ₒ A)} 𝔻.∘ F○G.ₐ (ι1.fnc⁻¹ {F.ₒ A}) 𝔻.∘ F.ₐ ι2.fnc⁻¹
                           ~[ ∘e (ass ⊙ ∘e r (ι1.natt.nat ι1.fnc⁻¹)) r ] /
            F.ₐ ι2.fnc 𝔻.∘ (ι1.fnc⁻¹ {F.ₒ A} 𝔻.∘ ι1.fnc {F.ₒ A}) 𝔻.∘ F.ₐ ι2.fnc⁻¹
                           ~[ ∘e (lidgg r ι1.iddom) r ] /
            F.ₐ ι2.fnc 𝔻.∘ F.ₐ ι2.fnc⁻¹ ~[ F.∘ax ι2.idcod ⊙ F.id ]∎
            𝔻.idar (F.ₒ A) ∎
            where open ecategory-aux-only 𝔻

                      
          η-unv-uq : {B : 𝔻.Obj}{A : ℂ.Obj}{f : || 𝔻.Hom (F.ₒ A) B ||}{u : || ℂ.Hom A (G.ₒ B) ||}
                        → ι1.fnc 𝔻.∘ F.ₐ u 𝔻.~ f → u ℂ.~ G.ₐ f ℂ.∘ η.fnc
          η-unv-uq {B} {A} {f} {u} utr = ~proof
            u                                                         ~[ lidggˢ r ι2.idcod ⊙ assˢ ] /
            ι2.fnc {G.ₒ B} ℂ.∘ ι2.fnc⁻¹ {G.ₒ B} ℂ.∘ u                    ~[ ∘e (ι2.natt⁻¹.nat u) r ] /
            ι2.fnc {G.ₒ B} ℂ.∘ G○F.ₐ u ℂ.∘ ι2.fnc⁻¹ {A}
                                        ~[ ∘e (∘e r (G.∘axˢ (𝔻.iso-trcod ι1.isiso utr)) ⊙ assˢ) r ] /
            ι2.fnc {G.ₒ B} ℂ.∘ G.ₐ (ι1.fnc⁻¹ {B}) ℂ.∘ G.ₐ f ℂ.∘ ι2.fnc⁻¹ {A}
                                             ~[ ∘e (ass ⊙ ∘e r (G.∘∘ (ι1.natt⁻¹.nat f)) ⊙ assˢ) r ] /
            ι2.fnc {G.ₒ B} ℂ.∘ G.ₐ (F○G.ₐ f) ℂ.∘  G.ₐ (ι1.fnc⁻¹ {F.ₒ A}) ℂ.∘ ι2.fnc⁻¹ {A}
                                                      ~[ ass ⊙ ∘e r (ι2.natt.nat (G.ₐ f)) ⊙ assˢ ]∎
            G.ₐ f ℂ.∘ ι2.fnc {G○F.ₒ A} ℂ.∘ G.ₐ (ι1.fnc⁻¹ {F.ₒ A}) ℂ.∘ ι2.fnc⁻¹ {A} ∎
            where open ecategory-aux-only ℂ
            
          {- η' consists also of 4 identity arrows corresponding to 2 lid and 2 ass.
          η' : natural-transformation IdF (G ○ F)
          η' = natt-vcmp ○lid.natt (natt-vcmp (G○F.⋆ₙₜ ι2.natt)
                                             (natt-vcmp ass-aux
                                                        (natt-vcmp (G.ₙₜ (F.⋆ₙₜ ι1.natt⁻¹))
                                                                   (natt-vcmp (G.ₙₜ (○lid.natt⁻¹ {K = F}))
                                                                              ι2.natt⁻¹))))
            where module ○lid {𝕏 𝕐 : ecategory}{K : efunctor 𝕏 𝕐}
                                 = natural-iso (○lid {𝕏} {𝕐} {K})
                  module ○ass {𝕏 𝕐 𝕍 ℤ : ecategory}{K₁ : efunctor 𝕏 𝕐}{K₂ : efunctor 𝕐 𝕍}{K₃ : efunctor 𝕍 ℤ}
                                 = natural-iso (○ass {𝕏} {𝕐} {𝕍} {ℤ} {K₁} {K₂} {K₃})
                  ass-aux : G ○ (F ○ G) ○ F ⇒ (G ○ F) ○ G ○ F
                  ass-aux = natt-vcmp (○ass.natt {K₁ = G ○ F} {K₂ = F} {K₃ = G})
                                      (G.ₙₜ (○ass.natt⁻¹ {K₁ = F} {K₂ = G} {K₃ = F}))
          -}


{-
  module pres-term (Eadj : is-adj-equivalence-pair E.iseqvp){X : ℂ.Obj}(Xtrm : ℂ.is-terminal X) where
    private
      module X = ℂ.is-terminal Xtrm

    EXtrm : 𝔻.is-terminal (E.ₒ X)
    EXtrm = record
      { ! = λ B → E.ₐ (X.! (E.inv.ₒ B)) 𝔻.∘ E.ι1.fnc⁻¹ {B}
      ; !uniq = λ {B} f → ~proof
              f                                             ~[ lidggˢ r (Eadj.trid⁻¹₁ {X}) ⊙ assˢ ] /
              -- need to have an adjoint equivalence?
              E.ₐ (E.ι2.fnc {X}) 𝔻.∘ E.ι1.fnc⁻¹ {E.ₒ X} 𝔻.∘ f             ~[ ∘e (E.ι1.nat⁻¹ f) r ] /
              E.ₐ (E.ι2.fnc {X}) 𝔻.∘ E.ₐ (E.inv.ₐ f) 𝔻.∘ E.ι1.fnc⁻¹ {B}   ~[ ass ⊙ ∘e r E.∘ax-rf ] /
              E.ₐ (E.ι2.fnc {X} ℂ.∘ E.inv.ₐ f) 𝔻.∘ E.ι1.fnc⁻¹ {B}
                                            ~[ ∘e r (E.ext (X.!uniq (E.ι2.fnc {X} ℂ.∘ E.inv.ₐ f))) ]∎
              E.ₐ (X.! (E.inv.ₒ B)) 𝔻.∘ E.ι1.fnc⁻¹ {B} ∎
      }
      where open ecategory-aux-only 𝔻
            module Eadj = is-adj-equivalence-pair Eadj
  --end pres-term
  
  pres-term : is-adj-equivalence-pair E.iseqvp → preserves-terminal E
  pres-term Eadj = record
    { pres-!-pf = pres-term.EXtrm Eadj 
    }
-}

-- end equivalence-props
