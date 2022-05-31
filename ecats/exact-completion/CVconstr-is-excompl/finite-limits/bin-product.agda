
{-# OPTIONS --without-K #-}

module ecats.exact-completion.CVconstr-is-excompl.finite-limits.bin-product where

open import ecats.basic-defs.ecat-def&not
open import ecats.basic-defs.commut-shapes
open import ecats.basic-defs.epi&mono
open import ecats.basic-defs.eqv-rel
open import ecats.finite-limits.defs.collective
open import ecats.finite-limits.d&n-bin-weak-product
open import ecats.finite-limits.d&n-weak-pullback
open import ecats.finite-limits.d&n-bin-product
open import ecats.exact-completion.CVconstruction
open import ecats.exact-completion.CVconstr-is-excompl.exact.canonical-epi&mono



-- Binary products

module exact-compl-has-bin-products {ℂ : ecategory} (hasfwl : has-fin-weak-limits ℂ)  where
  private
    module ℂ where
      open ecategory ℂ public
      open comm-shapes ℂ public
      open pseudo-eq-rel-defs ℂ public
      open binary-wproducts ℂ public
      open wpullback-squares ℂ public
    module fwlℂ where
      open has-fin-weak-limits hasfwl public
      open has-bin-weak-products haswprd public using (wprd-of)
      open has-weak-pullbacks haswpb public using (wpb-of)
    module Exℂ where
      open ecategory Ex ℂ [ hasfwl ] public
      open comm-shapes Ex ℂ [ hasfwl ] public
      open epi&mono-defs Ex ℂ [ hasfwl ] public
      open binary-products Ex ℂ [ hasfwl ] public
    infixr 2  _~_
    infixr 5 _∘_
    _~_ : {A B : ℂ.Obj} (f f' : || ℂ.Hom A B ||) → Set
    _~_ =  ℂ._~_
    _∘_ : {A B C : ℂ.Obj} →  || ℂ.Hom B C ||  → || ℂ.Hom A B || → || ℂ.Hom A C ||
    _∘_ = ℂ._∘_

  module peq-product (R S : ℂ.peq) where
    --open ecategory-aux-only ℂ
    open bin-wproducts-aux fwlℂ.haswprd using (_w×ₐ_)
    open can-epi&mono-defs hasfwl
    private
      module R = ℂ.peq R
      module S = ℂ.peq S
      module Rτ = ℂ.wpullback-of-not R.τwpb
      module Sτ = ℂ.wpullback-of-not S.τwpb
      Lo[R×S] : ℂ.wproduct-of R.Lo S.Lo
      Lo[R×S] = fwlℂ.wprd-of R.Lo S.Lo
      module Lo[R×S] = ℂ.wproduct-of-not Lo[R×S]
      module Hisp where
        open canonical-mono-sp R.peqover S.peqover (ℂ.mkspan/ Lo[R×S].wπ₁ Lo[R×S].wπ₂)
        open Exℂ.span/ cmsp public
        open is-Ex-monic-sp cmsp-is-Ex-monic public
        open Exℂ.is-jointly-monic/ cmsp-is-jm/ public
      module π₁ = ℂ.peq-mor Hisp.a1
      module π₂ = ℂ.peq-mor Hisp.a2

    peq-prd : Exℂ.Obj
    peq-prd = Hisp.O12
    peq-π₁ : || Exℂ.Hom peq-prd R ||
    peq-π₁ = Hisp.a1
    peq-π₂ : || Exℂ.Hom peq-prd S ||
    peq-π₂ = Hisp.a2

    peq-<> : {T : ℂ.peq} → || Exℂ.Hom T R || → || Exℂ.Hom T S || → || Exℂ.Hom T peq-prd ||
    peq-<> {T} f g = record
      { lo = Lo[R×S].w< f.lo , g.lo >
      ; isext = record
        { hi = hiun
        ; cmptb₀ = R×Sob.%0 ∘ hiun                   ~[ Hisp.trl₀ hiun₁₀ hiun₁₁ hiun₂₀ hiun₂₁ ]
                   Lo[R×S].w< f.lo , g.lo > ∘ T.%0
        ; cmptb₁ = R×Sob.%1 ∘ hiun                   ~[ Hisp.trl₁ hiun₁₀ hiun₁₁ hiun₂₀ hiun₂₁ ]
                   Lo[R×S].w< f.lo , g.lo > ∘ T.%1
        }
      }
      where open ecategory-aux-only ℂ
            module R×Sob = ℂ.peq peq-prd
            module T = ℂ.peq T
            module f = ℂ.peq-mor f
            module g = ℂ.peq-mor g
            hiun₁₀ = π₁.lo ∘ Lo[R×S].w< f.lo , g.lo > ∘ T.%0
                     ~[ ass ⊙ ∘e r Lo[R×S].w×tr₁ ⊙ f.cmptb₀ ˢ ]
                     R.%0 ∘ f.hi
            hiun₁₁ = π₁.lo ∘ Lo[R×S].w< f.lo , g.lo > ∘ T.%1
                     ~[ ass ⊙ ∘e r Lo[R×S].w×tr₁ ⊙ f.cmptb₁ ˢ ]
                     R.%1 ∘ f.hi
            hiun₂₀ = π₂.lo ∘ Lo[R×S].w< f.lo , g.lo > ∘ T.%0
                     ~[ ass ⊙ ∘e r Lo[R×S].w×tr₂ ⊙ g.cmptb₀ ˢ ]
                     S.%0 ∘ g.hi
            hiun₂₁ = π₂.lo ∘ Lo[R×S].w< f.lo , g.lo > ∘ T.%1
                     ~[ ass ⊙ ∘e r Lo[R×S].w×tr₂ ⊙ g.cmptb₁ ˢ ]
                     S.%1 ∘ g.hi
            hiun : || ℂ.Hom T.Hi R×Sob.Hi ||
            hiun = Hisp.⟨ Lo[R×S].w< f.lo , g.lo > ∘ T.%0 , f.hi , g.hi , Lo[R×S].w< f.lo , g.lo > ∘ T.%1
                        ⟩[ hiun₁₀ , hiun₁₁ , hiun₂₀ , hiun₂₁ ]

    peq-×of : Exℂ.product-of R S
    peq-×of = record
            { ×sp/ = Exℂ.mkspan/ peq-π₁ peq-π₂
            ; ×isprd = record
                     { <_,_> = peq-<>
                     ; ×tr₁ = ℂ.peq-mor-eq-ext Lo[R×S].w×tr₁
                     ; ×tr₂ = ℂ.peq-mor-eq-ext Lo[R×S].w×tr₂
                     ; ×uq = Hisp.jm-pf
                     }
            }
  -- end peq-product

  ex-cmpl-prd : has-bin-products Ex ℂ [ hasfwl ]
  ex-cmpl-prd = record
    { prd-of = peq-×of
    }
    where open peq-product using (peq-×of)

-- end exact-compl-has-bin-products



exact-compl-has-bin-products : {ℂ : ecategory} (hasfwl : has-fin-weak-limits ℂ) → has-bin-products Ex ℂ [ hasfwl ]
exact-compl-has-bin-products {ℂ} hasfwl = ex-cmpl-prd
                                        where open exact-compl-has-bin-products {ℂ} hasfwl using (ex-cmpl-prd)



exact-compl-qcart-has-bin-products : {ℂ : ecategory} (qcart : is-quasi-cartesian ℂ) → has-bin-products Ex ℂ qc[ qcart ]
exact-compl-qcart-has-bin-products qcart = exact-compl-has-bin-products (qcart→has-fwlim qcart)









-- The following is actually the choice of binary products given by Γₑₓ ℂ [ qcart ]


-- module exact-compl-qcart-has-bin-products {ℂ : ecategory} (qcart : is-quasi-cartesian ℂ)  where
--   private
--     module ℂ where
--       open ecategory ℂ public
--       open pseudo-eq-rel-defs ℂ public
--       open wpullback-squares ℂ public
--       open binary-products ℂ public
--     module qcℂ where
--       open is-quasi-cartesian qcart public
--       open has-bin-products hasprd public using (prd-of)
--       open has-weak-pullbacks haswpb public using (wpb-of)
--     module Exℂ where
--       open ecategory Ex ℂ qc[ qcart ] public
--       open comm-shapes Ex ℂ qc[ qcart ] public
--       open binary-products Ex ℂ qc[ qcart ] public
--     infixr 2  _~_
--     infixr 5 _∘_
--     _~_ : {A B : ℂ.Obj} (f f' : || ℂ.Hom A B ||) → Set
--     _~_ =  ℂ._~_
--     _∘_ : {A B C : ℂ.Obj} →  || ℂ.Hom B C ||  → || ℂ.Hom A B || → || ℂ.Hom A C ||
--     _∘_ = ℂ._∘_


--   module peq-product (R S : ℂ.peq) where
--     --open ecategory-aux-only ℂ
--     open bin-products-aux qcℂ.hasprd using (_×ₐ_)
--     private
--       module R = ℂ.peq R
--       module S = ℂ.peq S
--       module Rτ = ℂ.wpullback-of-not R.τwpb
--       module Sτ = ℂ.wpullback-of-not S.τwpb
--       Lo[R×S] : ℂ.product-of R.Lo S.Lo
--       Lo[R×S] = qcℂ.prd-of R.Lo S.Lo
--       Hi[R×S] : ℂ.product-of R.Hi S.Hi
--       Hi[R×S] = qcℂ.prd-of R.Hi S.Hi
--       module Lo[R×S] = ℂ.product-of-not Lo[R×S]
--       module Hi[R×S] = ℂ.product-of-not Hi[R×S]
--       module ×lhl where
--         open ℂ.×ₐnot2-only Lo[R×S].prdsp Hi[R×S].prdsp public
--         open ℂ.×ₐnot3-only Lo[R×S].prdsp Hi[R×S].prdsp Lo[R×S].prdsp public
--       module ×hhl where
--         open ℂ.×ₐnot2-only Hi[R×S].prdsp Hi[R×S].prdsp public
--         open ℂ.×ₐnot3-only Lo[R×S].prdsp Hi[R×S].prdsp Hi[R×S].prdsp public
--     -- TO DO: write R×Sτ as a product of the weak pullbacks R.τwpb and S.τwpb
--     R×Sτ : ℂ.wpullback-of (R.%1 ×ₐ S.%1) (R.%0 ×ₐ S.%0)
--     R×Sτ = qcℂ.wpb-of (R.%1 ×ₐ S.%1) (R.%0 ×ₐ S.%0)
--     private
--       module R×Sτ = ℂ.wpullback-of R×Sτ

--     peq-prd : ℂ.peq
--     peq-prd = record
--       { Lo = Lo[R×S].O12
--       ; peqover = record { Hi = Hi[R×S].O12
--                          ; %0 = R.%0 ×ₐ S.%0
--                          ; %1 = R.%1 ×ₐ S.%1
--                          ; ispeq = record
--                                  { isρ = record
--                                  { ρ = R.ρ ×ₐ S.ρ
--                                  ; ρ-ax₀ = ×lhl.×ₐ×ₐ~ar (lidggˢ rid R.ρ-ax₀)
--                                                         (lidggˢ rid S.ρ-ax₀)
--                                  ; ρ-ax₁ = ×lhl.×ₐ×ₐ~ar (lidggˢ rid R.ρ-ax₁)
--                                                         (lidggˢ rid S.ρ-ax₁)
--                                  }
--                                  ; isσ = record
--                                  { σ = R.σ ×ₐ S.σ
--                                  ; σ-ax₀ = ×hhl.×ₐ×ₐ~×ₐ R.σ-ax₀  S.σ-ax₀
--                                  ; σ-ax₁ = ×hhl.×ₐ×ₐ~×ₐ R.σ-ax₁ S.σ-ax₁
--                                  }
--                                  ; iswτ = record
--                                  { τwpb = R×Sτ
--                                  ; τ = τRS
--                                  ; τ-ax₀ = τRS-ax₀
--                                  ; τ-ax₁ = τRS-ax₁
--                                  }
--                                  }
--                          }
--       }
--       where open ecategory-aux-only ℂ
--             commsqR : R.%1 ∘ Hi[R×S].π₁ ∘ R×Sτ.wπ/₁ ~ R.%0 ∘ Hi[R×S].π₁ ∘ R×Sτ.wπ/₂
--             commsqR = ~proof
--                       R.%1 ∘ Hi[R×S].π₁ ∘ R×Sτ.wπ/₁              ~[ ass ⊙ ∘e r Lo[R×S].×tr₁ˢ ⊙ assˢ ] /
--                       Lo[R×S].π₁ ∘ (R.%1 ×ₐ S.%1) ∘ R×Sτ.wπ/₁    ~[ ∘e R×Sτ.w×/sqpf r ] /
--                       Lo[R×S].π₁ ∘ (R.%0 ×ₐ S.%0) ∘ R×Sτ.wπ/₂    ~[ ass ⊙ ∘e r Lo[R×S].×tr₁ ⊙ assˢ ]∎
--                       R.%0 ∘ Hi[R×S].π₁ ∘ R×Sτ.wπ/₂ ∎
--             commsqS : S.%1 ∘ Hi[R×S].π₂ ∘ R×Sτ.wπ/₁ ~ S.%0 ∘ Hi[R×S].π₂ ∘ R×Sτ.wπ/₂
--             commsqS = ~proof
--                       S.%1 ∘ Hi[R×S].π₂ ∘ R×Sτ.wπ/₁              ~[ ass ⊙ ∘e r Lo[R×S].×tr₂ˢ ⊙ assˢ ] /
--                       Lo[R×S].π₂ ∘ (R.%1 ×ₐ S.%1) ∘ R×Sτ.wπ/₁    ~[ ∘e R×Sτ.w×/sqpf r ] /
--                       Lo[R×S].π₂ ∘ (R.%0 ×ₐ S.%0) ∘ R×Sτ.wπ/₂    ~[ ass ⊙ ∘e r Lo[R×S].×tr₂ ⊙ assˢ ]∎
--                       S.%0 ∘ Hi[R×S].π₂ ∘ R×Sτ.wπ/₂ ∎          
--             prR : || ℂ.Hom R×Sτ.ul Rτ.ul ||
--             prR = Rτ.w⟨ Hi[R×S].π₁ ∘ R×Sτ.wπ/₁ , Hi[R×S].π₁ ∘ R×Sτ.wπ/₂ ⟩[ commsqR ]
--             prS : || ℂ.Hom R×Sτ.ul Sτ.ul ||
--             prS = Sτ.w⟨ Hi[R×S].π₂ ∘ R×Sτ.wπ/₁ , Hi[R×S].π₂ ∘ R×Sτ.wπ/₂ ⟩[ commsqS ]

--             τRS : || ℂ.Hom R×Sτ.ul Hi[R×S].O12 ||
--             τRS = Hi[R×S].< R.τ ∘ prR , S.τ ∘ prS >
--             τRS-ax₀ = ~proof
--               (R.%0 ×ₐ S.%0) ∘ τRS      ~[ Lo[R×S].<>ar~<> (assˢ ⊙ ∘e Hi[R×S].×tr₁ r) (assˢ ⊙ ∘e Hi[R×S].×tr₂ r) ] /
--               Lo[R×S].< R.%0 ∘ R.τ ∘ prR , S.%0 ∘ S.τ ∘ prS >
--                                        ~[ Lo[R×S].<>~<> (ass ⊙ ∘e r R.τ-ax₀ ⊙ assˢ ⊙ ∘e (Rτ.w×/tr₁ commsqR) r)
--                                                         (ass ⊙ ∘e r S.τ-ax₀ ⊙ assˢ ⊙ ∘e (Sτ.w×/tr₁ commsqS) r) ] /
--               Lo[R×S].< R.%0 ∘  Hi[R×S].π₁ ∘ R×Sτ.wπ/₁  , S.%0 ∘  Hi[R×S].π₂ ∘ R×Sτ.wπ/₁ >
--                                        ~[ Lo[R×S].<>ar~<>ˢ assˢ assˢ ]∎
--               (R.%0 ×ₐ S.%0) ∘ R×Sτ.wπ/₁ ∎

--             τRS-ax₁ = ~proof
--               (R.%1 ×ₐ S.%1) ∘ τRS      ~[ Lo[R×S].<>ar~<> (assˢ ⊙ ∘e Hi[R×S].×tr₁ r) (assˢ ⊙ ∘e Hi[R×S].×tr₂ r) ] /
--               Lo[R×S].< R.%1 ∘ R.τ ∘ prR , S.%1 ∘ S.τ ∘ prS >
--                                        ~[ Lo[R×S].<>~<> (ass ⊙ ∘e r R.τ-ax₁ ⊙ assˢ ⊙ ∘e (Rτ.w×/tr₂ commsqR) r)
--                                                         (ass ⊙ ∘e r S.τ-ax₁ ⊙ assˢ ⊙ ∘e (Sτ.w×/tr₂ commsqS) r) ] /
--               Lo[R×S].< R.%1 ∘  Hi[R×S].π₁ ∘ R×Sτ.wπ/₂  , S.%1 ∘  Hi[R×S].π₂ ∘ R×Sτ.wπ/₂ >
--                                         ~[  Lo[R×S].<>ar~<>ˢ assˢ assˢ ]∎
--               (R.%1 ×ₐ S.%1) ∘ R×Sτ.wπ/₂ ∎


--     peq-π₁ : || Exℂ.Hom peq-prd R ||
--     peq-π₁ = record { lo = Lo[R×S].π₁
--                     ; isext = record
--                       { hi = Hi[R×S].π₁
--                       ; cmptb₀ = Lo[R×S].×tr₁ˢ
--                       ; cmptb₁ = Lo[R×S].×tr₁ˢ
--                       }
--                     }

--     peq-π₂ : || Exℂ.Hom peq-prd S ||
--     peq-π₂ = record { lo = Lo[R×S].π₂
--                     ; isext = record
--                       { hi = Hi[R×S].π₂
--                       ; cmptb₀ = Lo[R×S].×tr₂ˢ
--                       ; cmptb₁ = Lo[R×S].×tr₂ˢ
--                       }
--                     }

--     peq-<> : {T : ℂ.peq} → || Exℂ.Hom T R || → || Exℂ.Hom T S || → || Exℂ.Hom T peq-prd ||
--     peq-<> {T} f g = record
--       { lo = Lo[R×S].< f.lo , g.lo >
--       ; isext = record
--         { hi = Hi[R×S].< f.hi , g.hi >
--         ; cmptb₀ = ~proof
--                  (R.%0 ×ₐ S.%0) ∘ Hi[R×S].< f.hi , g.hi >
--                                         ~[ Lo[R×S].<>ar~<> (assˢ ⊙ ∘e Hi[R×S].×tr₁ r) (assˢ ⊙ ∘e Hi[R×S].×tr₂ r) ] /
--                  Lo[R×S].< R.%0 ∘ f.hi , S.%0 ∘ g.hi >         ~[ Lo[R×S].<>ar~<>ˢ (f.cmptb₀ ˢ) (g.cmptb₀ ˢ) ]∎
--                  Lo[R×S].< f.lo , g.lo > ∘ T.%0 ∎
--         ; cmptb₁ = ~proof
--                (R.%1 ×ₐ S.%1) ∘ Hi[R×S].< f.hi , g.hi >
--                                         ~[ Lo[R×S].<>ar~<> (assˢ ⊙ ∘e Hi[R×S].×tr₁ r) (assˢ ⊙ ∘e Hi[R×S].×tr₂ r) ] /
--                Lo[R×S].< R.%1 ∘ f.hi , S.%1 ∘ g.hi >             ~[ Lo[R×S].<>ar~<>ˢ (f.cmptb₁ ˢ) (g.cmptb₁ ˢ) ]∎
--                Lo[R×S].< f.lo , g.lo > ∘ T.%1 ∎
--         }
--       }
--       where open ecategory-aux-only ℂ
--             module T = ℂ.peq T
--             module f = ℂ.peq-mor f
--             module g = ℂ.peq-mor g

--     peq-×of : Exℂ.product-of R S
--     peq-×of = record
--                 { ×sp/ = Exℂ.mkspan/ peq-π₁ peq-π₂
--                 ; ×isprd = record
--                          { <_,_> = peq-<>
--                          ; ×tr₁ = ℂ.peq-mor-eq-ext Lo[R×S].×tr₁
--                          ; ×tr₂ = ℂ.peq-mor-eq-ext Lo[R×S].×tr₂
--                          ; ×uq =  λ pf₁ pf₂ → record
--                                { hty = Hi[R×S].< hty pf₁ , hty pf₂ > 
--                                ; hty₀ = ×lhl.×ₐ<>~ar (hty₀ pf₁ ˢ) (hty₀ pf₂ ˢ)
--                                ; hty₁ = ×lhl.×ₐ<>~ar (hty₁ pf₁ ˢ) (hty₁ pf₂ ˢ)
--                                }
--                          }
--                 }
--                 where open ecategory-aux-only ℂ
--                       open ℂ.peq-mor-eq
--     -- end peq-product

--   ex-cmpl-prd : has-bin-products Ex ℂ qc[ qcart ]
--   ex-cmpl-prd = record
--               { prd-of = peq-×of
--               }
--               where open peq-product using (peq-×of)

-- -- end exact-compl-has-bin-products
