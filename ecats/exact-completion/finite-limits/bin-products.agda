
-- disable the K axiom:

{-# OPTIONS --without-K #-}

-- Agda version 2.5.4.1

module ecats.exact-completion.finite-limits.bin-products where

open import setoids
open import ecats.basic-defs.ecat-def&not
open import ecats.basic-defs.commut-shapes
open import ecats.basic-defs.eqv-rel
open import ecats.finite-limits.defs.collective
open import ecats.finite-limits.d&n-bin-product
open import ecats.finite-limits.d&n-weak-pullback
open import ecats.exact-completion.construction
open import ecats.functors.defs.efunctor



-- Binary products

module exact-compl-has-bin-products {ℂ : ecategory} (qcart : is-quasi-cartesian ℂ)  where
  open ecategory ℂ
  private
    module qcℂ where
      open is-quasi-cartesian qcart public
      open bin-products-aux prd public
      open weak-pullbacks-aux (wpb-aux wpb) public
      open pseudo-eq-rel-defs wpb public
    module Exℂ where
      open ecategory Ex ℂ [ qcart ] public
      open comm-shapes Ex ℂ [ qcart ] public
      open binary-products Ex ℂ [ qcart ] public
  open qcℂ

  Peq-prd : (R S : Peq) → Peq
  Peq-prd R S = record
    { Lo = Lo R × Lo S
    ; peqover = record { Hi = Hi R × Hi S
                       ; %0 = %0 R ×ₐ %0 S
                       ; %1 = %1 R ×ₐ %1 S
                       ; ispeq = record
                               { ρ = ρ R ×ₐ ρ S
                               ; ρ-ax₀ = ×ₐ×ₐ~×ₐ (ρ-ax₀ R) (ρ-ax₀ S) ⊙ ×ₐid r r
                               ; ρ-ax₁ = ×ₐ×ₐ~×ₐ (ρ-ax₁ R) (ρ-ax₁ S) ⊙ ×ₐid r r
                               ; σ = σ R ×ₐ σ S
                               ; σ-ax₀ = ×ₐ×ₐ~×ₐ (σ-ax₀ R) (σ-ax₀ S)
                               ; σ-ax₁ = ×ₐ×ₐ~×ₐ (σ-ax₁ R) (σ-ax₁ S)
                               ; τ = τRS
                               ; τ-ax₀ = τRS-ax₀
                               ; τ-ax₁ = τRS-ax₁
                               }
                       }
    }

{-
-- with the following formulation. Agda takes a lot to normalise ΓFₒ (A × B):
-- reason is that Peq-prd A B gets normalised inside, som k's of lines
                mkpeq-c {Lo R × Lo S} (mkpeq/ {Lo R × Lo S} {Hi R × Hi S} {%0 R ×ₐ %0 S} {%1 R ×ₐ %1 S}
                                              (mkis-peqr {Hi R × Hi S} {Lo R × Lo S} {%0 R ×ₐ %0 S} {%1 R ×ₐ %1 S}
                                                         -- ρ
                                                         (ρ R ×ₐ ρ S)
                                                         (×ₐ×ₐ~×ₐ (ρ-ax₀ R) (ρ-ax₀ S) ⊙ ×ₐid r r)
                                                         (×ₐ×ₐ~×ₐ (ρ-ax₁ R) (ρ-ax₁ S) ⊙ ×ₐid r r)
                                                         -- σ
                                                         (σ R ×ₐ σ S)
                                                         (×ₐ×ₐ~×ₐ (σ-ax₀ R) (σ-ax₀ S))
                                                         (×ₐ×ₐ~×ₐ (σ-ax₁ R) (σ-ax₁ S))
                                                         -- τ
                                                         τRS
                                                         τRS-ax₀
                                                         τRS-ax₁
                                                         ))
-}

    where open ecategory-aux-only ℂ
          open Peq
          commsqR : %1 R ∘ π₁ ∘ wπ/₁ ~ %0 R ∘ π₁ ∘ wπ/₂
          commsqR = ~proof
                    %1 R ∘ π₁ ∘ wπ/₁            ~[ ass ⊙ ∘e r ×tr₁ˢ ⊙ assˢ ] /
                    π₁ ∘ (%1 R ×ₐ %1 S) ∘ wπ/₁  ~[ ∘e w×/sqpf r ] /
                    π₁ ∘ (%0 R ×ₐ %0 S) ∘ wπ/₂  ~[ ass ⊙ ∘e r ×tr₁ ⊙ assˢ ]∎
                    %0 R ∘ π₁ ∘ wπ/₂ ∎
          commsqS : %1 S ∘ π₂ ∘ wπ/₁ ~ %0 S ∘ π₂ ∘ wπ/₂
          commsqS = ~proof
                    %1 S ∘ π₂ ∘ wπ/₁            ~[ ass ⊙ ∘e r ×tr₂ˢ ⊙ assˢ ] /
                    π₂ ∘ (%1 R ×ₐ %1 S) ∘ wπ/₁  ~[ ∘e (w×/sqpf) r ] /
                    π₂ ∘ (%0 R ×ₐ %0 S) ∘ wπ/₂  ~[ ass ⊙ ∘e r ×tr₂ ⊙ assˢ ]∎
                    %0 S ∘ π₂ ∘ wπ/₂ ∎          
          prR : || Hom ((%1 R ×ₐ %1 S) w×/ₒ (%0 R ×ₐ %0 S)) (%1 R w×/ₒ %0 R) ||
          prR = w⟨ π₁ ∘ wπ/₁ , π₁ ∘ wπ/₂ ⟩[ commsqR ]
          prS : || Hom ((%1 R ×ₐ %1 S) w×/ₒ (%0 R ×ₐ %0 S)) (%1 S w×/ₒ %0 S) ||
          prS = w⟨ π₂ ∘ wπ/₁ , π₂ ∘ wπ/₂ ⟩[ commsqS ]
          
          τRS : || Hom ((%1 R ×ₐ %1 S) w×/ₒ (%0 R ×ₐ %0 S)) (Hi R × Hi S) ||
          τRS = < τ R ∘ prR , τ S ∘ prS >
          τRS-ax₀ = ~proof
            (%0 R ×ₐ %0 S) ∘ τRS                      ~[ <>ar~<> (assˢ ⊙ ∘e ×tr₁ r) (assˢ ⊙ ∘e ×tr₂ r) ] /
            < %0 R ∘ τ R ∘ prR , %0 S ∘ τ S ∘ prS >    ~[ <>~<> (ass ⊙ ∘e r (τ-ax₀ R) ⊙ assˢ ⊙ ∘e (w×/tr₁ commsqR) r)
                                                               (ass ⊙ ∘e r (τ-ax₀ S) ⊙ assˢ ⊙ ∘e (w×/tr₁ commsqS) r) ] /
            < %0 R ∘ π₁ ∘ wπ/₁  , %0 S ∘ π₂ ∘ wπ/₁ >   ~[ <>ar~<>ˢ assˢ assˢ ]∎
            (%0 R ×ₐ %0 S) ∘ wπ/₁ ∎

          τRS-ax₁ = ~proof
            (%1 R ×ₐ %1 S) ∘ τRS                       ~[ <>ar~<> (assˢ ⊙ ∘e ×tr₁ r) (assˢ ⊙ ∘e ×tr₂ r) ] /
            < %1 R ∘ τ R ∘ prR , %1 S ∘ τ S ∘ prS >     ~[ <>~<> (ass ⊙ ∘e r (τ-ax₁ R) ⊙ assˢ ⊙ ∘e (w×/tr₂ commsqR) r)
                                                                (ass ⊙ ∘e r (τ-ax₁ S) ⊙ assˢ ⊙ ∘e (w×/tr₂ commsqS) r) ] /
            < %1 R ∘ π₁ ∘ wπ/₂  , %1 S ∘ π₂ ∘ wπ/₂ >    ~[ <>ar~<>ˢ assˢ assˢ ]∎
            (%1 R ×ₐ %1 S) ∘ wπ/₂ ∎


  Peq-π₁ : (R S : Peq) → || Exℂ.Hom (Peq-prd R S) R ||
  Peq-π₁ R S = record { hi = π₁
                      ; lo = π₁
                      ; cmptb₀ = ×tr₁ˢ
                      ; cmptb₁ = ×tr₁ˢ }

  Peq-π₂ : (R S : Peq) → || Exℂ.Hom (Peq-prd R S) S ||
  Peq-π₂ R S = record { hi = π₂
                      ; lo = π₂
                      ; cmptb₀ = ×tr₂ˢ
                      ; cmptb₁ = ×tr₂ˢ }

  Peq-<> : {R S T : Peq} → || Exℂ.Hom T R || → || Exℂ.Hom T S || → || Exℂ.Hom T (Peq-prd R S) ||
  Peq-<> {R} {S} {T} f g = record
    { hi = < hi f , hi g >
    ; lo = < lo f , lo g >
    ; cmptb₀ = ~proof
             (%0 R ×ₐ %0 S) ∘ < hi f , hi g >      ~[ <>ar~<> (assˢ ⊙ ∘e ×tr₁ r) (assˢ ⊙ ∘e ×tr₂ r) ] /
             < %0 R ∘ hi f , %0 S ∘ hi g >         ~[ <>ar~<>ˢ (cmptb₀ f ˢ) (cmptb₀ g ˢ) ]∎
             < lo f , lo g > ∘ %0 T ∎
    ; cmptb₁ = ~proof
         (%1 R ×ₐ %1 S) ∘ < hi f , hi g >          ~[ <>ar~<> (assˢ ⊙ ∘e ×tr₁ r) (assˢ ⊙ ∘e ×tr₂ r) ] /
         < %1 R ∘ hi f , %1 S ∘ hi g >             ~[ <>ar~<>ˢ (cmptb₁ f ˢ) (cmptb₁ g ˢ) ]∎
         < lo f , lo g > ∘ %1 T ∎
    }
    where open ecategory-aux-only ℂ
          open Peq
          open Peq-mor

  Peq-×of : (R S : Peq) → Exℂ.product-of R S
  Peq-×of R S = record
              { ×sp/ = Exℂ.mkspan/ (Peq-π₁ R S) (Peq-π₂ R S)
              ; ×isprd = record
                       { <_,_> = Peq-<>
                       ; ×tr₁ = Peq-mor-eq-ext ×tr₁
                       ; ×tr₂ = Peq-mor-eq-ext ×tr₂
                       ; ×uq =  λ pf₁ pf₂ → record
                             { hty = < hty pf₁ , hty pf₂ > 
                             ; hty₀ = ×ₐ<>~ar (hty₀ pf₁ ˢ) (hty₀ pf₂ ˢ)
                             ; hty₁ = ×ₐ<>~ar (hty₁ pf₁ ˢ) (hty₁ pf₂ ˢ)
                             }
                       }
              }
              where open Peq-mor-eq
                    open ecategory-aux-only ℂ
                    open exact-compl-construction.Peq-mor-are-arrows wpb


  ex-cmpl-prd : has-bin-products Ex ℂ [ qcart ]
  ex-cmpl-prd = record
              { prd-of = Peq-×of
              }

-- end exact-compl-has-bin-products



exact-compl-has-bin-products : {ℂ : ecategory} (qcart : is-quasi-cartesian ℂ) → has-bin-products Ex ℂ [ qcart ]
exact-compl-has-bin-products qcart = ex-cmpl-prd
                               where open exact-compl-has-bin-products qcart
