{-# OPTIONS --without-K #-}

module ecats.constructions.free-eql-prd where

open import tt-basics.basics hiding (_×_; _×ₕ_; _×/_)
open import tt-basics.setoids hiding (||_||)
open import ecats.basic-defs.ecat-def&not
open import ecats.basic-defs.commut-shapes
--open import ecats.functors.defs.efunctor-d&n
--open import ecats.functors.defs.natural-transformation
--open import ecats.functors.defs.adjunction
open import ecats.finite-limits.all
open import ecats.isomorphism


module free-cat-with-equalisers-over-fin-products {ℂ : ecategory}(has-trm : has-terminal ℂ)(has-prd : has-bin-products ℂ) where
  open ecat ℂ
  --open ecategory-aux ℂ
  open comm-shapes ℂ
  open iso-d&p ℂ
  --open binary-products ℂ
  open finite-limits-d&p ℂ
  open has-bin-products has-prd using (prd-of)
  open has-terminal has-trm

  -- corelations

  record is-coreflexive {baseOb relOb : Obj} (∂₀ ∂₁ : || Hom baseOb relOb ||) : Set₁ where
    field
      ρ : || Hom relOb baseOb ||
      ρ-ax₀ : ρ ∘ ∂₀  ~ idar baseOb
      ρ-ax₁ : ρ ∘ ∂₁  ~ idar baseOb
    ρ-ax₀g : {X : Obj} {f : || Hom X baseOb ||} → ρ ∘ ∂₀ ∘ f ~ f
    ρ-ax₀g = ass ⊙ lidgg r ρ-ax₀
           where open ecategory-aux ℂ
    ρ-ax₁g : {X : Obj} {f : || Hom X baseOb ||} → ρ ∘ ∂₁ ∘ f ~ f
    ρ-ax₁g = ass ⊙ lidgg r ρ-ax₁
            where open ecategory-aux ℂ

  record is-cosymmetric {baseOb relOb : Obj} (∂₀ ∂₁ : || Hom baseOb relOb ||) : Set₁ where
    field
      σ : || Hom relOb relOb ||
      σ-ax₀ : σ ∘ ∂₀  ~ ∂₁
      σ-ax₁ : σ ∘ ∂₁  ~ ∂₀
    σ-ax₀g : {X : Obj} {f : || Hom X baseOb ||} → σ ∘ ∂₀ ∘ f ~ ∂₁ ∘ f
    σ-ax₀g = ass ⊙ ∘e r σ-ax₀
           where open ecategory-aux ℂ
    σ-ax₁g : {X : Obj} {f : || Hom X baseOb ||} → σ ∘ ∂₁ ∘ f ~ ∂₀ ∘ f
    σ-ax₁g = ass ⊙ ∘e r σ-ax₁
           where open ecategory-aux ℂ

  record is-rs-coRel {baseOb relOb : Obj} (∂₀ ∂₁ : || Hom baseOb relOb ||) : Set 1ₗₑᵥ where
    field
      isρ : is-coreflexive ∂₀ ∂₁
      isσ : is-cosymmetric ∂₀ ∂₁
    open is-coreflexive isρ public
    open is-cosymmetric isσ public

  record rs-coRel/ (baseOb : Obj) : Set 1ₗₑᵥ where
    field
      relOb : Obj
      ∂₀ ∂₁ : || Hom baseOb relOb ||
      isρσ : is-rs-coRel ∂₀ ∂₁
    open is-rs-coRel isρσ public

  record rs-coRel : Set 1ₗₑᵥ where
    field
      baseOb : Obj
      isrs/ : rs-coRel/ baseOb
    open rs-coRel/ isrs/ public

  cosym-compl-rfl-coRel :  {baseOb relOb : Obj} {∂₀ ∂₁ : || Hom baseOb relOb ||} → is-coreflexive ∂₀ ∂₁ → rs-coRel/ baseOb
  cosym-compl-rfl-coRel {baseOb} {relOb} {∂₀} {∂₁} iscr = record
    { relOb = R×R.O12
    ; ∂₀ = R×R.< ∂₀ , ∂₁ >
    ; ∂₁ = R×R.< ∂₁ , ∂₀ >
    ; isρσ = record
      { isρ = record
        { ρ = R.ρ ∘ R×R.π₁
        ; ρ-ax₀ = assˢ ⊙ ∘e R×R.×tr₁ r ⊙ R.ρ-ax₀
        ; ρ-ax₁ = assˢ ⊙ ∘e R×R.×tr₁ r ⊙ R.ρ-ax₁
        }
      ; isσ = record
        { σ = R×R.< R×R.π₂ , R×R.π₁ >
        ; σ-ax₀ = R×R.×uq (~proof R×R.π₁ ∘ R×R.< R×R.π₂ , R×R.π₁ > ∘ R×R.< ∂₀ , ∂₁ > ~[ ass ⊙ ∘e r R×R.×tr₁ ] /
                                  R×R.π₂ ∘ R×R.< ∂₀ , ∂₁ >     ~[ R×R.×tr₂ ⊙ R×R.×tr₁ˢ ]∎
                                  R×R.π₁ ∘ R×R.< ∂₁ , ∂₀ > ∎)
                          (~proof R×R.π₂ ∘ R×R.< R×R.π₂ , R×R.π₁ > ∘ R×R.< ∂₀ , ∂₁ > ~[ ass ⊙ ∘e r R×R.×tr₂ ] /
                                  R×R.π₁ ∘ R×R.< ∂₀ , ∂₁ >     ~[ R×R.×tr₁ ⊙ R×R.×tr₂ˢ ]∎
                                  R×R.π₂ ∘ R×R.< ∂₁ , ∂₀ > ∎)
        ; σ-ax₁ = R×R.×uq (~proof R×R.π₁ ∘ R×R.< R×R.π₂ , R×R.π₁ > ∘ R×R.< ∂₁ , ∂₀ > ~[ ass ⊙ ∘e r R×R.×tr₁ ] /
                                  R×R.π₂ ∘ R×R.< ∂₁ , ∂₀ >     ~[ R×R.×tr₂ ⊙ R×R.×tr₁ˢ ]∎
                                  R×R.π₁ ∘ R×R.< ∂₀ , ∂₁ > ∎)
                          (~proof R×R.π₂ ∘ R×R.< R×R.π₂ , R×R.π₁ > ∘ R×R.< ∂₁ , ∂₀ > ~[ ass ⊙ ∘e r R×R.×tr₂ ] /
                                  R×R.π₁ ∘ R×R.< ∂₁ , ∂₀ >     ~[ R×R.×tr₁ ⊙ R×R.×tr₂ˢ ]∎
                                  R×R.π₂ ∘ R×R.< ∂₀ , ∂₁ > ∎)
        }
      }
    }
    where module R = is-coreflexive iscr
          module R×R = product-of-not (prd-of relOb relOb)
          open ecategory-aux ℂ hiding (_∘_)


  record is-coRel-morphism/ {baseOb baseOb' : Obj}(cR : rs-coRel/ baseOb)(cR' : rs-coRel/ baseOb')
                            (base-ar : || Hom baseOb baseOb' ||)
                            : Set where
    open rs-coRel/
    field
      rel-ar : || Hom (relOb cR)  (relOb cR') ||
      cmptb₀ :  rel-ar ∘ ∂₀ cR ~ ∂₀ cR' ∘ base-ar
      cmptb₁ :  rel-ar ∘ ∂₁ cR ~ ∂₁ cR' ∘ base-ar
    cmptb₀g : {X : Obj} {k : || Hom X baseOb ||} → rel-ar ∘ ∂₀ cR ∘ k ~ ∂₀ cR' ∘ base-ar ∘ k
    cmptb₀g = ass ⊙ ∘e r cmptb₀ ⊙ assˢ
            where open ecategory-aux ℂ using (ass; _⊙_; ∘e; r; assˢ)
    cmptb₁g : {X : Obj} {k : || Hom X baseOb ||} → rel-ar ∘ ∂₁ cR ∘ k ~ ∂₁ cR' ∘ base-ar ∘ k
    cmptb₁g = ass ⊙ ∘e r cmptb₁ ⊙ assˢ
            where open ecategory-aux ℂ using (ass; _⊙_; ∘e; r; assˢ)

  record coRel-morphism (cR cR' : rs-coRel) : Set where
    open rs-coRel
    field
      base-ar : || Hom (baseOb cR) (baseOb cR') ||
      is-coext : is-coRel-morphism/ (isrs/ cR) (isrs/ cR') base-ar
    open is-coRel-morphism/ is-coext public

  
  record coRel-mor-pre-eq {R S : rs-coRel} (f g : coRel-morphism R S) : Set where
    -- constructor mkper-mor-eq
    open rs-coRel
    open coRel-morphism
    field
      wit : || Hom (relOb R) (baseOb S) ||
      wit₀ : wit ∘ ∂₀ R ~ base-ar f
      wit₁ : wit ∘ ∂₁ R ~ base-ar g
    wit₀g : {X : Obj} {k : || Hom X (baseOb R) ||} → wit ∘ ∂₀ R ∘ k ~ base-ar f ∘ k
    wit₀g = ass ⊙ ∘e r wit₀
          where open ecategory-aux ℂ using (ass; _⊙_; ∘e; r)
    wit₁g : {X : Obj} {k : || Hom X (baseOb R) ||} → wit ∘ ∂₁ R ∘ k ~ base-ar g ∘ k
    wit₁g = ass ⊙ ∘e r wit₁
          where open ecategory-aux ℂ using (ass; _⊙_; ∘e; r)

  coRel-mor-eq-ext : {R S : rs-coRel} {f g : coRel-morphism R S}
                      → coRel-morphism.base-ar f ~ coRel-morphism.base-ar g → coRel-mor-pre-eq f g
  coRel-mor-eq-ext {R} {S} {f} {g} eq = record
    { wit = S.ρ ∘ f.rel-ar
    ; wit₀ = ~proof (S.ρ ∘ f.rel-ar) ∘ R.∂₀        ~[ assˢ ⊙ ∘e f.cmptb₀ r ] /
                    S.ρ ∘ S.∂₀ ∘ f.base-ar         ~[ S.ρ-ax₀g ]∎
                    f.base-ar ∎
    ; wit₁ = ~proof (S.ρ ∘ f.rel-ar) ∘ R.∂₁         ~[ assˢ ⊙ ∘e f.cmptb₁ r ] /
                    S.ρ ∘ S.∂₁ ∘ f.base-ar          ~[ S.ρ-ax₁g ⊙ eq ]∎
                    g.base-ar ∎
    }
    where module R = rs-coRel R
          module S = rs-coRel S
          module f = coRel-morphism f
          module g = coRel-morphism g
          open ecategory-aux ℂ hiding (_∘_)

  coRel-mor-pre-eq-rfl : (R S : rs-coRel) → is-refl-ttRel (coRel-mor-pre-eq {R} {S})
  coRel-mor-pre-eq-rfl R S = record
    { refl = λ f → record
      { wit = base-ar f ∘ R.ρ
      ; wit₀ = assˢ ⊙ ridgg r R.ρ-ax₀
      ; wit₁ = assˢ ⊙ ridgg r R.ρ-ax₁
      }
    }
    where module R = rs-coRel R
          module S = rs-coRel S
          open coRel-morphism
          open ecategory-aux ℂ using (assˢ; _⊙_; ridgg; r)

  coRel-mor-pre-eq-sym : (R S : rs-coRel) → is-symm-ttRel (coRel-mor-pre-eq {R} {S})
  coRel-mor-pre-eq-sym R S = record
    { sym = λ {f} {g} h → record
      { wit = wit h ∘ R.σ
      ; wit₀ = ~proof (wit h ∘ R.σ) ∘ R.∂₀   ~[ assˢ ⊙ ∘e R.σ-ax₀ r ] /
                      wit h ∘ R.∂₁           ~[ wit₁ h ]∎
                      base-ar g ∎
      ; wit₁ = ~proof (wit h ∘ R.σ) ∘ R.∂₁   ~[ assˢ ⊙ ∘e R.σ-ax₁ r ] /
                      wit h ∘ R.∂₀           ~[ wit₀ h ]∎
                      base-ar f ∎
      }
    }
    where module R = rs-coRel R
          module S = rs-coRel S
          open coRel-morphism --using (base-ar)
          open coRel-mor-pre-eq {R} {S}
          open ecategory-aux ℂ hiding (_∘_)


  coRel-mor-eq : {R S : rs-coRel} (f g : coRel-morphism R S) → Set
  coRel-mor-eq {R} {S} = trans-clos-ttRel (coRel-mor-pre-eq {R} {S})

  coRel-mor-eq-eqv : (R S : rs-coRel) → is-tt-eqrel (coRel-mor-eq {R} {S})
  coRel-mor-eq-eqv R S = trans-clos-refsym-ttRel-is-eqv (coRel-mor-pre-eq-rfl R S) (coRel-mor-pre-eq-sym R S)
  module coRel-mor-eq-eqv (R S : rs-coRel) = is-tt-eqrel (coRel-mor-eq-eqv R S)


  coRelHom : rs-coRel → rs-coRel → setoid {0ₗₑᵥ} {0ₗₑᵥ}
  coRelHom R S = record
    { object = coRel-morphism R S
    ; _∼_ = coRel-mor-eq {R} {S}
    ; istteqrel = coRel-mor-eq-eqv R S
    }

  coRel-mor-id  : (R : rs-coRel) → || coRelHom R R ||
  coRel-mor-id R = record
    { base-ar = idar R.baseOb
    ; is-coext = record
      { rel-ar = idar R.relOb
      ; cmptb₀ = lidgen ridˢ
      ; cmptb₁ = lidgen ridˢ
      }
    }
    where module R = rs-coRel R
          open ecategory-aux ℂ hiding (idar; _∘_)

  coRel-mor-cmp  : {R S T : rs-coRel} → || coRelHom S T || → || coRelHom R S || → || coRelHom R T ||
  coRel-mor-cmp{R} {S} {T} g f = record
    { base-ar = g.base-ar ∘ f.base-ar
    ; is-coext = record
      { rel-ar = g.rel-ar ∘ f.rel-ar
      ; cmptb₀ = ~proof (g.rel-ar ∘ f.rel-ar) ∘ R.∂₀      ~[ assˢ ⊙ ∘e f.cmptb₀ r ] /
                        g.rel-ar ∘ S.∂₀ ∘ f.base-ar       ~[ ass ⊙ ∘e r g.cmptb₀ ⊙ assˢ ]∎
                        T.∂₀ ∘ g.base-ar ∘ f.base-ar ∎
      ; cmptb₁ = ~proof (g.rel-ar ∘ f.rel-ar) ∘ R.∂₁      ~[ assˢ ⊙ ∘e f.cmptb₁ r ] /
                        g.rel-ar ∘ S.∂₁ ∘ f.base-ar       ~[ ass ⊙ ∘e r g.cmptb₁ ⊙ assˢ ]∎
                        T.∂₁ ∘ g.base-ar ∘ f.base-ar ∎
      }
    }
    where module R = rs-coRel R
          module S = rs-coRel S
          module T = rs-coRel T
          module f = coRel-morphism f
          module g = coRel-morphism g
          open ecategory-aux ℂ hiding (_∘_)


  coRel-mor-cmp-ext-pre : {R S T : rs-coRel} (f f' : || coRelHom R S ||) (g g' : || coRelHom S T ||)
                         → coRel-mor-pre-eq f f' → coRel-mor-eq g g' → coRel-mor-eq (coRel-mor-cmp g f) (coRel-mor-cmp g' f')

  coRel-mor-cmp-ext-pre {R} {S} {T} f f' g g' rf (incl rg) =
    rel~.tra (incl aux₁) (incl aux₂)
    where module rel~ {X Y : rs-coRel} = coRel-mor-eq-eqv X Y
          module R = rs-coRel R
          module S = rs-coRel S
          --module T = rs-coRel T
          --module f = coRel-morphism f
          module f' = coRel-morphism f'
          module g = coRel-morphism g
          module g' = coRel-morphism g'
          module rf = coRel-mor-pre-eq rf
          module rg = coRel-mor-pre-eq rg
          aux₁ : coRel-mor-pre-eq (coRel-mor-cmp g f) (coRel-mor-cmp g f')
          aux₁ = record
            { wit = g.base-ar ∘ rf.wit
            ; wit₀ = assˢ ⊙ ∘e rf.wit₀ r
            ; wit₁ = assˢ ⊙ ∘e rf.wit₁ r
            }
            where open ecategory-aux ℂ hiding (_∘_)
          aux₂ : coRel-mor-pre-eq (coRel-mor-cmp g f') (coRel-mor-cmp g' f')
          aux₂ = record
            { wit = rg.wit ∘ f'.rel-ar
            ; wit₀ = ~proof (rg.wit ∘ f'.rel-ar) ∘ R.∂₀     ~[ assˢ ⊙ ∘e f'.cmptb₀ r ] /
                              rg.wit ∘ S.∂₀ ∘ f'.base-ar    ~[ ass ⊙ ∘e r rg.wit₀ ]∎
                              g.base-ar ∘ f'.base-ar ∎
            ; wit₁ = ~proof (rg.wit ∘ f'.rel-ar) ∘ R.∂₁     ~[ assˢ ⊙ ∘e f'.cmptb₁ r ] /
                            rg.wit ∘ S.∂₁ ∘ f'.base-ar      ~[ ass ⊙ ∘e r rg.wit₁ ]∎
                            g'.base-ar ∘ f'.base-ar ∎
            }
            where open ecategory-aux ℂ hiding (_∘_)

  coRel-mor-cmp-ext-pre {R} {S} {T} f f' g g' rf (indct {a' = g₀} eqg₁ eqg₂) =
    rel~.tra aux₁ aux₂
    where module rel~ {X Y : rs-coRel} = coRel-mor-eq-eqv X Y
          module relpre {X Y : rs-coRel} = is-refl-ttRel (coRel-mor-pre-eq-rfl X Y)
          aux₁ : coRel-mor-eq (coRel-mor-cmp g f) (coRel-mor-cmp g₀ f')
          aux₁ = coRel-mor-cmp-ext-pre f f' g g₀ rf eqg₁
          aux₂ : coRel-mor-eq (coRel-mor-cmp g₀ f') (coRel-mor-cmp g' f')
          aux₂ = coRel-mor-cmp-ext-pre f' f' g₀ g' (relpre.refl f') eqg₂


  coRel-mor-cmp-ext : {R S T : rs-coRel} (f f' : || coRelHom R S ||) (g g' : || coRelHom S T ||)
                         → coRel-mor-eq f f' → coRel-mor-eq g g' → coRel-mor-eq (coRel-mor-cmp g f) (coRel-mor-cmp g' f')
  coRel-mor-cmp-ext {R} {S} {T} f f' g g' (incl rf) eqg =
    coRel-mor-cmp-ext-pre f f' g g' rf eqg
  coRel-mor-cmp-ext {R} {S} {T} f f' g g' (indct {a' = f₀} eqf₁ eqf₂) eqg =
    rel~.tra aux₁ aux₂
    where module rel~ {X Y : rs-coRel} = coRel-mor-eq-eqv X Y
          aux₁ : coRel-mor-eq (coRel-mor-cmp g f) (coRel-mor-cmp g' f₀)
          aux₁ = coRel-mor-cmp-ext f f₀ g g' eqf₁ eqg
          aux₂ : coRel-mor-eq (coRel-mor-cmp g' f₀) (coRel-mor-cmp g' f')
          aux₂ = coRel-mor-cmp-ext f₀ f' g' g' eqf₂ (rel~.refl g')


  coRel-mor-lid-pre : {R S : rs-coRel} (f : || coRelHom R S ||)
                         → coRel-mor-pre-eq (coRel-mor-cmp (coRel-mor-id S) f) f
  coRel-mor-lid-pre {R} {S} f = record
    { wit = f.base-ar ∘ R.ρ
    ; wit₀ = assˢ ⊙ lidgenˢ (ridgg r R.ρ-ax₀)
    ; wit₁ = assˢ ⊙ ridgg r R.ρ-ax₁
    }
    where module rel~ {X Y : rs-coRel} = coRel-mor-eq-eqv X Y
          module R = rs-coRel R
          module S = rs-coRel S
          module f = coRel-morphism f
          open ecategory-aux ℂ using (assˢ; _⊙_; lidgenˢ; ridgg; r)

  coRel-mor-rid-pre : {R S : rs-coRel} (f : || coRelHom R S ||)
                         → coRel-mor-pre-eq (coRel-mor-cmp f (coRel-mor-id R)) f
  coRel-mor-rid-pre {R} {S} f = record
    { wit = f.base-ar ∘ R.ρ
    ; wit₀ = assˢ ⊙ ridgenˢ (ridgg r R.ρ-ax₀)
    ; wit₁ = assˢ ⊙ ridgg r R.ρ-ax₁
    }
    where module rel~ {X Y : rs-coRel} = coRel-mor-eq-eqv X Y
          module R = rs-coRel R
          module S = rs-coRel S
          module f = coRel-morphism f
          open ecategory-aux ℂ using (assˢ; _⊙_; ridgenˢ; ridgg; r)

  coRel-mor-ass-pre : {R S T U : rs-coRel} (f : || coRelHom R S ||) (g : || coRelHom S T ||) (h : || coRelHom T U ||)
                         → coRel-mor-pre-eq (coRel-mor-cmp h (coRel-mor-cmp g f)) (coRel-mor-cmp (coRel-mor-cmp h g) f)
  coRel-mor-ass-pre {R} {S} {T} {U} f g h = record
    { wit = h.base-ar ∘ g.base-ar ∘ f.base-ar ∘ R.ρ
    ; wit₀ = assˢ ⊙ ∘e (assˢ ⊙ ∘e (assˢ ⊙ ridgg r R.ρ-ax₀) r) r 
    ; wit₁ = assˢ ⊙ ∘e (assˢ ⊙ ∘e (assˢ ⊙ ridgg r R.ρ-ax₁) r) r ⊙ ass 
    }
    where module R = rs-coRel R
          module f = coRel-morphism f
          module g = coRel-morphism g
          module h = coRel-morphism h
          open ecategory-aux ℂ using (ass; assˢ; ∘e; _⊙_; ridgg; r)

  Eqlℂ : ecategory
  Eqlℂ = record
    { Obj = rs-coRel
    ; Hom = coRelHom
    ; isecat = record
             { _∘_ = coRel-mor-cmp
             ; idar = coRel-mor-id
             ; ∘ext = coRel-mor-cmp-ext
             ; lidax = λ f → incl (coRel-mor-lid-pre f)
             ; ridax = λ f → incl (coRel-mor-rid-pre f)
             ; assoc = λ f g h → incl (coRel-mor-ass-pre f g h)
             }
    }
    where module rel~ {X Y : rs-coRel} = coRel-mor-eq-eqv X Y
  module Eqlℂ = ecat Eqlℂ

  module Eqlℂ-has-equalisers {R S : Eqlℂ.Obj} (f g : || Eqlℂ.Hom R S ||)
                             (Rr×So : product-of (rs-coRel.relOb R) (rs-coRel.baseOb S))
                             where
    private
      module R = rs-coRel R
      module S = rs-coRel S
      module f = coRel-morphism f
      module g = coRel-morphism g
      module Rr×So = product-of-not Rr×So
      ∂'₀ ∂'₁ : || Hom R.baseOb Rr×So.O12 || 
      ∂'₀ = Rr×So.< R.∂₀ , f.base-ar >
      ∂'₁ = Rr×So.< R.∂₁ , g.base-ar >
      iscr' :  is-coreflexive ∂'₀ ∂'₁
      iscr' = record
        { ρ = R.ρ ∘ Rr×So.π₁
        ; ρ-ax₀ = assˢ ⊙ ∘e Rr×So.×tr₁ r ⊙ R.ρ-ax₀
        ; ρ-ax₁ = assˢ ⊙ ∘e Rr×So.×tr₁ r ⊙ R.ρ-ax₁
        }
        where open ecategory-aux ℂ using (ass; assˢ; ∘e; _⊙_; r)

    E : Eqlℂ.Obj
    E = record
      { baseOb = R.baseOb
      ; isrs/ = cosym-compl-rfl-coRel {R.baseOb} {Rr×So.O12} {∂'₀} {∂'₁} iscr'
      }
    module E where
      open rs-coRel E public
      module relOb = product-of-not (prd-of Rr×So.O12 Rr×So.O12)

    e : || Eqlℂ.Hom E R ||
    e = record
      { base-ar = idar R.baseOb
      ; is-coext = record
        { rel-ar = Rr×So.π₁ ∘ E.relOb.π₁
        ; cmptb₀ = assˢ ⊙ ∘e E.relOb.×tr₁ r ⊙ ridgenˢ Rr×So.×tr₁
        ; cmptb₁ = assˢ ⊙ ∘e E.relOb.×tr₁ r ⊙ ridgenˢ Rr×So.×tr₁
        }
      }
      where open ecategory-aux ℂ using (assˢ; ∘e; _⊙_; r; ridgenˢ)
    module e = coRel-morphism e

    etr' : coRel-mor-pre-eq (f Eqlℂ.∘ e) (g Eqlℂ.∘ e)
    etr' = record
      { wit = Rr×So.π₂ ∘ E.relOb.π₁
      ; wit₀ = ~proof (Rr×So.π₂ ∘ E.relOb.π₁) ∘ E.∂₀   ~[ assˢ ⊙ ∘e E.relOb.×tr₁ r ] /
                      Rr×So.π₂ ∘ ∂'₀                  ~[ ridgenˢ Rr×So.×tr₂ ]∎
                      f.base-ar ∘ e.base-ar ∎
      ; wit₁ = ~proof (Rr×So.π₂ ∘ E.relOb.π₁) ∘ E.∂₁   ~[ assˢ ⊙ ∘e E.relOb.×tr₁ r ] /
                      Rr×So.π₂ ∘ ∂'₁                   ~[ ridgenˢ Rr×So.×tr₂ ]∎
                      g.base-ar ∘ e.base-ar ∎
      }
      where open ecategory-aux ℂ hiding (_∘_)

    etr : f Eqlℂ.∘ e Eqlℂ.~ g Eqlℂ.∘ e
    etr = incl etr'

    can-ar : {T : Eqlℂ.Obj} (h : || Eqlℂ.Hom T R ||) → f Eqlℂ.∘ h Eqlℂ.~ g Eqlℂ.∘ h → || Eqlℂ.Hom T E ||
    can-ar {T} h (incl r) = {!!}
      where module T = rs-coRel T
            module h = coRel-morphism h

    can-ar {T} h (indct {a' = k} eq₁ eq₂) = {!!}


    can-ar-par : {T : Eqlℂ.Obj} (h : || Eqlℂ.Hom T R ||) {k : || Eqlℂ.Hom T S ||}
                    → f Eqlℂ.∘ h Eqlℂ.~ k → k Eqlℂ.~ g Eqlℂ.∘ h
                      → || Eqlℂ.Hom T E ||
    can-ar-par {T} h {k} (incl rf) (incl rg) = {!!}
    can-ar-par {T} h {k} (incl rf) (indct {a' = k'} eq₂₁ eq₂₂) = {!!}

{-
      { base-ar = h.base-ar
      ; is-coext = record
        { rel-ar = rar
        ; cmptb₀ = E.relOb.×uq (~proof E.relOb.π₁ ∘ rar ∘ T.∂₀                       ~[ ass ⊙ ∘e r E.relOb.×tr₁ ] /
                                       Rr×So.< h.rel-ar , re.wit > ∘ T.∂₀            ~[ Rr×So.<>ar~<>ar h.cmptb₀ re.wit₀ ] /
                                       Rr×So.< R.∂₀ , f.base-ar > ∘ h.base-ar       ~[ ∘e r E.relOb.×tr₁ˢ ⊙ assˢ ]∎
                                       E.relOb.π₁ ∘ E.relOb.< ∂'₀ , ∂'₁ > ∘ h.base-ar ∎)
                               {!~proof E.relOb.π₂ ∘ rar ∘ T.∂₀                       ~[ ass ⊙ ∘e r E.relOb.×tr₂ ] /
                                       Rr×So.< h.rel-ar , re.wit > ∘ T.∂₀            ~[ Rr×So.<>ar~<>ar h.cmptb₀ (re.wit₀ ⊙ ?) ] /
                                       Rr×So.< R.∂₀ , g.base-ar > ∘ h.base-ar       ~[ ∘e r E.relOb.×tr₂ˢ ⊙ assˢ ]∎
                                       E.relOb.π₂ ∘ E.relOb.< ∂'₀ , ∂'₁ > ∘ h.base-ar ∎!}
        ; cmptb₁ = E.relOb.×uq {!~proof E.relOb.π₁ ∘ rar ∘ T.∂₁                       ~[ ass ⊙ ∘e r E.relOb.×tr₁ ] /
                                       Rr×So.< h.rel-ar , re.wit > ∘ T.∂₁            ~[ Rr×So.<>ar~<>ar h.cmptb₁ re.wit₁ ] /
                                       Rr×So.< R.∂₁ , g.base-ar > ∘ h.base-ar       ~[ ∘e r E.relOb.×tr₁ˢ ⊙ assˢ ]∎
                                       E.relOb.π₁ ∘ E.relOb.< ∂'₁ , ∂'₀ > ∘ h.base-ar ∎!}
                               {!!}
        }
      }
      where module T = rs-coRel T
            module h = coRel-morphism h
            module k = coRel-morphism k
            module re = coRel-mor-pre-eq re
            open ecategory-aux ℂ hiding (Hom; _∘_)
            rar : || Hom T.relOb E.relOb ||
            rar = E.relOb.< Rr×So.< h.rel-ar , re.wit > , Rr×So.< h.rel-ar , re.wit > >
-}

    can-ar-par {T} h (indct {a' = k'} eq₁₁ eq₁₂) eq₂ =
      can-ar-par h eq₁₁ aux
      where module rel~ {X Y : rs-coRel} = coRel-mor-eq-eqv X Y
            aux : k' Eqlℂ.~ g Eqlℂ.∘ h
            aux = rel~.tra eq₁₂ eq₂

  -- end Eqlℂ-has-equalisers

  Eql-has-eql : has-equalisers Eqlℂ
  Eql-has-eql = {!!}
  


-- end free-cat-with-equalisers-over-fin-products
