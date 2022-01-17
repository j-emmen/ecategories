
{-# OPTIONS --without-K #-}

module ecats.constructions.free-ecat-on-graph where

open import tt-basics.setoids hiding (||_||)
open import ecats.basic-defs.ecat-def&not
open import ecats.basic-defs.isomorphism
open import ecats.basic-props.isomorphism
open import ecats.functors.defs.efunctor-d&n
open import ecats.functors.defs.natural-iso

module free-category-on-graph-defs {ℓ₁ ℓ₂ ℓ₃ : Level}(ℂ : ecategoryₗₑᵥ ℓ₁ ℓ₂ ℓ₃)
                                   {V : Set ℓ₁}(E : V → V → setoid {ℓ₂} {ℓ₃})
                                   {FO : V → ecat.Obj ℂ}
                                   (FE : {u v : V} → || E u v || → || ecat.Hom ℂ (FO u) (FO v) ||)
                                   (FEext : {u v : V}{uv uv' : || E u v ||} → < E u v > uv ~ uv'
                                              → < ecat.Hom ℂ (FO u) (FO v) > FE uv ~ FE uv')
                                   where
  private
    module ℂ = ecat ℂ
    module unvprop-aux {ℓ₁' ℓ₂' ℓ₃' : Level}(𝕏 : ecategoryₗₑᵥ ℓ₁' ℓ₂' ℓ₃') where
      open ecat 𝕏 public
      open iso-defs 𝕏 public
      open iso-props 𝕏 public

  record is-free-on-graph-prop {ℓ₁' ℓ₂' ℓ₃' : Level}(𝔻 : ecategoryₗₑᵥ ℓ₁' ℓ₂' ℓ₃'){GO : V → ecat.Obj 𝔻}
                               {GE : {u v : V} → || E u v || → || ecat.Hom 𝔻 (GO u) (GO v) ||}
                               (GEext : {u v : V}{uv uv' : || E u v ||} → < E u v > uv ~ uv'
                                          → < ecat.Hom 𝔻 (GO u) (GO v) > GE uv ~ GE uv')
                               : Set (ℂ.ℓₐₗₗ ⊔ ecat.ℓₐₗₗ 𝔻) where
    private
      module 𝔻 = unvprop-aux 𝔻
    field
      fctr : efunctorₗₑᵥ ℂ 𝔻
    private module fctr = efunctorₗₑᵥ fctr
    field
      tr-fnc : {v : V} → || 𝔻.Hom (fctr.ₒ (FO v)) (GO v) ||
      tr-nat : {u v : V}(uv : || E u v ||) → tr-fnc {v} 𝔻.∘ fctr.ₐ (FE uv) 𝔻.~ GE uv 𝔻.∘ tr-fnc {u}
      tr-iso : {v : V} → 𝔻.is-iso (tr-fnc {v})
    private module tmp {v : V} = 𝔻.is-iso (tr-iso {v}) renaming (invf to tr-fnc⁻¹)
    open tmp public
    tr-nat⁻¹ : {u v : V}(uv : || E u v ||) → tr-fnc⁻¹ 𝔻.∘ GE uv 𝔻.~ fctr.ₐ (FE uv) 𝔻.∘ tr-fnc⁻¹
    tr-nat⁻¹ {u} {v} uv = 𝔻.iso-sq (isisopair {u}) (isisopair {v}) (tr-nat uv)
    field
      uq : {H : efunctorₗₑᵥ ℂ 𝔻}
           (Hfnc : {v : V} → || 𝔻.Hom (efctr.ₒ H (FO v)) (GO v) ||)
           (Hnat : {u v : V}(uv : || E u v ||)
                      → Hfnc {v} 𝔻.∘ efctr.ₐ H (FE uv) 𝔻.~ GE uv 𝔻.∘ Hfnc {u})
           (Hiso : {v : V} → 𝔻.is-iso (Hfnc {v}))
             → H ≅ₐ fctr
-- end free-category-on-graph-defs



record _is-free-category-on-graph_via_at-lev[_,_,_]
         {ℓ₁ ℓ₂ ℓ₃ : Level}(ℂ : ecategoryₗₑᵥ ℓ₁ ℓ₂ ℓ₃)
         {V : Set ℓ₁}(E : V → V → setoid {ℓ₂} {ℓ₃})
         {FO : V → ecat.Obj ℂ}
         (FE : {u v : V} → || E u v || → || ecat.Hom ℂ (FO u) (FO v) ||)
         (ℓ₁' ℓ₂' ℓ₃' : Level)
         : Set (sucₗₑᵥ (ecat.ℓₐₗₗ ℂ ⊔ ℓ₁' ⊔ ℓ₂' ⊔ ℓ₃'))
         where
  private
    module ℂ = ecat ℂ
  open free-category-on-graph-defs ℂ E FE
  field
    ext : {u v : V}{uv uv' : || E u v ||} → < E u v > uv ~ uv'
             → FE uv ℂ.~ FE uv'
    unvprop : (𝔻 : ecategoryₗₑᵥ ℓ₁' ℓ₂' ℓ₃'){GO : V → ecat.Obj 𝔻}
              {GE : {u v : V} → || E u v || → || ecat.Hom 𝔻 (GO u) (GO v) ||}
              (GEext : {u v : V}{uv uv' : || E u v ||} → < E u v > uv ~ uv'
                           → < ecat.Hom 𝔻 (GO u) (GO v) > GE uv ~ GE uv')
                    → is-free-on-graph-prop ext 𝔻 GEext
  module unv (𝔻 : ecategoryₗₑᵥ ℓ₁' ℓ₂' ℓ₃'){GO : V → ecat.Obj 𝔻}
             {GE : {u v : V} → || E u v || → || ecat.Hom 𝔻 (GO u) (GO v) ||}
             (GEext : {u v : V}{uv uv' : || E u v ||} → < E u v > uv ~ uv'
                        → < ecat.Hom 𝔻 (GO u) (GO v) > GE uv ~ GE uv')
             = is-free-on-graph-prop ext (unvprop 𝔻 GEext)



module free-ecat-on-graph-via-inductive-paths {ℓ₁ ℓ₂ ℓ₃ : Level}{V : Set ℓ₁}
                                              (E : V → V → setoid {ℓ₂} {ℓ₃})
                                              where
  private
    ||E|| : V → V → Set ℓ₂
    ||E|| u v = || E u v ||
    module E {u v : V} = setoid-aux (E u v)

  -- inductive type of finite paths
  data fin-path  (u : V) : V → Set (ℓ₁ ⊔ ℓ₂) where
    --indv : ||E|| u v → fin-path u v
    emty : fin-path u u
    apnd : {w v : V} → fin-path u w → ||E|| w v → fin-path u v
  indv : {u v : V} → ||E|| u v → fin-path u v
  indv e = apnd emty e

  path-rec : {u : V}{ℓ : Level}{PP : {v : V} → fin-path u v → Set ℓ}
                --→ ((e : ||E|| u v) → PP (indv e))
                → (PP emty)
                → ({w v : V}(p : fin-path u w)(e : ||E|| w v) → PP (apnd p e))
                  → {v : V}(p : fin-path u v) → PP p
  path-rec {PP = PP} P∅ Pₐ emty = P∅
  path-rec {PP = PP} P∅ Pₐ (apnd p e) = Pₐ p e

  path-rec-all : {ℓ : Level}{PP : {u v : V} → fin-path u v → Set ℓ}
                    → ({u : V} → PP (emty {u}))
                    → ({u v w : V}(p : fin-path u v)(e : ||E|| v w) → PP (apnd p e))
                      → {u v : V}(p : fin-path u v) → PP p
  path-rec-all {PP = PP} P∅ Pₐ emty = P∅
  path-rec-all {PP = PP} P∅ᵢ Pₐ (apnd p e) = Pₐ p e

{-
  module path-eq-defs (u v : V) where
  
    record indv-eq (e e' : ||E|| u v) : Set (ℓ₁ ⊔ ℓ₂) where
      field
        pf : e == e'

    record lid-inv (e : ||E|| u v)(p' : fin-path u u)(e' : ||E|| u v) : Set (ℓ₁ ⊔ ℓ₂) where
      field
        pf : e == e'
        -- p' = refl, refl, ..., refl

    record rid-inv (p p' : fin-path u v)(e' : ||E|| v v) : Set (ℓ₁ ⊔ ℓ₂) where
      field
        r-pf : e' == refl v
        -- p = p'
-}

  -- end path-eq-defs


  -- setoid of finite paths (doing w/o refl of E)
  data path-eq {u : V} : {v : V}(p₁ p₂ : fin-path u v) → Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃) where
    emty-eq : path-eq emty emty
    apnd-eq : {w v : V}{p₁ p₂ : fin-path u w}{e₁ e₂ : ||E|| w v}
                  → path-eq p₁ p₂ → e₁ E.~ e₂ → path-eq (apnd p₁ e₁) (apnd p₂ e₂)
{-
    apnd-eeq : {w v : V}{p : fin-path u w}{e₁ e₂ : ||E|| w v}
                  → e₁ E.~ e₂ → path-eq (apnd p e₁) (apnd p e₂)
    apnd-peq : {w v : V}{p₁ p₂ : fin-path u w}{e : ||E|| w v}
                  → path-eq p₁ p₂ → path-eq (apnd p₁ e) (apnd p₂ e)
                  -- maybe provable?
-}
  indv-eq : {u v : V}{e₁ e₂ : ||E|| u v}→ e₁ E.~ e₂ → path-eq (indv e₁) (indv e₂)
  indv-eq {u} = apnd-eq emty-eq

  path-eq-refl : {u v : V}(p : fin-path u v) → path-eq p p
  path-eq-refl emty = emty-eq
  path-eq-refl (apnd p e) = apnd-eq (path-eq-refl p) E.r
{- the definition via path-rec does not pass the termination check...
                  path-rec {PP = λ p → path-eq p p}
                           emty-eq
                           (λ p _ → apnd-eq (path-eq-refl p) E.r)
-}

  path-eq-trans : {u v : V}{p₁ p₂ p₃ : fin-path u v}
                     → path-eq p₁ p₂ → path-eq p₂ p₃ → path-eq p₁ p₃
  path-eq-trans {u} {u} {emty} {emty} {emty} emty-eq emty-eq = emty-eq
  path-eq-trans {u} {v} {apnd p₁ e₁} {apnd p₂ e₂} {apnd p₃ e₃}
                (apnd-eq eq₁ eeq) (apnd-eq eq₂ eeq')
                = apnd-eq (path-eq-trans eq₁ eq₂) (eeq E.⊙ eeq')

  path-eq-sym : {u v : V}{p₁ p₂ : fin-path u v}
                     → path-eq p₁ p₂ → path-eq p₂ p₁
  path-eq-sym {u} {u} {emty} {emty} emty-eq = emty-eq
  path-eq-sym {u} {v} {apnd p₁ e₁} {apnd p₂ e₂} (apnd-eq eq eeq)
              = apnd-eq (path-eq-sym eq) (eeq E.ˢ)


--- end free-ecat-on-graph-via-inductive-paths
