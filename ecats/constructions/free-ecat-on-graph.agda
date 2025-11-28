
{-# OPTIONS --without-K #-}

module ecats.constructions.free-ecat-on-graph where

open import tt-basics.setoids hiding (||_||)
open import ecats.basic-defs.ecat-def&not
open import ecats.basic-defs.isomorphism
open import ecats.basic-props.isomorphism
open import ecats.functors.defs.efunctor-d&n
open import ecats.functors.defs.natural-transformation
open import ecats.functors.defs.natural-iso

-- when ℂ is free on a graph E ⇉ V
module free-category-on-graph-defs {ℓ₁ ℓ₂ ℓ₃ : Level}(ℂ : ecategoryₗₑᵥ ℓ₁ ℓ₂ ℓ₃)
                                   {ℓ₄ ℓ₅ : Level}{V : Set ℓ₁}(E : V → V → setoid {ℓ₄} {ℓ₅})
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
                               : Set (ℂ.ℓₐₗₗ ⊔ ecat.ℓₐₗₗ 𝔻 ⊔ ℓ₄) where
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
         {ℓ₄ ℓ₅ : Level}{V : Set ℓ₁}(E : V → V → setoid {ℓ₄} {ℓ₅})
         {FO : V → ecat.Obj ℂ}
         (FE : {u v : V} → || E u v || → || ecat.Hom ℂ (FO u) (FO v) ||)
         (ℓ₁' ℓ₂' ℓ₃' : Level)
         : Set (ecat.ℓₐₗₗ ℂ ⊔ sucₗₑᵥ (ℓ₁' ⊔ ℓ₂' ⊔ ℓ₃') ⊔ ℓ₄ ⊔ ℓ₅)
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


-- Constructions of the free ecategory on a graph using inductive types

module free-ecat-on-graph-via-inductive-paths {ℓ₁ ℓ₂ ℓ₃ : Level}{V : Set ℓ₁}
                                              (E : V → V → setoid {ℓ₂} {ℓ₃})
                                              where
  private
    ||E|| : V → V → Set ℓ₂
    ||E|| u v = || E u v ||
    module E {u v : V} = setoid-aux (E u v)

  -- inductive type of finite paths
  data fin-path  (u : V) : V → Set (ℓ₁ ⊔ ℓ₂) where
    emty : fin-path u u
    apnd : {w v : V} → fin-path u w → ||E|| w v → fin-path u v
  indv : {u v : V} → ||E|| u v → fin-path u v
  indv e = apnd emty e
  twocmp : {u v w : V} → ||E|| u v → ||E|| v w → fin-path u w
  twocmp e e' = apnd (indv e) e'
  lapnd : {u v w : V} → ||E|| u v → fin-path v w → fin-path u w
  lapnd e emty = indv e
  lapnd e (apnd p e') = apnd (lapnd e p) e'

  path-rec : {u : V}{ℓ : Level}{PP : {v : V} → fin-path u v → Set ℓ}
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

  -- setoid of finite paths
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

  HomStd : V → V → setoid {ℓ₁ ⊔ ℓ₂} {ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃}
  HomStd u v = record
    { object = fin-path u v
    ; _∼_ = path-eq {u} {v}
    ; istteqrel = record
                { refl = path-eq-refl {u} {v}
                ; sym = path-eq-sym {u} {v}
                ; tra = path-eq-trans {u} {v}
                }
    }

  private
    ||H|| : V → V → Set (ℓ₁ ⊔ ℓ₂)
    ||H|| u v = || HomStd u v ||
    module H {u v : V} = setoid-aux (HomStd u v)

  path-cmp : {u v w : V} → fin-path v w → fin-path u v → fin-path u w
  path-cmp emty p₁ = p₁
  path-cmp (apnd p e) p₁ = apnd (path-cmp p p₁) e

  path-cmp-ext : {u v w : V}{p₁ p₁' : fin-path u v}{p₂ p₂' : fin-path v w}
                    → p₁ H.~ p₁' → p₂ H.~ p₂' → path-cmp p₂ p₁ H.~ path-cmp p₂' p₁'
  path-cmp-ext eq₁ emty-eq = eq₁
  path-cmp-ext eq₁ (apnd-eq eq₂ eeq) = apnd-eq (path-cmp-ext eq₁ eq₂) eeq

  path-rid : {u v : V} (p : fin-path u v) → path-cmp p emty H.~ p
  path-rid emty = emty-eq
  path-rid (apnd p e) = apnd-eq (path-rid p) E.r

  path-ass : {u v w z : V}(p₁ : fin-path u v)(p₂ : fin-path v w)(p₃ : fin-path w z)
                → path-cmp p₃ (path-cmp p₂ p₁) H.~ path-cmp (path-cmp p₃ p₂) p₁
  path-ass p₁ p₂ emty = H.r
  path-ass p₁ p₂ (apnd p₃ e) = apnd-eq (path-ass p₁ p₂ p₃) E.r
--- end free-ecat-on-graph-via-inductive-paths



free-ecat-on-graph : {ℓ₁ ℓ₂ ℓ₃ : Level}{V : Set ℓ₁}(E : V → V → setoid {ℓ₂} {ℓ₃})
                         → ecategoryₗₑᵥ ℓ₁ (ℓ₁ ⊔ ℓ₂) (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃)
free-ecat-on-graph {V = V} E = record
    { Obj = V
    ; Hom = HomStd
    ; isecat = record
                 { _∘_ = path-cmp
                 ; idar = λ u → emty
                 ; ∘ext = λ p₁ p₁' p₂ p₂' → path-cmp-ext {p₁ = p₁} {p₁'} {p₂} {p₂'}
                 ; lidax = λ _ → H.r
                 ; ridax = path-rid
                 ; assoc = path-ass
                 }
    }
    where open free-ecat-on-graph-via-inductive-paths E
          module H {u v : V} = setoid-aux (HomStd u v)


module free-on-graph-emb {ℓ₁ ℓ₂ ℓ₃ : Level}{V : Set ℓ₁}(E : V → V → setoid {ℓ₂} {ℓ₃}) where
  open free-ecat-on-graph-via-inductive-paths E
  private
    module E {u v : V} = setoid-aux (E u v)
    module FC = ecat (free-ecat-on-graph E)
  ₒ : V → FC.Obj
  ₒ u = u
  ₐ : {u v : V} → || E u v || → || FC.Hom u v ||
  ₐ = indv
  ext : {u v : V}{e e' : || E u v ||} → e E.~ e' → ₐ e FC.~ ₐ e'
  ext = apnd-eq emty-eq
-- end free-on-graph-emb



module free-on-graph-is-free-on-graph {ℓ₁ ℓ₂ ℓ₃ : Level}{V : Set ℓ₁}(E : V → V → setoid {ℓ₂} {ℓ₃})
                                      {ℓ₁' ℓ₂' ℓ₃' : Level}(𝔻 : ecategoryₗₑᵥ ℓ₁' ℓ₂' ℓ₃')
                                      where
  private
    module E {u v : V} = setoid-aux (E u v)
    module FC = ecat (free-ecat-on-graph E)
    FC : ecategoryₗₑᵥ FC.ℓₒ FC.ℓₐᵣᵣ FC.ℓ~
    FC = free-ecat-on-graph E
    module FF = free-on-graph-emb E
    module 𝔻 where
      open ecat 𝔻 public
      open iso-defs 𝔻 public
      open iso-props 𝔻 public
  open free-category-on-graph-defs FC E FF.ₐ FF.ext
  module unv-prop {GO : V → 𝔻.Obj}
                  {GE : {u v : V} → || E u v || → || 𝔻.Hom (GO u) (GO v) ||}
                  (GEext : {u v : V}{uv uv' : || E u v ||} → uv E.~ uv' → GE uv 𝔻.~ GE uv')
                  where
    open free-ecat-on-graph-via-inductive-paths E
    --open fin-path
    --open path-eq

    har : {u v : V} → || FC.Hom u v || → || 𝔻.Hom (GO u) (GO v) ||
    har {u} emty = 𝔻.idar (GO u)
    har (apnd p e) = GE e 𝔻.∘ har p
    ext : {u v : V}{p p' : || FC.Hom u v ||} → p FC.~ p' → har p 𝔻.~ har p'
    ext {p = emty} {emty} emty-eq = r
                                  where open ecategory-aux-only 𝔻 using (r)
    ext {p = apnd p e} {apnd p' e'} (apnd-eq eq eeq) = ∘e (ext eq) (GEext eeq)
                                                     where open ecategory-aux-only 𝔻 using (∘e)
    idax : {u : V} → 𝔻.idar (GO u) 𝔻.~ 𝔻.idar (GO u)
    idax {u} = r
             where open ecategory-aux-only 𝔻 using (r)
    cmp : {u v w : V}(p₁ : || FC.Hom u v ||)(p₂ : || FC.Hom v w ||)
             → har p₂ 𝔻.∘ har p₁ 𝔻.~ har (p₂ FC.∘ p₁)
    cmp p₁ emty = lid
                where open ecategory-aux-only 𝔻 using (lid)
    cmp p₁ (apnd p₂ e) = assˢ ⊙ ∘e (cmp p₁ p₂) r
                       where open ecategory-aux-only 𝔻

    lift : efunctorₗₑᵥ FC 𝔻
    lift = record
      { FObj = GO
      ; FHom = har
      ; isF = record
            { ext = ext
            ; id = idax
            ; cmp = cmp
            }
      }
    private module lft = efunctor-aux lift

    module uniq-lift {H : efunctorₗₑᵥ FC 𝔻}(Hfnc : {v : V} → || 𝔻.Hom (efctr.ₒ H v) (GO v) ||)
                     (Hnate : {u v : V}(e : || E u v ||)
                                 → Hfnc 𝔻.∘ efctr.ₐ H (indv e) 𝔻.~ GE e 𝔻.∘ Hfnc)
                     (Hiso : {v : V} → 𝔻.is-iso (Hfnc {v}))
                     where
      private
        module H where
          open efunctor-aux H public
          module iso {v : V} = 𝔻.is-iso (Hiso {v})

      Hnat : {u v : V}(p : || FC.Hom u v ||)
                    → Hfnc 𝔻.∘ H.ₐ p 𝔻.~ lft.ₐ p 𝔻.∘ Hfnc
      Hnat emty = ridgg lidˢ H.id
                where open ecategory-aux-only 𝔻 using (ridgg; lidˢ)
      Hnat (apnd p e) = ~proof
        Hfnc 𝔻.∘ H.ₐ (apnd p e)            ~[ ∘e H.∘ax-rfˢ r ] /
        Hfnc 𝔻.∘ H.ₐ (indv e) 𝔻.∘ H.ₐ p    ~[ ass ⊙ ∘e r (Hnate e) ⊙ assˢ ] /
        GE e 𝔻.∘ Hfnc 𝔻.∘ H.ₐ p            ~[ ∘e (Hnat p) r ] /
        GE e 𝔻.∘ lft.ₐ p 𝔻.∘ Hfnc          ~[ ass ]∎
        lft.ₐ (apnd p e) 𝔻.∘ Hfnc ∎
                      where open ecategory-aux-only 𝔻

      natiso : H ≅ₐ lift
      natiso = record
        { natt = record
               { fnc = Hfnc
               ; nat = Hnat
               }
        ; natt⁻¹ = record
                 { fnc = H.iso.⁻¹
                 ; nat = λ p → 𝔻.iso-sq H.iso.isisopair H.iso.isisopair (Hnat p)
                 }
        ; isiso = H.iso.isisopair
        }
    -- end uniq-lift

    isfree : is-free-on-graph-prop 𝔻 GEext
    isfree = record
      { fctr = lift
      ; tr-fnc = λ {v} → 𝔻.idar (GO v)
      ; tr-nat = λ e → lid
      ; tr-iso = λ {v} → 𝔻.idar-is-iso (GO v)
      ; uq = natiso
      }
      where open ecategory-aux-only 𝔻 using (lid)
            open uniq-lift using (natiso)
  -- end unv-prop
-- end free-on-graph-is-free-on-graph


free-ecat-on-graph-is-free : {ℓ₁ ℓ₂ ℓ₃ : Level}{V : Set ℓ₁}(E : V → V → setoid {ℓ₂} {ℓ₃})
                             (ℓ₁' ℓ₂' ℓ₃' : Level)
                                  → (free-ecat-on-graph E) is-free-category-on-graph E
                                                            via (free-on-graph-emb.ₐ E)
                                                            at-lev[ ℓ₁' , ℓ₂' , ℓ₃' ]
free-ecat-on-graph-is-free E ℓ₁' ℓ₂' ℓ₃' = record
  { ext = FF.ext
  ; unvprop = unv-prop.isfree
  }
  where open free-on-graph-is-free-on-graph E {ℓ₁'} {ℓ₂'} {ℓ₃'}
        module FF = free-on-graph-emb E
