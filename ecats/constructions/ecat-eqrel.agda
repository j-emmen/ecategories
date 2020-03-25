
-- disable the K axiom:

{-# OPTIONS --without-K #-}

-- Agda version 2.5.4.1

module ecats.constructions.ecat-eqrel where

open import tt-basics.basics using (is-tt-eqrel)
open import tt-basics.setoids hiding (||_||)
open import ecats.basic-defs.ecat-def&not
open import ecats.basic-defs.all-arrows
open import ecats.basic-props.epi&mono
open import ecats.basic-props.image-fact
open import ecats.basic-defs.regular-ecat
open import ecats.basic-props.regular-ecat
open import ecats.basic-defs.exact-ecat
open import ecats.basic-props.exact-ecat
open import ecats.finite-limits.all
open import ecats.functors.defs.efunctor-d&n
open import ecats.functors.defs.basic-defs
open import ecats.functors.defs.natural-transformation


-- The category EqRel ℂ of equivalence relations in a category ℂ & extensional arrows quotiented under eqrel of codomain.
-- If ℂ is exact, ℂ is a retract of EqRel ℂ.


module cat-of-equivalence-relations (ℂ : ecategory) where
  open ecategory ℂ
  open eq-rel-defs ℂ
  open pullback-squares ℂ


  module eqrel-mor-eq-is-tt-eqrel (R S : eqrel) where
    open ecategory-aux-only ℂ
    private
      module R = eqrel R
      module S = eqrel S

    eqrel-mor-eq-refl : (f : eqrel-mor R S) →  eqrel-mor-eq f f
    eqrel-mor-eq-refl f = record
      { wit =  S.ρ ∘ f.base-ar
      ; wit₀ = ass ⊙ ∘e r S.ρ-ax₀ ⊙ lid
      ; wit₁ =  ass ⊙ ∘e r S.ρ-ax₁ ⊙ lid
      }
      where module f = eqrel-mor f

    eqrel-mor-eq-sym : {f g : eqrel-mor R S} →  eqrel-mor-eq f g →  eqrel-mor-eq g f
    eqrel-mor-eq-sym pf = record
      { wit = S.σ ∘ f~g.wit
      ; wit₀ = ass ⊙ ∘e r S.σ-ax₀ ⊙ f~g.wit₁
      ; wit₁ = ass ⊙ ∘e r S.σ-ax₁ ⊙ f~g.wit₀
      }
      where module f~g = eqrel-mor-eq pf

    eqrel-mor-eq-tra : {f g h : eqrel-mor R S} →  eqrel-mor-eq f g →  eqrel-mor-eq g h →  eqrel-mor-eq f h
    eqrel-mor-eq-tra pf1 pf2 = record
      { wit = S.τ ∘ Sτ.⟨ f~g.wit , g~h.wit ⟩[ τpf ]
      ; wit₀ = ass ⊙ ∘e r S.τ-ax₀ ⊙ assˢ ⊙ ∘e (Sτ.×/tr₁ τpf) r ⊙ f~g.wit₀
      ; wit₁ = ass ⊙ ∘e r S.τ-ax₁ ⊙ assˢ ⊙ ∘e (Sτ.×/tr₂ τpf) r ⊙ g~h.wit₁
      }
      where module f~g = eqrel-mor-eq pf1
            module g~h = eqrel-mor-eq pf2
            module Sτ = pullback-of-not S.τpb
            τpf = f~g.wit₁ ⊙ g~h.wit₀ ˢ

  -- end eqrel-mor-eq-is-tt-eqrel


  eqrel-mor-eq-is-tteqrel : (R S : eqrel) → is-tt-eqrel (eqrel-mor-eq {R} {S})
  eqrel-mor-eq-is-tteqrel R S = record
    { refl = eqrel-mor-eq-refl
    ; sym = eqrel-mor-eq-sym
    ; tra = eqrel-mor-eq-tra
    }
    where open eqrel-mor-eq-is-tt-eqrel R S


  -- Setoid of eqrel-morphisms
  eqrel-Hom : (R S : eqrel) → setoid
  eqrel-Hom R S = record
    { object = eqrel-mor R S 
    ; _∼_ = eqrel-mor-eq
    ; istteqrel = eqrel-mor-eq-is-tteqrel R S
    }
    where open eqrel-mor
          open ecategory-aux-only ℂ


  module eqrel-mor-are-arrows where
    open eqrel
    open eqrel-mor
    open ecategory-aux-only ℂ    
    eqrel-cmp : {R S T : eqrel} → || eqrel-Hom S T || → || eqrel-Hom R S || → || eqrel-Hom R T ||
    eqrel-cmp {R} {S} {T} f g = record
      { base-ar = base-ar f ∘ base-ar g 
      ; isext = record
        { rel-ar = rel-ar f ∘ rel-ar g 
        ; cmptb₀ = ass ⊙ ∘e r (cmptb₀ f) ⊙ assˢ ⊙ ∘e (cmptb₀ g) r ⊙ ass
        ; cmptb₁ = ass ⊙ ∘e r (cmptb₁ f) ⊙ assˢ ⊙ ∘e (cmptb₁ g) r ⊙ ass
        }
      }
    eqrel-idar : (R : eqrel) → || eqrel-Hom R R ||
    eqrel-idar R = record
      { base-ar = idar (baseOb R)
      ; isext = record
        { rel-ar = idar (relOb R)
        ; cmptb₀ = rid ⊙ lidˢ
        ; cmptb₁ = rid ⊙ lidˢ
        }
      }
    eqrel-∘ext : {R S T : eqrel} (f f' : || eqrel-Hom R S ||) (g g' : || eqrel-Hom S T ||)
                  → < eqrel-Hom R S > f ~ f' → < eqrel-Hom S T > g ~ g'
                    → < eqrel-Hom R T > (eqrel-cmp g f) ~ (eqrel-cmp g' f')
    eqrel-∘ext {R} {S} {T} f f' g g' f~f' g~g' = record
      { wit = τ T ∘ Tτ.⟨ g.rel-ar ∘ f~f'.wit , g~g'.wit ∘ f'.base-ar ⟩[ commsq ]
      ; wit₀ = ass ⊙ ∘e r T.τ-ax₀ ⊙ assˢ ⊙ ∘e (Tτ.×/tr₁ commsq) r
               ⊙ ass ⊙ ∘e r g.cmptb₀ ⊙ assˢ ⊙ ∘e f~f'.wit₀ r
      ; wit₁ = ass ⊙ ∘e r T.τ-ax₁ ⊙ assˢ ⊙ ∘e (Tτ.×/tr₂ commsq) r
               ⊙ ass ⊙ ∘e r g~g'.wit₁
      }
      where module R = eqrel R
            module T = eqrel T
            module Tτ = pullback-of-not T.τpb
            module f' = eqrel-mor f'
            module g = eqrel-mor g
            module f~f' = eqrel-mor-eq f~f'
            module g~g' = eqrel-mor-eq g~g'
            commsq : < Hom R.baseOb T.baseOb > T.r₂ ∘ g.rel-ar ∘ f~f'.wit ~ T.r₁ ∘ g~g'.wit ∘ f'.base-ar
            commsq = ass ⊙ ∘e r g.cmptb₁ ⊙ assˢ ⊙ ∘e f~f'.wit₁ r
                     ⊙ ∘e r (g~g'.wit₀ ˢ) ⊙ assˢ

    eqrel-lid : {R S : eqrel} (f : || eqrel-Hom R S ||) → < eqrel-Hom R S >  eqrel-cmp (eqrel-idar S) f ~ f
    eqrel-lid f = eqrel-mor-eq-ext lid

    eqrel-rid : {R S : eqrel} (f : || eqrel-Hom R S ||) → < eqrel-Hom R S >  eqrel-cmp f (eqrel-idar R) ~ f
    eqrel-rid f = eqrel-mor-eq-ext rid

    eqrel-ass : {R₁ R₂ R₃ R₄ : eqrel} (f₁ : || eqrel-Hom R₁ R₂ ||)
              (f₂ : || eqrel-Hom R₂ R₃ ||) (f₃ : || eqrel-Hom R₃ R₄ ||)
                  → < eqrel-Hom R₁ R₄ > (eqrel-cmp f₃ (eqrel-cmp f₂ f₁)) ~ (eqrel-cmp (eqrel-cmp f₃ f₂) f₁)  
    eqrel-ass f g h = eqrel-mor-eq-ext ass
  -- end eqrel-mor-are-arrows

  eqrel-is-ecat : is-ecategory eqrel eqrel-Hom
  eqrel-is-ecat = record
    { _∘_ = eqrel-cmp
    ; idar = eqrel-idar
    ; ∘ext = eqrel-∘ext
    ; lidax = eqrel-lid
    ; ridax = eqrel-rid
    ; assoc = eqrel-ass
    }
    where open eqrel-mor-are-arrows
-- end cat-of-equivalence-relations

-- ecategory of equivalence relations and extensional arrows

EqRel : ecategory → ecategory
EqRel ℂ = record
  { Obj = eqrel
  ; Hom = eqrel-Hom
  ; isecat = eqrel-is-ecat
  }
  where open eq-rel-defs ℂ
        open cat-of-equivalence-relations ℂ


freeEqRel : (ℂ : ecategory) → efunctor ℂ (EqRel ℂ)
freeEqRel ℂ = record
  { FObj = ℂ.free-eqrel
  ; FHom = ℂ.free-eqrel-mor
  ; isF = record
        { ext = ℂ.eqrel-mor-eq-ext
        ; id = λ {A} → ℂ.eqrel-mor-eq-ext ℂ.r
        ; cmp = λ f g → ℂ.eqrel-mor-eq-ext ℂ.r
        }
  }
  where module ℂ where
          open ecategory-aux ℂ public
          open eq-rel-defs ℂ public

ΔER : (ℂ : ecategory) → efunctor ℂ (EqRel ℂ)
ΔER = freeEqRel




module quot-of-eqrel-funct {𝔼 : ecategory} (𝔼isex : is-exact 𝔼) where
  open ecategory 𝔼
  open eq-rel-defs 𝔼
  open pullback-squares 𝔼
  open epis&monos-defs 𝔼
  open epis&monos-props 𝔼
  open exact-cat-d&p 𝔼isex
  private
    module er where
      open eqrel public
      open eqrel-mor public
    module ER𝔼 = ecategory (EqRel 𝔼)
  module q (R : eqrel) = coeq-of (eqr-has-coeq (er.eqrelover R))
  
  q-ar-pf : {R S : eqrel} (f : eqrel-mor R S)
               → (q.ar S ∘ er.base-ar f) ∘ er.r₁ R ~ (q.ar S ∘ er.base-ar f) ∘ er.r₂ R
  q-ar-pf {R} {S} f = ~proof (q.ar S ∘ er.base-ar f) ∘ er.r₁ R   ~[ assˢ ⊙ ∘e (er.cmptb₀ f ˢ) r ] /
                             q.ar S ∘ er.r₁ S ∘ er.rel-ar f      ~[ ass ⊙ ∘e r (q.eq S) ⊙ assˢ ] /
                             q.ar S ∘ er.r₂ S ∘ er.rel-ar f      ~[ ∘e (er.cmptb₁ f) r ⊙ ass ]∎
                             (q.ar S ∘ er.base-ar f) ∘ er.r₂ R ∎
                    where open ecategory-aux-only 𝔼

  q-ar : {R S : eqrel} (f : eqrel-mor R S) → || Hom (q.Ob R) (q.Ob S) ||
  q-ar {R} {S} f = qR.univ (qS.ar ∘ f.base-ar) (q-ar-pf f)
                 where module qR = q R
                       module qS = q S
                       module f = eqrel-mor f

  q-sq : {R S : eqrel} (f : eqrel-mor R S) → q-ar f ∘ q.ar R ~ q.ar S ∘ (er.base-ar f)
  q-sq {R} {S} f = qR.univ-eq (q-ar-pf f)
                 where module qR = q R

  q-ar-ext : {R S : eqrel} (f f' : eqrel-mor R S)
                → eqrel-mor-eq f f' → q-ar f ~ q-ar f'
  q-ar-ext {R} {S} f f' f~f' = epi-pf (~proof q-ar f ∘ qR.ar               ~[ qR.univ-eq (q-ar-pf f) ⊙ ∘e (f~f'.wit₀ ˢ) r ] /
                                              qS.ar ∘ er.r₁ S ∘ f~f'.wit   ~[ ass ⊙ ∘e r qS.eq ⊙ assˢ ] /
                                              qS.ar ∘ er.r₂ S ∘ f~f'.wit   ~[ ∘e f~f'.wit₁ r ⊙ qR.univ-eq (q-ar-pf f') ˢ ]∎
                                              q-ar f' ∘ qR.ar ∎ )
                             where module qR = q R
                                   module qS = q S
                                   module f = eqrel-mor f
                                   module f' = eqrel-mor f'
                                   module f~f' = eqrel-mor-eq f~f'
                                   open is-epic (repi-is-epic (record { coeq = qR.iscoeq }))
                                   open ecategory-aux-only 𝔼

  q-ar-id : (R : eqrel) → q-ar (ER𝔼.idar R) ~ idar (q.Ob R)
  q-ar-id R = epi-pf (~proof q-ar (ER𝔼.idar R) ∘ qR.ar   ~[ qR.univ-eq (q-ar-pf (ER𝔼.idar R)) ] /
                             qR.ar ∘ idar R.baseOb        ~[ ridgen lidˢ ]∎
                             idar qR.Ob ∘ qR.ar ∎)
            where module R = eqrel R
                  module qR = q R
                  open is-epic (repi-is-epic (record { coeq = qR.iscoeq }))
                  open ecategory-aux-only 𝔼

  q-ar-cmp : {R S T : eqrel} (f : eqrel-mor R S) (g : eqrel-mor S T)
                → q-ar g ∘ q-ar f ~ q-ar (g ER𝔼.∘ f)
  q-ar-cmp {R} {S} {T} f g = epi-pf (~proof
    (q-ar g ∘ q-ar f) ∘ qR.ar       ~[ assˢ ⊙ ∘e (qR.univ-eq (q-ar-pf f)) r ] /
    q-ar g ∘ qS.ar ∘ f.base-ar      ~[ ass ⊙ ∘e r (qS.univ-eq (q-ar-pf g)) ⊙ assˢ ] /
    qT.ar ∘ gf.base-ar              ~[ qR.univ-eq (q-ar-pf (g ER𝔼.∘ f)) ˢ ]∎
    q-ar (g ER𝔼.∘ f) ∘ qR.ar ∎)
                           where module qR = q R
                                 module qS = q S
                                 module qT = q T
                                 module f = eqrel-mor f
                                 --module g = eqrel-mor g
                                 module gf = eqrel-mor (g ER𝔼.∘ f)
                                 open is-epic (repi-is-epic (record { coeq = qR.iscoeq }))
                                 open ecategory-aux-only 𝔼
-- end quot-of-eqrel-funct
  


QER : {𝔼 : ecategory} → is-exact 𝔼 → efunctor (EqRel 𝔼) 𝔼
QER {𝔼} isex = record
  { FObj = q.Ob
  ; FHom = q-ar
  ; isF = record
        { ext = λ {_} {_} {f} {f'} pf → q-ar-ext f f' pf
        ; id = λ {A} → q-ar-id A
        ; cmp = q-ar-cmp
        }
  }
  where open is-exact isex
        open quot-of-eqrel-funct isex
        --open eq-rel-defs 𝔼
        --open epis&monos-defs 𝔼
        --module q (R : eqrel) = coeq-of (eqr-has-coeq (eqrel.eqrelover R))
        --open ecategory-aux-only 𝔼
    


module exact-is-retract-of-EqRel {𝔼 : ecategory} (𝔼isex : is-exact 𝔼) where
  private
    module ER𝔼 where
      open ecategory (EqRel 𝔼) public
      open eq-rel-defs (EqRel 𝔼) public
      open pullback-squares (EqRel 𝔼) public
      open epis&monos-defs (EqRel 𝔼) public
      open epis&monos-props (EqRel 𝔼) public
      open iso-defs (EqRel 𝔼) public
    module 𝔼 where
      open ecategory 𝔼 public
      open eq-rel-defs 𝔼 public
      open pullback-squares 𝔼 public
      open epis&monos-defs 𝔼 public
      open epis&monos-props 𝔼 public
      open iso-defs 𝔼 public
    module ex𝔼 = is-exact 𝔼isex
    module er where
      open 𝔼.eqrel public
      open 𝔼.eqrel-mor public
    module q (R : 𝔼.eqrel) = 𝔼.coeq-of (ex𝔼.eqr-has-coeq (er.eqrelover R))
    module Q𝔼 = efunctor-aux (QER 𝔼isex)
    module Δ𝔼 = efunctor-aux (ΔER 𝔼)
    module QΔ𝔼 = efunctor-aux (QER 𝔼isex ○ ΔER 𝔼)


  idar-coeq : (A : 𝔼.Obj) → 𝔼.is-coeq (𝔼.idar A) (𝔼.idar A) (𝔼.idar A)
  idar-coeq A = record
    { eq = lidgen ridˢ
    ; univ = λ f _ → f
    ; univ-eq = λ _ → rid
    ; uniq = record { epi-pf = λ pf → ridˢ ⊙ pf ⊙ rid }
    }
    where open ecategory-aux-only 𝔼
  iso : (A : 𝔼.Obj) → q.Ob (𝔼.free-eqrel A) 𝔼.≅ₒ A
  iso A = record
        { a12 = uq-of-coeq-ar (idar-coeq A)
        ; a21 = uq-of-coeq-ar⁻¹ (idar-coeq A) -- = q.ar (𝔼.free-eqrel A)
        ; isop = uq-of-coeq-isopair (idar-coeq A)
        }
        where open 𝔼.uniq-of-coequalisers (q.iscoeq (𝔼.free-eqrel A))
  module iso (A : 𝔼.Obj) = 𝔼._≅ₒ_ (iso A)
  nat : {A B : 𝔼.Obj} (f : || 𝔼.Hom A B ||) → iso.a12 B 𝔼.∘ QΔ𝔼.ₐ f 𝔼.~ f 𝔼.∘ iso.a12 A
  nat {A} {B} f = epi-pf (~proof
    (iso.a12 B 𝔼.∘ QΔ𝔼.ₐ f) 𝔼.∘ qA.ar       ~[ assˢ ⊙ ∘e (qA.univ-eq (q-ar-pf (𝔼.free-eqrel-mor f))) r ] /
    iso.a12 B 𝔼.∘ qB.ar 𝔼.∘ f                ~[ ass ⊙ lidgg r (iso.idcod B) ] /
    f                                         ~[ ridggˢ r (iso.idcod A) ⊙ ass ]∎
    (f 𝔼.∘ iso.a12 A) 𝔼.∘ qA.ar ∎)
                where module qA = q (𝔼.free-eqrel A)
                      module qB = q (𝔼.free-eqrel B)
                      open 𝔼.is-epic (𝔼.repi-is-epic (record { coeq = qA.iscoeq }))
                      open ecategory-aux-only 𝔼
                      open quot-of-eqrel-funct 𝔼isex using (q-ar-pf) 


-- end exact-is-retract-of-EqRel




-- An exact category as a retract of its category of equivalence relations

ex-retr-EqR :  {𝔼 : ecategory} (𝔼isex : is-exact 𝔼) → natural-iso (QER 𝔼isex ○ ΔER 𝔼) IdF
ex-retr-EqR {𝔼} 𝔼isex = record
  { natt = record
         { fnc = λ {A} → iso.a12 A
         ; nat = nat
         }
  ; natt⁻¹ = record
           { fnc = λ {A} → iso.a21 A
           ; nat = λ {A} {B} f → iso-defs.invIsNat 𝔼 (iso.isop A) (iso.isop B) (nat f)
           }
  ; isiso = λ {A} → iso.isop A
  }
  where open exact-is-retract-of-EqRel 𝔼isex
