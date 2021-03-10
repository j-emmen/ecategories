
-- disable the K axiom:

{-# OPTIONS --without-K #-}

-- Agda version 2.5.4.1

module ecats.constructions.ecat-peq where

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


-- The category Peq ℂ of pseudo equivalence relations in a category ℂ & extensional arrows quotiented under peq of codomain.
-- If ℂ is exact, ℂ is a retract of EqRel ℂ.


module cat-of-pseudo-equivalence-relations (ℂ : ecategory) where
  open ecategory ℂ
  open pseudo-eq-rel-defs ℂ
  open wpullback-squares ℂ


  module peq-mor-eq-is-tt-eqrel (R S : peq) where
    open ecategory-aux-only ℂ
    private
      module R = peq R
      module S = peq S

    peq-mor-eq-refl : (f : peq-mor R S) →  peq-mor-eq f f
    peq-mor-eq-refl f = record
      { hty =  S.ρ ∘ f.lo
      ; hty₀ = ass ⊙ ∘e r S.ρ-ax₀ ⊙ lid
      ; hty₁ =  ass ⊙ ∘e r S.ρ-ax₁ ⊙ lid
      }
      where module f = peq-mor f

    peq-mor-eq-sym : {f g : peq-mor R S} →  peq-mor-eq f g →  peq-mor-eq g f
    peq-mor-eq-sym pf = record
      { hty = S.σ ∘ f~g.hty
      ; hty₀ = ass ⊙ ∘e r S.σ-ax₀ ⊙ f~g.hty₁
      ; hty₁ = ass ⊙ ∘e r S.σ-ax₁ ⊙ f~g.hty₀
      }
      where module f~g = peq-mor-eq pf

    peq-mor-eq-tra : {f g h : peq-mor R S} →  peq-mor-eq f g →  peq-mor-eq g h →  peq-mor-eq f h
    peq-mor-eq-tra pf1 pf2 = record
      { hty = S.τ ∘ Sτ.w⟨ f~g.hty , g~h.hty ⟩[ τpf ]
      ; hty₀ = ass ⊙ ∘e r S.τ-ax₀ ⊙ assˢ ⊙ ∘e (Sτ.w×/tr₁ τpf) r ⊙ f~g.hty₀
      ; hty₁ = ass ⊙ ∘e r S.τ-ax₁ ⊙ assˢ ⊙ ∘e (Sτ.w×/tr₂ τpf) r ⊙ g~h.hty₁
      }
      where module f~g = peq-mor-eq pf1
            module g~h = peq-mor-eq pf2
            module Sτ = wpullback-of-not S.τwpb
            τpf = f~g.hty₁ ⊙ g~h.hty₀ ˢ

  -- end peq-mor-eq-is-tt-eqrel


  peq-mor-eq-is-tteqrel : (R S : peq) → is-tt-eqrel (peq-mor-eq {R} {S})
  peq-mor-eq-is-tteqrel R S = record
    { refl = peq-mor-eq-refl
    ; sym = peq-mor-eq-sym
    ; tra = peq-mor-eq-tra
    }
    where open peq-mor-eq-is-tt-eqrel R S


  -- Setoid of peq-morphisms
  peq-Hom : (R S : peq) → setoid
  peq-Hom R S = record
    { object = peq-mor R S 
    ; _∼_ = peq-mor-eq
    ; istteqrel = peq-mor-eq-is-tteqrel R S
    }
    where open peq-mor
          open ecategory-aux-only ℂ


  module peq-mor-are-arrows where
    open peq
    open peq-mor
    open ecategory-aux-only ℂ    
    peq-cmp : {R S T : peq} → || peq-Hom S T || → || peq-Hom R S || → || peq-Hom R T ||
    peq-cmp {R} {S} {T} f g = record
      { lo = lo f ∘ lo g 
      ; isext = record
        { hi = hi f ∘ hi g 
        ; cmptb₀ = ass ⊙ ∘e r (cmptb₀ f) ⊙ assˢ ⊙ ∘e (cmptb₀ g) r ⊙ ass
        ; cmptb₁ = ass ⊙ ∘e r (cmptb₁ f) ⊙ assˢ ⊙ ∘e (cmptb₁ g) r ⊙ ass
        }
      }
    peq-idar : (R : peq) → || peq-Hom R R ||
    peq-idar R = record
      { lo = idar (Lo R)
      ; isext = record
        { hi = idar (Hi R)
        ; cmptb₀ = rid ⊙ lidˢ
        ; cmptb₁ = rid ⊙ lidˢ
        }
      }
    peq-∘ext : {R S T : peq} (f f' : || peq-Hom R S ||) (g g' : || peq-Hom S T ||)
                  → < peq-Hom R S > f ~ f' → < peq-Hom S T > g ~ g'
                    → < peq-Hom R T > (peq-cmp g f) ~ (peq-cmp g' f')
    peq-∘ext {R} {S} {T} f f' g g' f~f' g~g' = record
      { hty = τ T ∘ Tτ.w⟨ g.hi ∘ f~f'.hty , g~g'.hty ∘ f'.lo ⟩[ commsq ]
      ; hty₀ = ass ⊙ ∘e r T.τ-ax₀ ⊙ assˢ ⊙ ∘e (Tτ.w×/tr₁ commsq) r
               ⊙ ass ⊙ ∘e r g.cmptb₀ ⊙ assˢ ⊙ ∘e f~f'.hty₀ r
      ; hty₁ = ass ⊙ ∘e r T.τ-ax₁ ⊙ assˢ ⊙ ∘e (Tτ.w×/tr₂ commsq) r
               ⊙ ass ⊙ ∘e r g~g'.hty₁
      }
      where module R = peq R
            module T = peq T
            module Tτ = wpullback-of-not T.τwpb
            module f' = peq-mor f'
            module g = peq-mor g
            module f~f' = peq-mor-eq f~f'
            module g~g' = peq-mor-eq g~g'
            commsq : < Hom R.Lo T.Lo > T.%1 ∘ g.hi ∘ f~f'.hty ~ T.%0 ∘ g~g'.hty ∘ f'.lo
            commsq = ass ⊙ ∘e r g.cmptb₁ ⊙ assˢ ⊙ ∘e f~f'.hty₁ r
                     ⊙ ∘e r (g~g'.hty₀ ˢ) ⊙ assˢ

    peq-lid : {R S : peq} (f : || peq-Hom R S ||) → < peq-Hom R S >  peq-cmp (peq-idar S) f ~ f
    peq-lid f = peq-mor-eq-ext lid

    peq-rid : {R S : peq} (f : || peq-Hom R S ||) → < peq-Hom R S >  peq-cmp f (peq-idar R) ~ f
    peq-rid f = peq-mor-eq-ext rid

    peq-ass : {R₁ R₂ R₃ R₄ : peq} (f₁ : || peq-Hom R₁ R₂ ||)
              (f₂ : || peq-Hom R₂ R₃ ||) (f₃ : || peq-Hom R₃ R₄ ||)
                  → < peq-Hom R₁ R₄ > (peq-cmp f₃ (peq-cmp f₂ f₁)) ~ (peq-cmp (peq-cmp f₃ f₂) f₁)  
    peq-ass f g h = peq-mor-eq-ext ass
  -- end peq-mor-are-arrows

  peq-is-ecat : is-ecategory peq peq-Hom
  peq-is-ecat = record
    { _∘_ = peq-cmp
    ; idar = peq-idar
    ; ∘ext = peq-∘ext
    ; lidax = peq-lid
    ; ridax = peq-rid
    ; assoc = peq-ass
    }
    where open peq-mor-are-arrows
-- end cat-of-pseudo-equivalence-relations


-- ecategory of pseudo equivalence relations and extensional arrows

Peq : ecategory → ecategory
Peq ℂ = record
  { Obj = peq
  ; Hom = peq-Hom
  ; isecat = peq-is-ecat
  }
  where open pseudo-eq-rel-defs ℂ
        open cat-of-pseudo-equivalence-relations ℂ


freePeq : (ℂ : ecategory) → efunctor ℂ (Peq ℂ)
freePeq ℂ = record
  { FObj = ℂ.freepeq
  ; FHom = ℂ.freepeq-mor
  ; isF = record
        { ext = ℂ.freepeq-min-min-eq (ℂ.freepeq _)
        ; id = λ {A} → ℂ.peq-mor-eq-ext ℂ.r
        ; cmp = λ f g → ℂ.peq-mor-eq-ext ℂ.r
        }
  }
  where module ℂ where
          open ecategory-aux ℂ public
          open pseudo-eq-rel-defs ℂ public

ΔPeq : (ℂ : ecategory) → efunctor ℂ (Peq ℂ)
ΔPeq = freePeq




module quot-of-eqrel-funct {𝔼 : ecategory} (𝔼isex : is-exact 𝔼) where
  private
    module 𝔼 where
      open ecategory 𝔼
      open pseudo-eq-rel-defs 𝔼
      open wpullback-squares 𝔼
      open epis&monos-defs 𝔼
      open epis&monos-props 𝔼
      open exact-cat-d&p 𝔼isex
    module er where
      open eqrel public
      open eqrel-mor public
    module ER𝔼 = ecategory (EqRel 𝔼)
  module q (R : eqrel) = coeq-of (eqr-has-coeq (er.eqrelover R))
  
  q-ar-pf : {R S : eqrel} (f : eqrel-mor R S)
               → (q.ar S ∘ er.lo f) ∘ er.r₁ R ~ (q.ar S ∘ er.lo f) ∘ er.r₂ R
  q-ar-pf {R} {S} f = ~proof (q.ar S ∘ er.lo f) ∘ er.r₁ R   ~[ assˢ ⊙ ∘e (er.cmptb₀ f ˢ) r ] /
                             q.ar S ∘ er.r₁ S ∘ er.hi f      ~[ ass ⊙ ∘e r (q.eq S) ⊙ assˢ ] /
                             q.ar S ∘ er.r₂ S ∘ er.hi f      ~[ ∘e (er.cmptb₁ f) r ⊙ ass ]∎
                             (q.ar S ∘ er.lo f) ∘ er.r₂ R ∎
                    where open ecategory-aux-only 𝔼

  q-ar : {R S : eqrel} (f : eqrel-mor R S) → || Hom (q.Ob R) (q.Ob S) ||
  q-ar {R} {S} f = qR.univ (qS.ar ∘ f.lo) (q-ar-pf f)
                 where module qR = q R
                       module qS = q S
                       module f = eqrel-mor f

  q-sq : {R S : eqrel} (f : eqrel-mor R S) → q-ar f ∘ q.ar R ~ q.ar S ∘ (er.lo f)
  q-sq {R} {S} f = qR.univ-eq (q-ar-pf f)
                 where module qR = q R

  q-ar-ext : {R S : eqrel} (f f' : eqrel-mor R S)
                → eqrel-mor-eq f f' → q-ar f ~ q-ar f'
  q-ar-ext {R} {S} f f' f~f' = epi-pf (~proof q-ar f ∘ qR.ar               ~[ qR.univ-eq (q-ar-pf f) ⊙ ∘e (f~f'.hty₀ ˢ) r ] /
                                              qS.ar ∘ er.r₁ S ∘ f~f'.hty   ~[ ass ⊙ ∘e r qS.eq ⊙ assˢ ] /
                                              qS.ar ∘ er.r₂ S ∘ f~f'.hty   ~[ ∘e f~f'.hty₁ r ⊙ qR.univ-eq (q-ar-pf f') ˢ ]∎
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
                             qR.ar ∘ idar R.Lo        ~[ ridgen lidˢ ]∎
                             idar qR.Ob ∘ qR.ar ∎)
            where module R = eqrel R
                  module qR = q R
                  open is-epic (repi-is-epic (record { coeq = qR.iscoeq }))
                  open ecategory-aux-only 𝔼

  q-ar-cmp : {R S T : eqrel} (f : eqrel-mor R S) (g : eqrel-mor S T)
                → q-ar g ∘ q-ar f ~ q-ar (g ER𝔼.∘ f)
  q-ar-cmp {R} {S} {T} f g = epi-pf (~proof
    (q-ar g ∘ q-ar f) ∘ qR.ar       ~[ assˢ ⊙ ∘e (qR.univ-eq (q-ar-pf f)) r ] /
    q-ar g ∘ qS.ar ∘ f.lo      ~[ ass ⊙ ∘e r (qS.univ-eq (q-ar-pf g)) ⊙ assˢ ] /
    qT.ar ∘ gf.lo              ~[ qR.univ-eq (q-ar-pf (g ER𝔼.∘ f)) ˢ ]∎
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
        { a12 = ar
        ; a21 = ar⁻¹
        ; isop = isopair
        }
        where open 𝔼.uniq-of-coequalisers (q.iscoeq (𝔼.free-eqrel A))
              open same-rel-so-iso-coeq (idar-coeq A)
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
