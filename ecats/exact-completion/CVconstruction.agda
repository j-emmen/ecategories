
-- disable the K axiom:

{-# OPTIONS --without-K #-}

-- Agda version 2.5.4.1

module ecats.exact-completion.CVconstruction where

open import tt-basics.basics using (is-tt-eqrel)
open import tt-basics.setoids hiding (||_||)
open import ecats.basic-defs.ecat-def&not
open import ecats.basic-defs.eqv-rel
open import ecats.finite-limits.defs&not
open import ecats.functors.defs.efunctor
open import ecats.functors.defs.basic-defs



module exact-compl-construction {ℂ : ecategory} (wpb : has-weak-pullbacks ℂ) where
  open ecategory ℂ
  open pseudo-eq-rel-defs ℂ
  open wpullback-squares ℂ
  open weak-pullbacks-aux (wpb-aux wpb)


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
  peq-Hom R S = record { object = peq-mor R S 
                       ; _∼_ = peq-mor-eq {R} {S}
                       ; istteqrel = peq-mor-eq-is-tteqrel R S
                       }


  module peq-mor-are-arrows where
    open peq
    open peq-mor
    open peq-mor-eq
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
    peq-∘ext {R} {S} {T} f f' g g' pff pfg = record
      { hty = τ T ∘ Tτ.w⟨ hi g ∘ hty pff , hty pfg ∘ lo f' ⟩[ commsq ]
      ; hty₀ = ass ⊙ ∘e r (τ-ax₀ T) ⊙ assˢ ⊙ ∘e (Tτ.w×/tr₁ commsq) r
               ⊙ ass ⊙ ∘e r (cmptb₀ g) ⊙ assˢ ⊙ ∘e (hty₀ pff) r
      ; hty₁ = ass ⊙ ∘e r (τ-ax₁ T) ⊙ assˢ ⊙ ∘e (Tτ.w×/tr₂ commsq) r
               ⊙ ass ⊙ ∘e r (hty₁ pfg)
      }
      where module Tτ = wpullback-of-not (peq.τwpb T)
            commsq : < Hom (Lo R) (Lo T) > %1 T ∘ hi g ∘ hty pff ~ %0 T ∘ hty pfg ∘ lo f'
            commsq = ass ⊙ ∘e r (cmptb₁ g) ⊙ assˢ ⊙ ∘e (hty₁ pff) r
                     ⊙ ∘e r (hty₀ pfg ˢ) ⊙ assˢ

    peq-lid : {R S : peq} (f : || peq-Hom R S ||) → < peq-Hom R S >  peq-cmp (peq-idar S) f ~ f
    peq-lid f = peq-mor-eq-ext (lid {f = lo f})

    peq-rid : {R S : peq} (f : || peq-Hom R S ||) → < peq-Hom R S >  peq-cmp f (peq-idar R) ~ f
    peq-rid f = peq-mor-eq-ext (rid {f = lo f})


    peq-ass : {R₁ R₂ R₃ R₄ : peq} (f₁ : || peq-Hom R₁ R₂ ||)
              (f₂ : || peq-Hom R₂ R₃ ||) (f₃ : || peq-Hom R₃ R₄ ||)
                  → < peq-Hom R₁ R₄ > (peq-cmp f₃ (peq-cmp f₂ f₁)) ~ (peq-cmp (peq-cmp f₃ f₂) f₁)  
    peq-ass f g h = peq-mor-eq-ext ass

  -- end peq-mor-are-arrows
-- end exact-compl-construction  



--------------------
-- Exact completion
--------------------

exact-compl-cat : (ℂ : ecategory)  → has-fin-weak-limits ℂ → ecategory
exact-compl-cat ℂ hasfwl = record
  { Obj = peq
  ; Hom = peq-Hom
  ; isecat = record
               { _∘_ = peq-cmp
               ; idar = peq-idar
               ; ∘ext = peq-∘ext
               ; lidax = peq-lid
               ; ridax = peq-rid
               ; assoc = peq-ass
               }
  }
  where open has-fin-weak-limits hasfwl
        open pseudo-eq-rel-defs ℂ
        open exact-compl-construction haswpb
        open peq-mor-are-arrows

exact-compl-qcart-cat : (ℂ : ecategory) → is-quasi-cartesian ℂ → ecategory
exact-compl-qcart-cat ℂ qcart = record
  { Obj = peq
  ; Hom = peq-Hom
  ; isecat = record
               { _∘_ = peq-cmp
               ; idar = peq-idar
               ; ∘ext = peq-∘ext
               ; lidax = peq-lid
               ; ridax = peq-rid
               ; assoc = peq-ass
               }
  }
  where open is-quasi-cartesian qcart
        open pseudo-eq-rel-defs ℂ
        open exact-compl-construction haswpb
        open peq-mor-are-arrows


Ex_[_] : (ℂ : ecategory) → has-fin-weak-limits ℂ → ecategory
Ex ℂ [ hasfwl ] = exact-compl-cat ℂ hasfwl


Ex_qc[_] : (ℂ : ecategory) → is-quasi-cartesian ℂ → ecategory
Ex ℂ qc[ qcart ] = exact-compl-qcart-cat ℂ qcart


exact-compl-functor : {ℂ : ecategory} (hasfwl : has-fin-weak-limits ℂ)
                         → efunctor ℂ (Ex ℂ [ hasfwl ])
exact-compl-functor {ℂ} hasfwl = record
  { FObj = freepeq
  ; FHom = freepeq-mor
  ; isF = record
        { ext = λ {_} {_} {f} {f'} pf → record
              { hty = f
              ; hty₀ = lid
              ; hty₁ = lidgen pf
              }
        ; id = record
             { hty = idar _
             ; hty₀ = lid
             ; hty₁ = lid
             }
        ; cmp = λ f g → record
              { hty = g ∘ f
              ; hty₀ = lid
              ; hty₁ = lid
              }
        }
  }
  where open ecategory-aux ℂ
        open pseudo-eq-rel-defs ℂ
        open has-fin-weak-limits hasfwl
        open exact-compl-construction haswpb


exact-compl-qcart-functor : (ℂ : ecategory) (qcart : is-quasi-cartesian ℂ)
                         → efunctor ℂ (Ex ℂ qc[ qcart ])
exact-compl-qcart-functor ℂ qcart = exact-compl-functor (qcart→has-fwlim qcart)        
        


CVex_[_] : (ℂ : ecategory) (hasfwl : has-fin-weak-limits ℂ) → efunctor ℂ Ex ℂ [ hasfwl ]
CVex ℂ [ hasfwl ] = exact-compl-functor {ℂ} hasfwl


CVex_qc[_] : (ℂ : ecategory) (qcart : is-quasi-cartesian ℂ) → efunctor ℂ Ex ℂ qc[ qcart ]
CVex ℂ qc[ qcart ] = exact-compl-qcart-functor ℂ qcart



CVex-faith : {ℂ : ecategory} (hasfwl : has-fin-weak-limits ℂ)
               → is-faithful CVex ℂ [ hasfwl ]
CVex-faith {ℂ} hasfwl = record
  { faith-pf = λ pf → hty₀ pf ˢ ⊙ hty₁ pf
  }
  where open ecategory-aux-only ℂ
        open pseudo-eq-rel-defs ℂ
        open peq-mor-eq


CVex-full : {ℂ : ecategory} (hasfwl : has-fin-weak-limits ℂ)
           → is-full CVex ℂ [ hasfwl ]
CVex-full {ℂ} hasfwl = record
  { full-ar = λ f → lo f
  ; full-pf = λ {_} {_} {f} → record { hty = lo f ; hty₀ = lid ; hty₁ = lid }
  }
  where open ecategory-aux-only ℂ
        open pseudo-eq-rel-defs ℂ
        open peq-mor
