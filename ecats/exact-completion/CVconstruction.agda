
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



module exact-compl-construction {ℂ : ecategory} (wpb : has-weak-pullbacks ℂ) where
  open ecategory ℂ
  open pseudo-eq-rel-defs ℂ
  open wpullback-squares ℂ
  open weak-pullbacks-aux (wpb-aux wpb)


  module Peq-mor-eq-is-tt-eqrel (R S : Peq) where
    open ecategory-aux-only ℂ
    private
      module R = Peq R
      module S = Peq S

    Peq-mor-eq-refl : (f : Peq-mor R S) →  Peq-mor-eq f f
    Peq-mor-eq-refl f = record
      { hty =  S.ρ ∘ f.lo
      ; hty₀ = ass ⊙ ∘e r S.ρ-ax₀ ⊙ lid
      ; hty₁ =  ass ⊙ ∘e r S.ρ-ax₁ ⊙ lid
      }
      where module f = Peq-mor f

    Peq-mor-eq-sym : {f g : Peq-mor R S} →  Peq-mor-eq f g →  Peq-mor-eq g f
    Peq-mor-eq-sym pf = record
      { hty = S.σ ∘ f~g.hty
      ; hty₀ = ass ⊙ ∘e r S.σ-ax₀ ⊙ f~g.hty₁
      ; hty₁ = ass ⊙ ∘e r S.σ-ax₁ ⊙ f~g.hty₀
      }
      where module f~g = Peq-mor-eq pf

    Peq-mor-eq-tra : {f g h : Peq-mor R S} →  Peq-mor-eq f g →  Peq-mor-eq g h →  Peq-mor-eq f h
    Peq-mor-eq-tra pf1 pf2 = record
      { hty = S.τ ∘ Sτ.w⟨ f~g.hty , g~h.hty ⟩[ τpf ]
      ; hty₀ = ass ⊙ ∘e r S.τ-ax₀ ⊙ assˢ ⊙ ∘e (Sτ.w×/tr₁ τpf) r ⊙ f~g.hty₀
      ; hty₁ = ass ⊙ ∘e r S.τ-ax₁ ⊙ assˢ ⊙ ∘e (Sτ.w×/tr₂ τpf) r ⊙ g~h.hty₁
      }
      where module f~g = Peq-mor-eq pf1
            module g~h = Peq-mor-eq pf2
            module Sτ = wpullback-of-not S.τwpb
            τpf = f~g.hty₁ ⊙ g~h.hty₀ ˢ

  -- end Peq-mor-eq-is-tt-eqrel


  Peq-mor-eq-is-tteqrel : (R S : Peq) → is-tt-eqrel (Peq-mor-eq {R} {S})
  Peq-mor-eq-is-tteqrel R S = record
    { refl = Peq-mor-eq-refl
    ; sym = Peq-mor-eq-sym
    ; tra = Peq-mor-eq-tra
    }
    where open Peq-mor-eq-is-tt-eqrel R S
    

  -- Setoid of Peq-morphisms
  Peq-Hom : (R S : Peq) → setoid
  Peq-Hom R S = record { object = Peq-mor R S 
                       ; _∼_ = Peq-mor-eq {R} {S}
                       ; istteqrel = Peq-mor-eq-is-tteqrel R S
                       }


  module Peq-mor-are-arrows where
    open Peq
    open Peq-mor
    open Peq-mor-eq
    open ecategory-aux-only ℂ
    
    Peq-cmp : {R S T : Peq} → || Peq-Hom S T || → || Peq-Hom R S || → || Peq-Hom R T ||
    Peq-cmp {R} {S} {T} f g = record
      { lo = lo f ∘ lo g 
      ; isext = record
        { hi = hi f ∘ hi g 
        ; cmptb₀ = ass ⊙ ∘e r (cmptb₀ f) ⊙ assˢ ⊙ ∘e (cmptb₀ g) r ⊙ ass
        ; cmptb₁ = ass ⊙ ∘e r (cmptb₁ f) ⊙ assˢ ⊙ ∘e (cmptb₁ g) r ⊙ ass
        }
      }


    Peq-idar : (R : Peq) → || Peq-Hom R R ||
    Peq-idar R = record
      { lo = idar (Lo R)
      ; isext = record
        { hi = idar (Hi R)
        ; cmptb₀ = rid ⊙ lidˢ
        ; cmptb₁ = rid ⊙ lidˢ
        }
      }

    Peq-∘ext : {R S T : Peq} (f f' : || Peq-Hom R S ||) (g g' : || Peq-Hom S T ||)
                  → < Peq-Hom R S > f ~ f' → < Peq-Hom S T > g ~ g'
                    → < Peq-Hom R T > (Peq-cmp g f) ~ (Peq-cmp g' f')
    Peq-∘ext {R} {S} {T} f f' g g' pff pfg = record
      { hty = τ T ∘ Tτ.w⟨ hi g ∘ hty pff , hty pfg ∘ lo f' ⟩[ commsq ]
      ; hty₀ = ass ⊙ ∘e r (τ-ax₀ T) ⊙ assˢ ⊙ ∘e (Tτ.w×/tr₁ commsq) r
               ⊙ ass ⊙ ∘e r (cmptb₀ g) ⊙ assˢ ⊙ ∘e (hty₀ pff) r
      ; hty₁ = ass ⊙ ∘e r (τ-ax₁ T) ⊙ assˢ ⊙ ∘e (Tτ.w×/tr₂ commsq) r
               ⊙ ass ⊙ ∘e r (hty₁ pfg)
      }
      where module Tτ = wpullback-of-not (Peq.τwpb T)
            commsq : < Hom (Lo R) (Lo T) > %1 T ∘ hi g ∘ hty pff ~ %0 T ∘ hty pfg ∘ lo f'
            commsq = ass ⊙ ∘e r (cmptb₁ g) ⊙ assˢ ⊙ ∘e (hty₁ pff) r
                     ⊙ ∘e r (hty₀ pfg ˢ) ⊙ assˢ

    Peq-lid : {R S : Peq} (f : || Peq-Hom R S ||) → < Peq-Hom R S >  Peq-cmp (Peq-idar S) f ~ f
    Peq-lid f = Peq-mor-eq-ext (lid {f = lo f})

    Peq-rid : {R S : Peq} (f : || Peq-Hom R S ||) → < Peq-Hom R S >  Peq-cmp f (Peq-idar R) ~ f
    Peq-rid f = Peq-mor-eq-ext (rid {f = lo f})


    Peq-ass : {R₁ R₂ R₃ R₄ : Peq} (f₁ : || Peq-Hom R₁ R₂ ||)
              (f₂ : || Peq-Hom R₂ R₃ ||) (f₃ : || Peq-Hom R₃ R₄ ||)
                  → < Peq-Hom R₁ R₄ > (Peq-cmp f₃ (Peq-cmp f₂ f₁)) ~ (Peq-cmp (Peq-cmp f₃ f₂) f₁)  
    Peq-ass f g h = Peq-mor-eq-ext ass

  -- end Peq-mor-are-arrows
-- end exact-compl-construction  



--------------------
-- Exact completion
--------------------

exact-compl-cat : (ℂ : ecategory)  → has-fin-weak-limits ℂ → ecategory
exact-compl-cat ℂ hasfwl = record
  { Obj = Peq
  ; Hom = Peq-Hom
  ; isecat = record
               { _∘_ = Peq-cmp
               ; idar = Peq-idar
               ; ∘ext = Peq-∘ext
               ; lidax = Peq-lid
               ; ridax = Peq-rid
               ; assoc = Peq-ass
               }
  }
  where open has-fin-weak-limits hasfwl
        open pseudo-eq-rel-defs ℂ
        open exact-compl-construction haswpb
        open Peq-mor-are-arrows

exact-compl-qcart-cat : (ℂ : ecategory) → is-quasi-cartesian ℂ → ecategory
exact-compl-qcart-cat ℂ qcart = record
  { Obj = Peq
  ; Hom = Peq-Hom
  ; isecat = record
               { _∘_ = Peq-cmp
               ; idar = Peq-idar
               ; ∘ext = Peq-∘ext
               ; lidax = Peq-lid
               ; ridax = Peq-rid
               ; assoc = Peq-ass
               }
  }
  where open is-quasi-cartesian qcart
        open pseudo-eq-rel-defs ℂ
        open exact-compl-construction haswpb
        open Peq-mor-are-arrows


Ex_[_] : (ℂ : ecategory) → has-fin-weak-limits ℂ → ecategory
Ex ℂ [ hasfwl ] = exact-compl-cat ℂ hasfwl


Ex_qc[_] : (ℂ : ecategory) → is-quasi-cartesian ℂ → ecategory
Ex ℂ qc[ qcart ] = exact-compl-qcart-cat ℂ qcart


exact-compl-functor : {ℂ : ecategory} (hasfwl : has-fin-weak-limits ℂ)
                         → efunctor ℂ (Ex ℂ [ hasfwl ])
exact-compl-functor {ℂ} hasfwl = record
  { FObj = freePeq
  ; FHom = freePeq-mor
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
        


Γex_[_] : (ℂ : ecategory) (hasfwl : has-fin-weak-limits ℂ) → efunctor ℂ Ex ℂ [ hasfwl ]
Γex ℂ [ hasfwl ] = exact-compl-functor {ℂ} hasfwl


Γex_qc[_] : (ℂ : ecategory) (qcart : is-quasi-cartesian ℂ) → efunctor ℂ Ex ℂ qc[ qcart ]
Γex ℂ qc[ qcart ] = exact-compl-qcart-functor ℂ qcart
