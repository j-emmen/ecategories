 
-- disable the K axiom:

{-# OPTIONS --without-K #-}

-- Agda version 2.5.4.1

module ecats.finite-limits.not.weak-pullback where

open import ecats.basic-defs.ecat-def&not
open import ecats.basic-defs.commut-shapes
open import ecats.finite-limits.defs.weak-pullback
open import ecats.finite-limits.defs.pullback



-- notation for and properties of weak pullback squares

module wpullback-squares-not (ℂ : ecategory) where
  open ecategory-aux ℂ
  open comm-shapes ℂ
  open wpullback-defs ℂ
  

  module wpullback-sq-not-only (wpbsq : wpullback-sq) where
    --open comm-square sq renaming (left to wπ/₁; up to wπ/₂; sq-pf to w×/sq)
    open wpullback-sq wpbsq

    w×/pbsq : wpullback-sq
    w×/pbsq = wpbsq

    w×/of : wpullback-of down right
    w×/of = mkwpb-of w×/iswpbsq

    w×/tr₁g : {C : Obj} {h h' : || Hom C dl ||} {k : || Hom C ur ||} (pf : down ∘ h ~ right ∘ k)
                 → h ~ h' → wπ/₁ ∘ w⟨ h , k ⟩[ pf ] ~ h'
    w×/tr₁g pf pfdl = w×/tr₁ pf ⊙ pfdl

    w×/tr₂g : {C : Obj} {h : || Hom C dl ||} {k k' : || Hom C ur ||} (pf : down ∘ h ~ right ∘ k)
                → k ~ k' → wπ/₂ ∘ w⟨ h , k ⟩[ pf ] ~ k'
    w×/tr₂g pf pfur = w×/tr₂ pf ⊙ pfur

  -- end wpullback-sq-not-only

  
  module wpullback-sq-not (wpbsq : wpullback-sq) where
    --open comm-square sq renaming (left to wπ/₁; up to wπ/₂; sq-pf to w×/sq) public
    open wpullback-sq wpbsq public
    open wpullback-sq-not-only wpbsq public
  -- end wpullback-sq-not

  module wpullback-of-not {I A B} {a : || Hom A I ||} {b : || Hom B I ||} (wpbof : wpullback-of a b) where
    open wpullback-of wpbof public
    open wpullback-sq-not-only (mkwpb-sq w×/iswpbsq) public
  -- end wpullback-of-not


  module w×/ₐdef {I A₁ B₁ : Obj} {a₁ : || Hom A₁ I ||} {b₁ : || Hom B₁ I ||}
                 {A₂ B₂ : Obj} {a₂ : || Hom A₂ I ||} {b₂ : || Hom B₂ I ||}
                 (wpbsq₁ : wpullback-of a₁ b₁) (wpbsq₂ : wpullback-of a₂ b₂) where
    private
      module w×/₁ = wpullback-sq-not (mkwpb-sq (wpullback-of.w×/iswpbsq wpbsq₁))
      module w×/₂ = wpullback-sq-not (mkwpb-sq (wpullback-of.w×/iswpbsq wpbsq₂))

    w×/ₐcanpf : {f : || Hom w×/₂.dl w×/₁.dl ||} {g : || Hom w×/₂.ur w×/₁.ur ||}
                   → w×/₁.down ∘ f ~ w×/₂.down → w×/₁.right ∘ g ~ w×/₂.right
                     → w×/₁.down ∘ f ∘ w×/₂.wπ/₁ ~ w×/₁.right ∘ g ∘ w×/₂.wπ/₂
    w×/ₐcanpf {f} {g} pff pfg = ~proof w×/₁.down ∘ f ∘ w×/₂.wπ/₁      ~[ ass ⊙ ∘e r pff ] /
                                        w×/₂.down ∘ w×/₂.wπ/₁        ~[ w×/₂.w×/sqpf ] /
                                        w×/₂.right ∘ w×/₂.wπ/₂       ~[ ∘e r (pfg ˢ) ⊙ assˢ ]∎
                                        w×/₁.right ∘ g ∘ w×/₂.wπ/₂ ∎

    infixr 6 _w×/ₐ_[_,_]
    _w×/ₐ_[_,_] : (f : || Hom w×/₂.dl w×/₁.dl ||) (g : || Hom w×/₂.ur w×/₁.ur ||)
                     → w×/₁.down ∘ f ~ w×/₂.down → w×/₁.right ∘ g ~ w×/₂.right
                       → || Hom w×/₂.ul w×/₁.ul ||
    f w×/ₐ g [ pff , pfg ] = w×/₁.w⟨ f ∘ w×/₂.wπ/₁ , g ∘ w×/₂.wπ/₂ ⟩[ w×/ₐcanpf pff pfg ] 

  -- end w×/ₐdef

-- end wpullback-squares-not






-- notation and basic properties of chosen products
-- empty record instead of module to avoid further reduction of notation. not sure it works

record weak-pullbacks-aux {ℂ : ecategory} (wpb : has-weak-pullbacks ℂ) : Set₁ where
  open ecategory-aux ℂ
  open comm-shapes ℂ
  open wpullback-defs ℂ
  open wpullback-squares-not ℂ
  open has-weak-pullbacks wpb public

  module w×/ᶜnot-only {I A B : Obj} {a : || Hom A I ||} {b : || Hom B I ||} = wpullback-sq-not-only (mkwpb-sq (w×/iswpbsq {a = a} {b}))
  open w×/ᶜnot-only public

  module w×/ₐᶜdef {I A B : Obj} {a : || Hom A I ||} {b : || Hom B I ||}
                  {A' B' : Obj} {a' : || Hom A' I ||} {b' : || Hom B' I ||} = w×/ₐdef (wpb-of a b) (wpb-of a' b')
  open w×/ₐᶜdef public
    
-- end weak-pullbacks-aux

wpb-aux : {ℂ : ecategory}(wpb : has-weak-pullbacks ℂ) → weak-pullbacks-aux wpb
wpb-aux wpb = record {}
