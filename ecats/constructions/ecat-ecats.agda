 
-- disable the K axiom:

{-# OPTIONS --without-K #-}

-- Agda version 2.5.4.1

module ecats.constructions.ecat-ecats where

open import tt-basics.basics using (is-tt-eqrel)
open import tt-basics.setoids hiding (||_||)
open import ecats.basic-defs.ecat-def&not
open import ecats.basic-defs.isomorphism
open import ecats.functors.defs.efunctor-d&n
open import ecats.functors.defs.natural-transformation


-- Large E-category of locally small E-ecategories

natiso-is-tt-eqrel : (ℂ 𝔻 : ecategory) → is-tt-eqrel (_≅ₐ_ {ℂ} {𝔻})
natiso-is-tt-eqrel ℂ 𝔻 = record
  { refl = λ F → natiso-id {F = F}
  ; sym = natiso-sym
  ; tra = λ α β → natiso-vcmp β α
  }

efunct-std : (ℂ 𝔻 : ecategory) → setoid
efunct-std ℂ 𝔻 = record
           { object = efunctor ℂ 𝔻
           ; _∼_ = _≅ₐ_ {ℂ} {𝔻}
           ; istteqrel = natiso-is-tt-eqrel ℂ 𝔻
           }


ECat : Large-ecategory
ECat = record
     { Obj = ecategory
     ; Hom = efunct-std
     ; isecat = record
                  { _∘_ = _○_
                  ; idar = λ ℂ → IdF {ℂ}
                  ; ∘ext = λ _ _ _ _ α β → natiso-hcmp β α
                  ; lidax = λ F → ○lid {F = F}
                  ; ridax = λ F → ○rid {F = F}
                  ; assoc = λ F G H → ○ass {F = F} {G} {H}
                  }
     }
