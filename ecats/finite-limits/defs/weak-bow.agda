
{-# OPTIONS --without-K #-}

module ecats.finite-limits.defs.weak-bow where

open import ecats.basic-defs.ecat-def&not
open import ecats.basic-defs.commut-shapes


-- weak bow limits of two spans sp₁, sp₂  over the same two objects
-- when sp₁ = sp₂, it is the weak kernel pair of sp₁



module weak-bow-defs (ℂ : ecategory) where
  open ecategory-aux ℂ
  open comm-shapes ℂ
  open span/

   

  record is-wbow {DL DR : Obj} {sp₁ sp₂ : span/ DL DR} {wbow : span/ (O12 sp₁) (O12 sp₂)}
                 (×//sqpf₁ : a1 sp₁ ∘ a1 wbow ~ a1 sp₂ ∘ a2 wbow) (×//sqpf₂ : a2 sp₁ ∘ a1 wbow ~ a2 sp₂ ∘ a2 wbow) : Set₁
                 where
                       --{wbowOb : Obj} {π//₁ : || Hom wbowOb (O12 sp₁) ||} {π//₂ : || Hom wbowOb (O12 sp₂) ||}
    --constructor mkis-wbow-lim
    private
      module sp₁ = span/ sp₁
      module sp₂ = span/ sp₂
      module w×// = span/ wbow
    field
      ⟨_,_⟩[_,_] : {X : Obj} (f₁ : || Hom X sp₁.O12 ||) (f₂ : || Hom X sp₂.O12 ||)
                          → sp₁.a1 ∘ f₁ ~ sp₂.a1 ∘ f₂ → sp₁.a2 ∘ f₁ ~ sp₂.a2 ∘ f₂
                            → || Hom X w×//.O12 ||
      tr₁ : {X : Obj} {f₁ : || Hom X sp₁.O12 ||} {f₂ : || Hom X sp₂.O12 ||}
                (pf₁ : sp₁.a1 ∘ f₁ ~ sp₂.a1 ∘ f₂) (pf₂ : sp₁.a2 ∘ f₁ ~ sp₂.a2 ∘ f₂)
                  → w×//.a1 ∘ ⟨ f₁ , f₂ ⟩[ pf₁ , pf₂ ] ~ f₁
      tr₂ : {X : Obj} {f₁ : || Hom X sp₁.O12 ||} {f₂ : || Hom X sp₂.O12 ||}
                (pf₁ : sp₁.a1 ∘ f₁ ~ sp₂.a1 ∘ f₂) (pf₂ : sp₁.a2 ∘ f₁ ~ sp₂.a2 ∘ f₂)
                  → w×//.a2 ∘ ⟨ f₁ , f₂ ⟩[ pf₁ , pf₂ ] ~ f₂
    

  record wbow-of {DL DR : Obj} (sp₁ sp₂ : span/ DL DR) : Set₁ where
    --constructor mkwbow-of
    private
      module sp₁ = span/ sp₁
      module sp₂ = span/ sp₂
    field
      {sp} : span/ sp₁.O12 sp₂.O12
    open span/ sp renaming (O12 to Ob; a1 to wπ//₁; a2 to wπ//₂) public
      --{wBow} : Obj
      --{π//₁} : || Hom wBow sp₁.O12 ||
      --{π//₂} : || Hom wBow sp₂.O12 ||
    field
      {sqpf₁} : sp₁.a1 ∘ wπ//₁  ~ sp₂.a1 ∘ wπ//₂
      {sqpf₂} : sp₁.a2 ∘ wπ//₁ ~ sp₂.a2 ∘ wπ//₂
      is-wbw : is-wbow {wbow = sp} sqpf₁ sqpf₂
    open is-wbow is-wbw public


-- end wbow-defs


record has-weak-bows (ℂ : ecategory) : Set₁ where
  open ecategory-aux ℂ
  open comm-shapes ℂ
  open weak-bow-defs ℂ
  field
    wbw-of : {DL DR : Obj} (sp₁ sp₂ : span/ DL DR) → wbow-of sp₁ sp₂
  module wbowl {DL DR : Obj} {sp₁ sp₂ : span/ DL DR} = wbow-of (wbw-of sp₁ sp₂)
  open wbowl public
  _w×//ₒ_ : {DL DR : Obj} (sp₁ sp₂ : span/ DL DR) → Obj
  sp₁ w×//ₒ sp₂ = Ob {sp₁ = sp₁} {sp₂ = sp₂}
