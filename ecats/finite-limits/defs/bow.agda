
{-# OPTIONS --without-K #-}

module ecats.finite-limits.defs.bow where

open import ecats.basic-defs.ecat-def&not
open import ecats.basic-defs.commut-shapes


-- weak bow limits of two spans sp₁, sp₂  over the same two objects
-- when sp₁ = sp₂, it is the weak kernel pair of sp₁





-- bow limits of two spans sp₁, sp₂  over the same two objects
-- when sp₁ = sp₂, it is the kernel pair of sp₁

module bow-defs (ℂ : ecategory) where
  open ecategory-aux ℂ
  open comm-shapes ℂ
  open span/

   

  record is-bow {DL DR : Obj} {sp₁ sp₂ : span/ DL DR} {bow : span/ (O12 sp₁) (O12 sp₂)}
                (×//sqpf₁ : a1 sp₁ ∘ a1 bow ~ a1 sp₂ ∘ a2 bow) (×//sqpf₂ : a2 sp₁ ∘ a1 bow ~ a2 sp₂ ∘ a2 bow) : Set₁
                where
                       --{bowOb : Obj} {π//₁ : || Hom bowOb (O12 sp₁) ||} {π//₂ : || Hom bowOb (O12 sp₂) ||}
    --constructor mkis-bow-lim
    private
      module sp₁ = span/ sp₁
      module sp₂ = span/ sp₂
      module ×// = span/ bow
    field
      ⟨_,_⟩[_,_] : {X : Obj} (f₁ : || Hom X sp₁.O12 ||) (f₂ : || Hom X sp₂.O12 ||)
                         → sp₁.a1 ∘ f₁ ~ sp₂.a1 ∘ f₂ → sp₁.a2 ∘ f₁ ~ sp₂.a2 ∘ f₂
                           → || Hom X ×//.O12 ||
      tr₁ : {X : Obj} {f₁ : || Hom X sp₁.O12 ||} {f₂ : || Hom X sp₂.O12 ||}
               (pf₁ : sp₁.a1 ∘ f₁ ~ sp₂.a1 ∘ f₂) (pf₂ : sp₁.a2 ∘ f₁ ~ sp₂.a2 ∘ f₂)
                 → ×//.a1 ∘ ⟨ f₁ , f₂ ⟩[ pf₁ , pf₂ ] ~ f₁
      tr₂ : {X : Obj} {f₁ : || Hom X sp₁.O12 ||} {f₂ : || Hom X sp₂.O12 ||}
               (pf₁ : sp₁.a1 ∘ f₁ ~ sp₂.a1 ∘ f₂) (pf₂ : sp₁.a2 ∘ f₁ ~ sp₂.a2 ∘ f₂)
                 → ×//.a2 ∘ ⟨ f₁ , f₂ ⟩[ pf₁ , pf₂ ] ~ f₂
      uq :  {X : Obj} {h h' : || Hom X ×//.O12 ||}
                  → ×//.a1 ∘ h ~ ×//.a1 ∘ h' → ×//.a2 ∘ h ~ ×//.a2 ∘ h'
                    → h ~ h'
  

  record bow-of {DL DR : Obj} (sp₁ sp₂ : span/ DL DR) : Set₁ where
    --constructor mkbow-of
    private
      module sp₁ = span/ sp₁
      module sp₂ = span/ sp₂
    field
      {sp} : span/ sp₁.O12 sp₂.O12
    open span/ sp renaming (O12 to Ob; a1 to π//₁; a2 to π//₂) public
    field
      {sqpf₁} : sp₁.a1 ∘ π//₁  ~ sp₂.a1 ∘ π//₂
      {sqpf₂} : sp₁.a2 ∘ π//₁ ~ sp₂.a2 ∘ π//₂
      is-bw : is-bow {bow = sp} sqpf₁ sqpf₂
    open is-bow is-bw public
    
-- end bow-defs


record has-bows (ℂ : ecategory) : Set₁ where
  open ecategory-aux ℂ
  open comm-shapes ℂ
  open bow-defs ℂ
  field
    bw-of : {DL DR : Obj} (sp₁ sp₂ : span/ DL DR) → bow-of sp₁ sp₂
  module bowl {DL DR : Obj} {sp₁ sp₂ : span/ DL DR} = bow-of (bw-of sp₁ sp₂)
  open bowl public
  _×//ₒ_ : {DL DR : Obj} (sp₁ sp₂ : span/ DL DR) → Obj
  sp₁ ×//ₒ sp₂ = Ob {sp₁ = sp₁} {sp₂ = sp₂}
