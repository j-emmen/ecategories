
{-# OPTIONS --without-K #-}

module ecats.concr-ecats.finite-ecat where

open import tt-basics.basics
--open import tt-basics.id-type
open import tt-basics.setoids renaming (||_|| to ||_||std)
open import ecats.basic-defs.ecat-def&not
open import ecats.concr-ecats.Std



𝟚 : small-ecategory
𝟚 = record
  { Obj = sum N₁ N₁
  ; Hom = 𝟚Hom
  ; isecat = record
           { _∘_ = {!!}
           ; idar = {!!}
           ; ∘ext = {!!}
           ; lidax = {!!}
           ; ridax = {!!}
           ; assoc = {!!}
           }
  }
  where
    𝟚Hom : sum N₁ N₁ → sum N₁ N₁ → setoid
    𝟚Hom (inl x) (inl y) = Freestd N₁
    𝟚Hom (inl x) (inr y) = Freestd N₁
    𝟚Hom (inr x) (inl x₁) = Freestd N₀
    𝟚Hom (inr x) (inr x₁) = Freestd N₁
    cmp : {a b c : sum N₁ N₁} → || 𝟚Hom b c || → || 𝟚Hom a b ||
             → || 𝟚Hom a c ||
    cmp g f = {!!}
