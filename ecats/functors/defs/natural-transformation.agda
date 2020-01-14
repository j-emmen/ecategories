 
-- disable the K axiom:

{-# OPTIONS --without-K #-}

-- Agda version 2.5.4.1

module ecats.functors.defs.natural-transformation where

open import ecats.basic-defs.ecat-def&not
open import ecats.basic-defs.isomorphism
open import ecats.functors.defs.efunctor


-- Natural transformations

record natural-transformation {ℂ 𝔻 : ecategory} (F G : efunctor ℂ 𝔻) : Set₁ where
  private
    module ℂ = ecategory ℂ
    module 𝔻 = ecategory 𝔻
    module F = efunctor F
    module G = efunctor G
  field
    fnc : {A : ℂ.Obj} → || 𝔻.Hom (F.ₒ A) (G.ₒ A) ||
    nat : {A B : ℂ.Obj} → (f : || ℂ.Hom A B ||)
             → fnc 𝔻.∘ (F.ₐ f) 𝔻.~ (G.ₐ f) 𝔻.∘ fnc

record natural-iso {ℂ 𝔻 : ecategory} (F G : efunctor ℂ 𝔻) : Set₁ where
  private
    module ℂ = ecategory ℂ
    module 𝔻 = ecategory 𝔻
    module F = efunctor F
    module G = efunctor G
  field
    natt : natural-transformation F G
    natt⁻¹ : natural-transformation G F
  --open natural-transformation natt renaming (fnc to φ; nat to φnat)
  --open natural-transformation natt⁻¹ renaming (fnc to φ⁻¹; nat to φ⁻¹nat)
  private
    module natt = natural-transformation natt
    module natt⁻¹ = natural-transformation natt⁻¹
  open iso-defs 𝔻
  field
    isiso : {A : ℂ.Obj} → is-iso-pair (natt.fnc {A}) (natt⁻¹.fnc {A})
    --idDom : (A : ℂ.Obj) → φ⁻¹ 𝔻.∘ φ 𝔻.~ 𝔻.idar (F.ₒ A)
    --idCod : (A : ℂ.Obj) → φ 𝔻.∘ φ⁻¹ 𝔻.~ 𝔻.idar (G.ₒ A)
