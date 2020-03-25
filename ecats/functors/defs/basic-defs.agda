 
-- disable the K axiom:

{-# OPTIONS --without-K #-}

-- Agda version 2.5.4.1

module ecats.functors.defs.basic-defs where

open import ecats.basic-defs.ecat-def&not
open import ecats.basic-defs.isomorphism
open import ecats.functors.defs.efunctor-d&n
open import ecats.functors.defs.natural-transformation



-- Adjunctions

record adjunction {ℂ 𝔻 : ecategory} (L : efunctor ℂ 𝔻) (R : efunctor 𝔻 ℂ) : Set₁ where
  private
    module ℂ = ecategory ℂ
    module 𝔻 = ecategory 𝔻
    module L = efunctor L
    module R = efunctor R
  field
    η : natural-transformation IdF (R ○ L)
    ε : natural-transformation (L ○ R) IdF
  open natural-transformation ε renaming (fnc to ε-f; nat to ε-n)
  open natural-transformation η renaming (fnc to η-f; nat to η-n)
  field
    trid₁ : {X : ℂ.Obj} → ε-f 𝔻.∘ (L.ₐ η-f) 𝔻.~ 𝔻.idar (L.ₒ X)
    trid₂ : {A : 𝔻.Obj} → η-f ℂ.∘ (R.ₐ ε-f) ℂ.~ ℂ.idar (R.ₒ (L.ₒ (R.ₒ A)))

infix 3 _⊣_

_⊣_ : {ℂ 𝔻 : ecategory} → (L : efunctor ℂ 𝔻) → (R : efunctor 𝔻 ℂ) → Set₁
L ⊣ R = adjunction L R


-- Equivalences

record is-equivalence-pair {ℂ 𝔻 : ecategory} (F : efunctor ℂ 𝔻) (G : efunctor 𝔻 ℂ) : Set₁ where
  field
    ι1 : natural-iso (F ○ G) IdF
    ι2 : natural-iso (G ○ F) IdF


record is-equivalence {ℂ 𝔻 : ecategory} (F : efunctor ℂ 𝔻) : Set₁ where
  field
    invF : efunctor 𝔻 ℂ
    iseqv : is-equivalence-pair F invF
  open is-equivalence-pair iseqv public



-- Other properties of funtors

record is-full {ℂ 𝔻 : ecategory} (F : efunctor ℂ 𝔻) : Set₁ where
  private
    module ℂ = ecategory ℂ
    module 𝔻 = ecategory 𝔻
    module F = efunctor F
  field
    full-ar : {X Y : ℂ.Obj} → || 𝔻.Hom (F.ₒ X) (F.ₒ Y) || → || ℂ.Hom X Y ||
    full-pf : {X Y : ℂ.Obj} {g : || 𝔻.Hom (F.ₒ X) (F.ₒ Y) ||}
                    → F.ₐ (full-ar g) 𝔻.~ g
  full-pfˢ : {X Y : ℂ.Obj} {g : || 𝔻.Hom (F.ₒ X) (F.ₒ Y) ||}
                    → g 𝔻.~ F.ₐ (full-ar g)
  full-pfˢ =  full-pf ˢ
           where open ecategory-aux-only 𝔻
  full-pfg : {X Y : ℂ.Obj} {g g' : || 𝔻.Hom (F.ₒ X) (F.ₒ Y) ||}
                    → g 𝔻.~ g' → F.ₐ (full-ar g) 𝔻.~ g'
  full-pfg pf = full-pf ⊙ pf
              where open ecategory-aux-only 𝔻
  full-pfgˢ : {X Y : ℂ.Obj} {g g' : || 𝔻.Hom (F.ₒ X) (F.ₒ Y) ||}
                    → g 𝔻.~ g' → g' 𝔻.~ F.ₐ (full-ar g)
  full-pfgˢ pf = full-pfg pf ˢ
              where open ecategory-aux-only 𝔻


record is-faithful {ℂ 𝔻 : ecategory} (F : efunctor ℂ 𝔻) : Set₁ where
  private
    module ℂ = ecategory ℂ
    module 𝔻 = ecategory 𝔻
    module F = efunctor F
  field
    faith-pf : {X Y : ℂ.Obj} {f g : || ℂ.Hom X Y ||}
                  → F.ₐ f 𝔻.~ F.ₐ g → f ℂ.~ g


record is-ess-surjective {ℂ 𝔻 : ecategory} (F : efunctor ℂ 𝔻) : Set₁ where
  private
    module ℂ = ecategory ℂ
    module 𝔻 = ecategory 𝔻
    module F = efunctor F
  open iso-defs 𝔻
  field
    esurj-ob : 𝔻.Obj → ℂ.Obj
    esurj-ar : (Y : 𝔻.Obj) → || 𝔻.Hom (F.ₒ (esurj-ob Y)) Y ||
    esurj-iso : (Y : 𝔻.Obj) → is-iso (esurj-ar Y)



-- Essential equivalences

record is-ess-equivalence {ℂ 𝔻 : ecategory} (F : efunctor ℂ 𝔻) : Set₁ where
  private
    module ℂ = ecategory ℂ
    module 𝔻 = ecategory 𝔻
    module F = efunctor F
  field
    isfull : is-full F
    isfaithful : is-faithful F
    isesurjobj : is-ess-surjective F
