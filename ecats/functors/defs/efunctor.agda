 
-- disable the K axiom:

{-# OPTIONS --without-K #-}

-- Agda version 2.5.4.1

module ecats.functors.defs.efunctor where

open import ecats.basic-defs.ecat-def&not


-- E-functors

record efunctor (ℂ 𝔻 : ecategory) : Set₁ where
  private
    module ℂ = ecategory ℂ
    module 𝔻 = ecategory 𝔻
  field
    FObj : ℂ.Obj → 𝔻.Obj
    FHom : {A B : ℂ.Obj}
              → || ℂ.Hom A B || → || 𝔻.Hom (FObj A) (FObj B) ||
    ext : {A B : ℂ.Obj} {f f' : || ℂ.Hom A B ||}
              → f ℂ.~ f' → FHom f 𝔻.~ FHom f'
    id : {A : ℂ.Obj}
             → FHom (ℂ.idar A) 𝔻.~ 𝔻.idar (FObj A)
    cmp : {A B C : ℂ.Obj} (f : || ℂ.Hom A B ||) (g : || ℂ.Hom B C ||)
              → FHom g 𝔻.∘ FHom f 𝔻.~ FHom (g ℂ.∘ f)
  ₒ : ℂ.Obj → 𝔻.Obj
  ₒ = FObj
  ₐ : {A B : ℂ.Obj}
            → || ℂ.Hom A B || → || 𝔻.Hom (FObj A) (FObj B) ||
  ₐ = FHom
  idˢ : {A : ℂ.Obj} → 𝔻.idar (FObj A) 𝔻.~ FHom (ℂ.idar A)
  idˢ {A} = id {A} ˢ
          where open ecategory-aux-only 𝔻



IdF : {ℂ : ecategory} → efunctor ℂ ℂ
IdF {ℂ} = record
  { FObj = λ A → A
  ; FHom = λ f → f
  ; ext = λ pf → pf
  ; id = r
  ; cmp = λ f g → r
  }
  where open ecategory-aux ℂ


efunctor-cmp : {ℂ 𝔻 𝔼 : ecategory} → efunctor 𝔻 𝔼 → efunctor ℂ 𝔻 → efunctor ℂ 𝔼
efunctor-cmp {ℂ} {𝔻} {𝔼} G F = record { FObj = λ A → G.ₒ (F.ₒ A) ;
                                          FHom = λ f → G.ₐ (F.ₐ f) ;
                                          ext = λ pf → G.ext (F.ext pf) ;
                                          id =  (G.ext F.id) 𝔼.⊙ G.id ;
                                          cmp = λ f g → G.cmp _ _ 𝔼.⊙ (G.ext (F.cmp f g))
                                        }
                          where module 𝔼 = ecategory-aux 𝔼
                                module F = efunctor F
                                module G = efunctor G

infix 5 _○_
_○_ : {ℂ 𝔻 𝔼 : ecategory} → efunctor 𝔻 𝔼 → efunctor ℂ 𝔻 → efunctor ℂ 𝔼
G ○ F = efunctor-cmp G F
