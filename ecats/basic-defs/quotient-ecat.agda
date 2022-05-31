
{-# OPTIONS --without-K #-}

module ecats.basic-defs.quotient-ecat where

open import tt-basics.basics
open import tt-basics.setoids using (setoid)
open import ecats.basic-defs.ecat-def&not
open import ecats.functors.defs.efunctor-d&n


module HomEqvrel-defs (ℂ : ecategory) where
  open ecategory-aux ℂ

  record isHomEqvrel (R : {X Y : Obj} → || Hom X Y || → || Hom X Y || → Set) : Set₁ where
    field
      istteqrel : {X Y : Obj} → is-tt-eqrel (R {X} {Y})
      isext : {X Y : Obj} {f f' : || Hom X Y ||} → f ~ f' → R f f'
      is∘cngr : {X Y Z : Obj} {f f' : || Hom X Y ||} {g g' : || Hom Y Z ||}
                   → R f f' → R g g' → R (g ∘ f) (g' ∘ f')

-- end HomEqvrel-defs


record HomEqvrel (ℂ : ecategory) : Set₁ where
  open ecategory ℂ
  open HomEqvrel-defs ℂ
  field
    Rel : {X Y : Obj} → || Hom X Y || → || Hom X Y || → Set
    ishomeqr : isHomEqvrel Rel
  open isHomEqvrel ishomeqr public





module quotient-ecategory (ℂ : ecategory) where
  private
    module ℂ where
      open ecategory ℂ public
      open HomEqvrel-defs ℂ public
      

  module quotient-ecat (HR : HomEqvrel ℂ) where
    private
      module HR = HomEqvrel HR

    QℂHom : (X Y : ℂ.Obj) → setoid
    QℂHom X Y = record
      { object = || ℂ.Hom X Y ||
      ; _∼_ = HR.Rel {X} {Y}
      ; istteqrel = HR.istteqrel
      }

    Qℂ : ecategory
    Qℂ = record
      { Obj = ℂ.Obj
      ; Hom = QℂHom
      ; isecat = record
               { _∘_ = ℂ._∘_
               ; idar = ℂ.idar
               ; ∘ext = λ f f' g g' → HR.is∘cngr {f = f} {f'} {g} {g'}
               ; lidax = λ f → HR.isext (ℂ.lidax f)
               ; ridax = λ f → HR.isext (ℂ.ridax f)
               ; assoc = λ f g h → HR.isext (ℂ.assoc f g h)
               }
      }

    qℂ : efunctor ℂ Qℂ
    qℂ = record
      { FObj = λ X → X
      ; FHom = λ f → f
      ; isF = record
            { ext = HR.isext
            ; id = λ {_} → r
            ; cmp = λ _ _ → r
            }
      }
      where open ecategory-aux-only Qℂ

  -- end quotient-ecat
-- end quotient-ecategory


quotient-ecategory : {ℂ : ecategory} → HomEqvrel ℂ → ecategory
quotient-ecategory {ℂ} HR = Qℂ
                          where open quotient-ecategory ℂ
                                open quotient-ecat HR


[_/_] : (ℂ : ecategory) → HomEqvrel ℂ → ecategory
[ ℂ / HR ] = quotient-ecategory {ℂ} HR


quotFunctor : {ℂ : ecategory} (HR : HomEqvrel ℂ) → efunctor ℂ [ ℂ / HR ]
quotFunctor {ℂ} HR = qℂ
                   where open quotient-ecategory ℂ
                         open quotient-ecat HR


