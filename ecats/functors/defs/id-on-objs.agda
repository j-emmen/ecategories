
{-# OPTIONS --without-K #-}

module ecats.functors.defs.id-on-objs where

open import Agda.Primitive
open import tt-basics.setoids hiding (||_||)
open import ecats.basic-defs.ecat-def&not
open import ecats.functors.defs.efunctor-d&n


module id-on-objs-defs {Obj : Set₁}{HomC HomD : Obj → Obj → setoid}
                       (isecatC : is-ecategory Obj HomC)(isecatD : is-ecategory Obj HomD)
                       where
  module dom = ecategory (mkecat isecatC)
  module cod = ecategory (mkecat isecatD)
  
  record is-idobj-functorial (F : {A B : Obj} → || HomC A B || → || HomD A B ||) : Set₁ where
    field
      ext : {A B : dom.Obj} {f f' : || dom.Hom A B ||}
              → f dom.~ f' → F f cod.~ F f'
      id : {A : dom.Obj}
              → F (dom.idar A) cod.~ cod.idar A
      cmp : {A B C : dom.Obj} (f : || dom.Hom A B ||) (g : || dom.Hom B C ||)
               → F g cod.∘ F f cod.~ F (g dom.∘ f)
-- end id-on-objs-defs


record idobj-efunctor {Obj : Set₁}{HomC HomD : Obj → Obj → setoid {lzero}}
                     (isecatC : is-ecategory Obj HomC)(isecatD : is-ecategory Obj HomD)
                     : Set₁ where
  open id-on-objs-defs isecatC isecatD
  field
    ₐ : {A B : Obj} → || HomC A B || → || HomD A B ||
    isfnct : is-idobj-functorial ₐ
  open is-idobj-functorial isfnct public

idobj-efunctor-is-efunctor : {Obj : Set₁}{HomC HomD : Obj → Obj → setoid {lzero}}
                             {isecatC : is-ecategory Obj HomC}{isecatD : is-ecategory Obj HomD}
                               → idobj-efunctor isecatC isecatD
                                 → efunctor (mkecat isecatC) (mkecat isecatD)
idobj-efunctor-is-efunctor {isecatC = isecatC} {isecatD} F = record
  { FObj = λ z → z
  ; FHom = F.ₐ
  ; isF = record
        { ext = F.ext
        ; id = F.id
        ; cmp = F.cmp
        }
  }
  where module F = idobj-efunctor F

module idobj-efunctor-aux-only {Obj : Set₁}{HomC HomD : Obj → Obj → setoid {lzero}}
                               {isecatC : is-ecategory Obj HomC}{isecatD : is-ecategory Obj HomD}
                               (F : idobj-efunctor isecatC isecatD)
                               where
  open efunctor-aux-only (idobj-efunctor-is-efunctor F) public
-- end idobj-efunctor-aux-only

module idobj-efunctor-aux {Obj : Set₁}{HomC HomD : Obj → Obj → setoid {lzero}}
                          {isecatC : is-ecategory Obj HomC}{isecatD : is-ecategory Obj HomD}
                            (F : idobj-efunctor isecatC isecatD)
                               where
  open idobj-efunctor F public
  open idobj-efunctor-aux-only F public
-- end idobj-efunctor-aux


IdioF : {Obj : Set₁}{HomC : Obj → Obj → setoid {lzero}}{isecatC : is-ecategory Obj HomC}
             → idobj-efunctor isecatC isecatC
IdioF {isecatC = isecatC} = record
  { ₐ = λ f → f
  ; isfnct = record
           { ext = λ pf → pf
           ; id = r
           ; cmp = λ f g → r
           }
  }
  where open ecategory-aux (mkecat isecatC) using (r)


infixr 10 _io○_
_io○_ : {Obj : Set₁}{HomC HomD HomE : Obj → Obj → setoid {lzero}}{isecatC : is-ecategory Obj HomC}
        {isecatD : is-ecategory Obj HomD}{isecatE : is-ecategory Obj HomE}
        (G : idobj-efunctor isecatD isecatE)(F : idobj-efunctor isecatC isecatD)
          → idobj-efunctor isecatC isecatE
_io○_ {isecatC = isecatC} {isecatD} {isecatE} G F = record
  { ₐ = λ f → G.ₐ (F.ₐ f)
  ; isfnct = record
           { ext = λ pf → G.ext (F.ext pf)
           ; id = λ {A} → G.ext F.id 𝔼.⊙ G.id
           ; cmp = λ f g → G.cmp (F.ₐ f) (F.ₐ g) 𝔼.⊙ G.ext (F.cmp f g)
           }
  }
  where module 𝔼 = ecategory-aux (mkecat isecatE)
        module F = idobj-efunctor-aux F
        module G = idobj-efunctor-aux G



record is-idobj-iso-pair {Obj : Set₁}{HomC HomD : Obj → Obj → setoid {lzero}}
                         {isecatC : is-ecategory Obj HomC}{isecatD : is-ecategory Obj HomD}
                         (F : idobj-efunctor isecatC isecatD)(G : idobj-efunctor isecatD isecatC)
                         : Set₁ where
  module dom = ecategory-aux (mkecat isecatC)
  module cod = ecategory-aux (mkecat isecatD)
  module F = idobj-efunctor-aux F
  module G = idobj-efunctor-aux G
  field
    iddom : {A B : Obj}(f : || HomC A B ||) → G.ₐ (F.ₐ f) dom.~ f
    idcod : {A B : Obj}(g : || HomD A B ||) → F.ₐ (G.ₐ g) cod.~ g

record is-idobj-isomorphism {Obj : Set₁}{domHom codHom : Obj → Obj → setoid {lzero}}
                            {dom : is-ecategory Obj domHom}{cod : is-ecategory Obj codHom}
                            (F : idobj-efunctor dom cod)
                            : Set₁ where
  field
    inv : idobj-efunctor cod dom
    isisopair : is-idobj-iso-pair F inv
