
-- disable the K axiom:

{-# OPTIONS --without-K #-}

-- Agda version 2.5.4.1

module tt-basics.setoids where

open import tt-basics.basics
open import tt-basics.id-type


-- Setoids

record setoid : Set₁  where
 infix 2 _∼_
 field
   object : Set
   _∼_ : object → object → Set
   istteqrel : is-tt-eqrel _∼_
 open is-tt-eqrel istteqrel public

infix 3 ||_||
infix 2 <_>_~_

||_|| : setoid → Set
|| X || = setoid.object X

<_>_~_ : (X : setoid) → || X || → || X || → Set
< X > a ~ b = setoid._∼_ X a b

{-
refl : (X : setoid) → (a : || X ||) →  < X > a ~ a
refl X a =  (Refl (setoid.isEqrel X)) a 

sym :  (X : setoid) → {a b : || X ||} → < X > a ~ b  →  < X > b ~ a 
sym X {a} {b} p = impE (((Sym (setoid.isEqrel X)) a) b) p

tra :  (X : setoid) → {a c : || X ||} → (b : || X ||)
          → < X > a ~ b  → < X > b ~ c →  < X > a ~ c
tra X {a} {c} b p q = impE (impE ((((Tra (setoid.isEqrel X)) a) b) c) p) q
-}


-- Free setoids

==istteqrel : (A : Set) → is-tt-eqrel (_==_ {A = A})
==istteqrel A = record
  { refl = λ _ → =rf
  ; sym = _⁻¹ 
  ; tra = _■_
  }


Freestd : Set → setoid
Freestd X = record
  { object = X
  ; _∼_ = _==_
  ; istteqrel = ==istteqrel X
  }

==→~ : (A : setoid) {a a' : || A ||} → a == a' → < A > a ~ a'
==→~ A {a} = =J (λ x _ → < A > a ~ x) (refl a)
            where open setoid A




-- Equational reasoning

module setoid-aux (A : setoid) where
  open setoid A

  infix 2 _~_
  infixr 35 _⊙_
  infix 40 _ˢ

  ob : Set
  ob = object
  _~_ : ob → ob → Set
  _~_ = _∼_
    
  r : {a : ob} → a ∼ a
  r {a} = refl a

  _ˢ :  {a a' : ob} → a ~ a' → a' ~ a
  pf ˢ = sym pf
  
  _⊙_ : {a a' a'' : ob} → a ~ a' → a' ~ a'' → a ~ a''
  pf₁ ⊙ pf₂ = tra pf₁ pf₂

  infixr 2 /_~[_]_
  infix 1 ~proof_~[_]_

  ~proof_~[_]_ : (a₁ {a₂ a₃} : ob) →  a₁ ~ a₂ →  a₂ ~ a₃ →  a₁ ~ a₃
  ~proof a₁ ~[ pf ] pf' = tra pf pf'

  /_~[_]_ : (a₁ {a₂ a₃} : || A ||) →  a₁ ~ a₂ →  a₂ ~ a₃ →  a₁ ~ a₃
  / a₁ ~[ pf ] pf' = tra pf pf'

  eqreasend : (a a' : ob) → a ~ a' → a ~ a'
  eqreasend a a' pf = pf

  infix 3 eqreasend --_~[_]_∎
  syntax eqreasend a a' pf = / a ~[ pf ]∎ a' ∎

-- end setoid-aux


-- Setoid functions

record setoidmap (A B : setoid) : Set where
  field
    op : fun || A || || B ||
    ext : {x : || A ||} {y : || A ||}  →  (< A > x ~ y) → (< B > op x ~ (op y))

ap : {A B : setoid} → setoidmap A B → || A || → || B ||
ap f a = setoidmap.op f a


ptw~ : {A B : setoid} → (f g : setoidmap A B) → Set
ptw~ {A} {B} f g = (x : || A ||) →  < B > ((setoidmap.op f) x) ~ ((setoidmap.op g) x)

ptw~-is-tt-eqrel : {A B : setoid} → is-tt-eqrel (ptw~ {A} {B})
ptw~-is-tt-eqrel {A} {B} = record
  { refl = λ f x → B.refl (ap f x)
  ; sym = λ pf x → B.sym (pf x)
  ; tra = λ pf pf' x → B.tra (pf x) (pf' x)
  }
  where module B = setoid B


setoidmaps : (A B : setoid) → setoid
setoidmaps A B = record
  { object = setoidmap A B
  ; _∼_  =  ptw~ {A} {B}
  ; istteqrel = ptw~-is-tt-eqrel {A} {B}
  }


_⇒_ : setoid → setoid → setoid
A ⇒ B = setoidmaps A B



free-stdmap : {X Y : Set} → (X → Y) → setoidmap (Freestd X) (Freestd Y)
free-stdmap f = record
  { op = f
  ; ext = =ap f
  }



std-id : {A : setoid} → || A ⇒ A ||
std-id {A} = record { op = λ x → x
                    ; ext = λ pf → pf
                    }


std-cmp : {A B C : setoid} → || B ⇒ C || → || A ⇒ B || → || A ⇒ C ||
std-cmp g f = record { op = λ x → op g (op f x)
                     ; ext = λ pf → ext g (ext f pf)
                     }
                     where open setoidmap


std-cmp-ext : {A B C : setoid} (g g' : || B ⇒ C ||) (f f' : || A ⇒ B ||)
                 → < B ⇒ C >  g ~ g' → < A ⇒ B > f ~ f'
                   → < A ⇒ C > std-cmp g f ~ std-cmp g' f'
std-cmp-ext {C = C} g g' f f' pfg pff x = pfg (op f x) ⊙ ext g' (pff x)
                                        where open setoidmap
                                              open setoid-aux C



-- Extensional properties

record is-ext-small-prop {X : setoid} (P : || X || → Set) : Set where
  field
    trnsp : {x x' : || X ||} → < X > x ~ x' → P x → P x'

record is-ext-prop {X : setoid} (P : || X || → Set₁) : Set₁ where
  field
    trnsp : {x x' : || X ||} → < X > x ~ x' → P x → P x'
                 



