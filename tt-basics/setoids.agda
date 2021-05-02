
{-# OPTIONS --without-K #-}

module tt-basics.setoids where

open import Agda.Primitive
open import tt-basics.basics
open import tt-basics.id-type


-- Setoids

record setoid {ℓo ℓr : Level} : Set (lsuc (ℓo ⊔ ℓr))  where
 infix 2 _∼_
 field
   object : Set ℓo
   _∼_ : object → object → Set ℓr
   istteqrel : is-tt-eqrel _∼_
 open is-tt-eqrel istteqrel public

{-
setoid : {ℓ : Level} → Set (lsuc ℓ)
setoid {ℓ} = setoidₗₑᵥ ℓ ℓ
module setoid {ℓ : Level}(X : setoid {ℓ}) = setoidₗₑᵥ {ℓ} {ℓ} X
-}

infix 3 ||_||
infix 2 <_>_~_

||_|| : {ℓo ℓr : Level} → setoid {ℓo} {ℓr} → Set ℓo
|| X || = setoid.object X

<_>_~_ : {ℓo ℓr : Level} (X : setoid {ℓo} {ℓr}) → || X || → || X || → Set ℓr
< X > a ~ b = setoid._∼_ X a b


-- Free setoids (small)

==istteqrel : {ℓ : Level}(A : Set ℓ) → is-tt-eqrel (_==_ {A = A})
==istteqrel A = record
  { refl = λ _ → =rf
  ; sym = _⁻¹ 
  ; tra = _■_
  }


Freestd : {ℓ : Level} → Set ℓ → setoid {ℓ} {ℓ}
Freestd X = record
  { object = X
  ; _∼_ = _==_
  ; istteqrel = ==istteqrel X
  }

==→~ : {ℓo ℓr : Level}(A : setoid {ℓo} {ℓr}){a a' : || A ||}
           → a == a' → < A > a ~ a'
==→~ A {a} = =J (λ x _ → < A > a ~ x) (refl a)
            where open setoid A




-- Equational reasoning

module setoid-aux {ℓo ℓr : Level}(A : setoid {ℓo} {ℓr}) where
  open setoid A

  infix 2 _~_
  infixr 35 _⊙_
  infix 40 _ˢ

  ob : Set ℓo
  ob = object
  _~_ : ob → ob → Set ℓr
  _~_ = _∼_
    
  r : {a : ob} → a ∼ a
  r {a} = refl a

  _ˢ :  {a a' : ob} → a ~ a' → a' ~ a
  pf ˢ = sym pf
  
  _⊙_ : {a a' a'' : ob} → a ~ a' → a' ~ a'' → a ~ a''
  pf₁ ⊙ pf₂ = tra pf₁ pf₂

  infix 3 eqendp
  infixr 2 /_~[_]_
  infix 1 ~proof_~[_]_

  eqendp : (a₁ a₂ : ob) → a₁ ~ a₂ → a₁ ~ a₂
  eqendp a₁ a₂ p = p
  syntax eqendp a₁ a₂ p = a₁ ~[ p ] a₂

  ~proof_~[_]_ : (a₁ : ob) {a₂ a₃ : ob} →  a₁ ~ a₂ →  a₂ ~ a₃ →  a₁ ~ a₃
  ~proof a₁ ~[ pf ] pf' = tra pf pf'

  /_~[_]_ : (a₁ : ob) {a₂ a₃ : ob} →  a₁ ~ a₂ →  a₂ ~ a₃ →  a₁ ~ a₃
  / a₁ ~[ pf ] pf' = tra pf pf'

  eqreasend endpoints : (a a' : ob) → a ~ a' → a ~ a'
  eqreasend a a' pf = pf
  endpoints = eqreasend

  infix 3 eqreasend endpoints --_~[_]_∎
  syntax eqreasend a a' pf = / a ~[ pf ]∎ a' ∎
  syntax endpoints a a' pf = a ~[ pf ] a' ∎

-- end setoid-aux


-- Setoid functions

record setoidmap {ℓo ℓr ℓo' ℓr' : Level}(A : setoid {ℓo} {ℓr})(B : setoid {ℓo'} {ℓr'})
                 : Set (ℓo ⊔ ℓo' ⊔ ℓr ⊔ ℓr') where
  field
    op : || A || → || B ||
    ext : {x : || A ||} {y : || A ||}  →  (< A > x ~ y) → (< B > op x ~ (op y))

ap : {ℓo ℓr ℓo' ℓr' : Level}{A : setoid {ℓo} {ℓr}}{B : setoid {ℓo'} {ℓr'}}
         → setoidmap A B → || A || → || B ||
ap f a = setoidmap.op f a


ptw~ : {ℓo ℓr ℓo' ℓr' : Level}{A : setoid {ℓo} {ℓr}}{B : setoid {ℓo'} {ℓr'}}
           → setoidmap A B → setoidmap A B → Set (ℓo ⊔ ℓr')
ptw~ {A = A} {B} f g = (x : || A ||) →  < B > ((setoidmap.op f) x) ~ ((setoidmap.op g) x)

ptw~-is-tt-eqrel : {ℓo ℓr ℓo' ℓr' : Level}{A : setoid {ℓo} {ℓr}}{B : setoid {ℓo'} {ℓr'}}
                       → is-tt-eqrel (ptw~ {A = A} {B})
ptw~-is-tt-eqrel {A = A} {B} = record
  { refl = λ f x → B.refl (ap f x)
  ; sym = λ pf x → B.sym (pf x)
  ; tra = λ pf pf' x → B.tra (pf x) (pf' x)
  }
  where module B = setoid B


setoidmaps : {ℓo ℓr ℓo' ℓr' : Level} → setoid {ℓo} {ℓr} → setoid {ℓo'} {ℓr'}
                 → setoid {ℓo ⊔ ℓo' ⊔ ℓr ⊔ ℓr'} {ℓo ⊔ ℓr'}
setoidmaps A B = record
  { object = setoidmap A B
  ; _∼_  =  ptw~ {A = A} {B}
  ; istteqrel = ptw~-is-tt-eqrel {A = A} {B}
  }


_⇒_ : {ℓo ℓr ℓo' ℓr' : Level} → setoid {ℓo} {ℓr} → setoid {ℓo'} {ℓr'}
                 → setoid {ℓo ⊔ ℓo' ⊔ ℓr ⊔ ℓr'} {ℓo ⊔ ℓr'}
A ⇒ B = setoidmaps A B



free-stdmap : {ℓ ℓ' : Level}{X : Set ℓ}{Y : Set ℓ'}
                 → (X → Y) → setoidmap (Freestd X) (Freestd Y)
free-stdmap f = record
  { op = f
  ; ext = =ap f
  }

free-std-is-min : {ℓ ℓo ℓr : Level}{X : Set ℓ}{A : setoid {ℓo} {ℓr}}(f : X → || A ||)
                     → setoidmap (Freestd X) A
free-std-is-min {X = X} {A} f = record
  { op = f
  ; ext = λ pf → ==→~ A (=ap f pf)
  }

can-cover : {ℓo ℓr : Level}(A : setoid {ℓo} {ℓr}) → setoidmap (Freestd || A ||) A
can-cover A = free-std-is-min (λ x → x)


std-id : {ℓo ℓr : Level}{A : setoid {ℓo} {ℓr}} → || A ⇒ A ||
std-id {A} = record { op = λ x → x
                    ; ext = λ pf → pf
                    }


std-cmp : {ℓo ℓr ℓo' ℓr' ℓo'' ℓr'' : Level}{A : setoid {ℓo} {ℓr}}{B : setoid {ℓo'} {ℓr'}}{C : setoid {ℓo''} {ℓr''}}
          → || B ⇒ C || → || A ⇒ B || → || A ⇒ C ||
std-cmp g f = record { op = λ x → op g (op f x)
                     ; ext = λ pf → ext g (ext f pf)
                     }
                     where open setoidmap


std-cmp-ext : {ℓo ℓr ℓo' ℓr' ℓo'' ℓr'' : Level}{A : setoid {ℓo} {ℓr}}{B : setoid {ℓo'} {ℓr'}}
              {C : setoid {ℓo''} {ℓr''}}(g g' : || B ⇒ C ||)(f f' : || A ⇒ B ||)
                 → < B ⇒ C >  g ~ g' → < A ⇒ B > f ~ f'
                   → < A ⇒ C > std-cmp g f ~ std-cmp g' f'
std-cmp-ext {C = C} g g' f f' pfg pff x = pfg (op f x) ⊙ ext g' (pff x)
                                        where open setoidmap
                                              open setoid-aux C



-- Extensional properties

record is-ext-small-prop {X : setoid} (P : || X || → Set) : Set where
  field
    trnsp : {x x' : || X ||} → < X > x ~ x' → P x → P x'

record is-ext-prop {ℓo ℓr ℓ : Level} {X : setoid {ℓo} {ℓr}} (P : || X || → Set ℓ)
                   : Set (ℓo ⊔ ℓr  ⊔ ℓ) where
  field
    trnsp : {x x' : || X ||} → < X > x ~ x' → P x → P x'
                 



