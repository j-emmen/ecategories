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
  infixr 35 ~tra _⊙_
  infix 40 ~sym _ˢ

  ob : Set ℓo
  ob = object
  _~_ : ob → ob → Set ℓr
  _~_ = _∼_
    
  r : {a : ob} → a ∼ a
  r {a} = refl a

  ~sym _ˢ :  {a a' : ob} → a ~ a' → a' ~ a
  ~sym = sym
  pf ˢ = sym pf
  
  ~tra _⊙_ : {a a' a'' : ob} → a ~ a' → a' ~ a'' → a ~ a''
  ~tra = tra
  pf₁ ⊙ pf₂ = tra pf₁ pf₂

  infix 3 eqendp
  infixr 2 /_~[_]_
  infix 1 ~proof_~[_]_

  eqendp : (a₁ a₂ : ob) → a₁ ~ a₂ → a₁ ~ a₂
  eqendp a₁ a₂ p = p
  syntax eqendp a₁ a₂ p = a₁ ~[ p ] a₂

  eqreasstart ~proof_~[_]_ : (a₁ : ob) {a₂ a₃ : ob} →  a₁ ~ a₂ →  a₂ ~ a₃ →  a₁ ~ a₃
  eqreasstart a₁ = tra
  ~proof a₁ ~[ pf ] pf' = tra pf pf'

  eqreasmid /_~[_]_ : (a₁ : ob) {a₂ a₃ : ob} →  a₁ ~ a₂ →  a₂ ~ a₃ →  a₁ ~ a₃
  eqreasmid a₁ = tra
  / a₁ ~[ pf ] pf' = tra pf pf'

  eqreasend endpoints : (a a' : ob) → a ~ a' → a ~ a'
  eqreasend a a' pf = pf
  endpoints = eqreasend

  infix 3 eqreasend endpoints --_~[_]_∎
  syntax eqreasend a a' pf = / a ~[ pf ]∎ a' ∎
  syntax endpoints a a' pf = a ~[ pf ] a' ∎

  -- versions of the above keeping track of intermediate points
  r[_] : (a : ob) → a ~ a
  r[ a ] = refl a  
  syntax ~sym {a = a} {a'} pf = pf ˢ[ a , a' ]
  syntax ~tra {a = a} {a'} {a''} pf₁ pf₂ = pf₁ ⊙ pf₂ [ a , a' , a'' ]
  syntax eqreasstart a₁ {a₂} {a₃} pf pf' = ~proof a₁ ~[ pf to a₂ , a₃ ] pf'
  syntax eqreasmid a₁ {a₂} {a₃} pf pf' = / a₁ ~[ pf to a₂ , a₃ ] pf'
  infix 45 r[_]

-- end setoid-aux


codisc-std : {ℓ : Level} → Set ℓ → setoid {ℓ} {lzero}
codisc-std A = record
  { object = A
  ; _∼_ = λ _ _ → N₁
  ; istteqrel = record
              { refl = λ _ → 0₁
              ; sym = λ _ → 0₁
              ; tra = λ _ _ → 0₁
              }
  }

{-
-- already defined above as Freestd
disc-std : {ℓ : Level} → Set ℓ → setoid {ℓ} {ℓ}
disc-std A = record
  { object = A
  ; _∼_ = λ x y → x == y
  ; istteqrel = record
              { refl = λ _ → =rf
              ; sym = =sym
              ; tra = =tra
              }
  }
-}

sub-setoid : {ℓ ℓo ℓr : Level}{X : Set ℓ}(A : setoid {ℓo} {ℓr})(f : X → || A ||)
                → setoid {ℓ} {ℓr}
sub-setoid {X = X} A f = record
  { object = X
  ; _∼_ = λ x x' → (f x) A.∼ (f x')
  ; istteqrel = tt-eqrel-stable f A.istteqrel
  }
  where module A = setoid A

prod-std : {ℓo₁ ℓr₁ : Level}(A : setoid {ℓo₁} {ℓr₁}){ℓo₂ ℓr₂ : Level}(B : setoid {ℓo₂} {ℓr₂})
                → setoid {ℓo₁ ⊔ ℓo₂} {ℓr₁ ⊔ ℓr₂}
prod-std A B = record
  { object = prod || A || || B ||
  ; _∼_ = λ z₁ z₂ → prod ((prj1 z₁) A.∼ prj1 z₂) ((prj2 z₁) B.∼ (prj2 z₂))
  ; istteqrel = record
              { refl = λ z → pair (A.refl (prj1 z)) (B.refl (prj2 z))
              ; sym = λ pf → pair (A.sym (prj1 pf)) (B.sym (prj2 pf))
              ; tra = λ pf₁ pf₂ → pair (A.tra (prj1 pf₁) (prj1 pf₂)) (B.tra (prj2 pf₁) (prj2 pf₂))
              }
  }
  where module A = setoid A
        module B = setoid B

module prod-std {ℓo₁ ℓr₁ : Level}(A : setoid {ℓo₁} {ℓr₁}){ℓo₂ ℓr₂ : Level}(B : setoid {ℓo₂} {ℓr₂})
                (z : || prod-std A B ||)
                where
  ₁ : || A ||
  ₁ = prj1 z
  ₂ : || B ||
  ₂ = prj2 z

module prod-stdeq {ℓo₁ ℓr₁ : Level}(A : setoid {ℓo₁} {ℓr₁}){ℓo₂ ℓr₂ : Level}(B : setoid {ℓo₂} {ℓr₂})
                  {z z' : || prod-std A B ||}(eq : < prod-std A B > z ~ z')
                  where
  private
    module A = setoid-aux A
    module B = setoid-aux B
    module z = prod-std A B z
    module z' = prod-std A B z'
  ₁ : z.₁ A.~ z'.₁
  ₁ = prj1 eq
  ₂ : z.₂ B.~ z'.₂
  ₂ = prj2 eq


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



ptw~S : {ℓ ℓo ℓr : Level}{A : Set ℓ}{B : A → setoid {ℓo} {ℓr}}
       (f g : ∀ a → || B a ||) → Set (ℓ ⊔ ℓr)
ptw~S {A = A} {B} f g = (x : A) →  < B x > f x ~ g x

ptw~S-is-tt-eqrel : {ℓ ℓo ℓr : Level}{A : Set ℓ}{B : A → setoid {ℓo} {ℓr}}
                       → is-tt-eqrel (ptw~S {A = A} {B})
ptw~S-is-tt-eqrel {A = A} {B} = record
  { refl = λ f x → B.refl x (f x)
  ; sym = λ pf x → B.sym x (pf x)
  ; tra = λ pf pf' x → B.tra x (pf x) (pf' x)
  }
  where module B (a : A) = setoid (B a)


std-id : {ℓo ℓr : Level}{A : setoid {ℓo} {ℓr}} → || A ⇒ A ||
std-id {A} = record { op = λ x → x
                    ; ext = λ pf → pf
                    }

std-cmp : {ℓo ℓr ℓo' ℓr' ℓo'' ℓr'' : Level}{A : setoid {ℓo} {ℓr}}
          {B : setoid {ℓo'} {ℓr'}}{C : setoid {ℓo''} {ℓr''}}
          → || B ⇒ C || → || A ⇒ B || → || A ⇒ C ||
std-cmp g f = record { op = λ x → op g (op f x)
                     ; ext = λ pf → ext g (ext f pf)
                     }
                     where open setoidmap

infixr 10 _⊛_
_⊛_ : {ℓo ℓr ℓo' ℓr' ℓo'' ℓr'' : Level}{A : setoid {ℓo} {ℓr}}
       {B : setoid {ℓo'} {ℓr'}}{C : setoid {ℓo''} {ℓr''}}
          → || B ⇒ C || → || A ⇒ B || → || A ⇒ C ||
g ⊛ f = std-cmp g f

std-cmp-ext : {ℓo ℓr ℓo' ℓr' ℓo'' ℓr'' : Level}{A : setoid {ℓo} {ℓr}}{B : setoid {ℓo'} {ℓr'}}
              {C : setoid {ℓo''} {ℓr''}}(g g' : || B ⇒ C ||)(f f' : || A ⇒ B ||)
                 → < B ⇒ C >  g ~ g' → < A ⇒ B > f ~ f'
                   → < A ⇒ C > std-cmp g f ~ std-cmp g' f'
std-cmp-ext {C = C} g g' f f' pfg pff x = pfg (op f x) ⊙ ext g' (pff x)
                                        where open setoidmap
                                              open setoid-aux C


record is-bij-pair {ℓo ℓr : Level}(A : setoid {ℓo} {ℓr}){ℓo' ℓr' : Level}(B : setoid {ℓo'} {ℓr'})
                   (f : || A ⇒ B ||)(g : || B ⇒ A ||)
                   : Set (ℓo ⊔ ℓo' ⊔ ℓr ⊔ ℓr')
                   where
  private
    module f = setoidmap f
    module g = setoidmap g
  field
    iddom : < A ⇒ A > std-cmp g f ~ std-id {A = A}
    idcod : < B ⇒ B > std-cmp f g ~ std-id {A = B}


stdsections : {ℓ ℓo ℓr : Level}{A : Set ℓ}(B : A → setoid {ℓo} {ℓr})
                 → setoid {ℓ ⊔ ℓo} {ℓ ⊔ ℓr}
stdsections {A = A} B = record
  { object = (a : A) → || B a ||
  ; _∼_  =  ptw~S {A = A} {B}
  ; istteqrel = ptw~S-is-tt-eqrel {A = A} {B}
  }


free-stdmap : {ℓ ℓ' : Level}{X : Set ℓ}{Y : Set ℓ'}
                 → (X → Y) → setoidmap (Freestd X) (Freestd Y)
free-stdmap f = record
  { op = f
  ; ext = =ap f
  }

free-std-is-min-pf : {ℓ ℓo ℓr : Level}{X : Set ℓ}(A : setoid {ℓo} {ℓr})(f : X → || A ||){x x' : X}
                        → < Freestd X > x ~ x' → < A > f x ~ f x'
free-std-is-min-pf A f pf = ==→~ A (=ap f pf)

free-std-is-min : {ℓ ℓo ℓr : Level}{X : Set ℓ}{A : setoid {ℓo} {ℓr}}(f : X → || A ||)
                     → setoidmap (Freestd X) A
free-std-is-min {X = X} {A} f = record
  { op = f
  ; ext = free-std-is-min-pf A f
  }

can-cover : {ℓo ℓr : Level}(A : setoid {ℓo} {ℓr}) → setoidmap (Freestd || A ||) A
can-cover A = free-std-is-min (λ x → x)



-- Extensional properties

record is-ext-small-prop {X : setoid} (P : || X || → Set) : Set where
  field
    trnsp : {x x' : || X ||} → < X > x ~ x' → P x → P x'

record is-ext-prop {ℓo ℓr ℓ : Level} {X : setoid {ℓo} {ℓr}} (P : || X || → Set ℓ)
                   : Set (ℓo ⊔ ℓr  ⊔ ℓ) where
  field
    trnsp : {x x' : || X ||} → < X > x ~ x' → P x → P x'
                 
-- Finite setoids

Finstd : N → setoid {lzero} {lzero}
Finstd n = Freestd (Fin n)

