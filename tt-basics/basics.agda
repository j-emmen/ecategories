
{-# OPTIONS --without-K #-}

module tt-basics.basics where

open import Agda.Primitive


-- empty and singleton types

data N₀ : Set where

N₀rec : {ℓ : Level}{C : N₀ → Set ℓ} (c : N₀) → C c
N₀rec ()


data  N₁ : Set where
  0₁ : N₁

N₁rec : {ℓ : Level}{C : N₁ → Set ℓ} → C 0₁ → (c : N₁) → C c
N₁rec d 0₁ = d


-- natural numbers

data N : Set where
   O : N
   s : N -> N

Nrec : {ℓ : Level} {C : N -> Set ℓ} -> C O -> ((n : N) -> C n -> C (s n)) -> (c : N) -> C c
Nrec d e O = d
Nrec d e (s n) = e n (Nrec d e n)


-- disjoint sums

data sum {i j} (A : Set i)(B : Set j) : Set (i ⊔ j) where
    inl : A → sum A B
    inr : B → sum A B

sumEl : {i j k : Level}{A : Set i}{B : Set j}{C : sum A B → Set k}
           → ((a : A) → C (inl a)) → ((b : B) → C (inr b)) → (c : sum A B) → C c
sumEl d e (inl a) = d a
sumEl d e (inr b) = e b

infix 50 _+_ _+ₕ_
_+_ : {i j : Level} (A : Set i)(B : Set j) → Set (i ⊔ j)
A + B = sum A B

_+ₕ_ : {i j i' j' : Level}{A : Set i}{A' : Set i'}{B : Set j}{B' : Set j'}
          → (A → B) → (A' → B')
            → A + A' → B + B'
(f +ₕ g) (inl a) = inl (f a)
(f +ₕ g) (inr a') = inr (g a')
--f +ₕ g = sumEl (λ a → inl (f a)) λ a' → inr (g a')


-- inductive finite types

data Finᵢ : N → Set where
  f0 : {n : N} → Finᵢ (s n)
  finj : {n : N} → Finᵢ n → Finᵢ (s n)

Finᵢ0rec : {ℓ : Level} {C : Finᵢ O → Set ℓ} (i : Finᵢ O) → C i
Finᵢ0rec ()
Finᵢsrec : {ℓ : Level}{n : N}{C : Finᵢ (s n) → Set ℓ}
              → (C f0) → ((i : Finᵢ n) → C (finj i))
                → (i : Finᵢ (s n)) → C i
Finᵢsrec c0 cinj f0 = c0
Finᵢsrec c0 cinj (finj i) = cinj i


-- defined finite types

Fin : N → Set
Fin = Nrec N₀ (λ m F → F + N₁)

Fin0rec : {ℓ : Level}{C : Fin O → Set ℓ} (i : Fin O) → C i
Fin0rec = N₀rec
Finsrec : {ℓ : Level}(n : N){C : Fin (s n) → Set ℓ}
             → ((i : Fin n) → C (inl i)) → (C (inr 0₁))
               → (i : Fin (s n)) → C i
Finsrec n {C} d e = sumEl {C = C} d (N₁rec e)

FinsInd : {ℓ : Level}(n : N){C : Fin (s (s n)) → Set ℓ}
             → (ind : (c : C (inr 0₁))(f : (i : Fin (s n)) → C (inl i))
                         → (i : Fin (s (s n))) → C i)
               → (c : C (inr 0₁)) (f : (i : Fin (s n)) → C (inl i))
                 → (i : Fin (s (s n))) → C i
FinsInd n {C} ind c f = ind c f
--sumEl {C = C} {!!} (N₁rec c)

Fin-emb : (n : N) → Fin n → Fin (s n)
Fin-emb n = inl

Fin-min : (n : N) → Fin (s n)
Fin-min O = inr 0₁
Fin-min (s n) = inl (Fin-min n)

Fin-max : (n : N) → Fin (s n)
Fin-max n = inr 0₁

Fin-suc : (n : N) → Fin n → Fin (s n)
Fin-suc (s n) (inl x) = inl (Fin-suc n x)
Fin-suc (s n) (inr x) = Fin-max (s n)

shiftr : (n : N) → Fin (s n) → Fin (s n)
shiftr n (inl x) = Fin-suc n x
shiftr n (inr x) = Fin-min n

{-
shiftl : (n : N) → Fin (s (s n)) → Fin (s (s n))
shiftl n (inl x) = {!!}
-- looks like the only way is by induction on n
shiftl n (inr x) = Fin-emb (s n) (Fin-max n)


Fin' : N → Set
Fin' n = N₁ + (Nrec N₀ (λ m F → F + N₁) n)

Fin'-emb : (n : N) → Fin' n → Fin' (s n)
Fin'-emb n = (λ x → x) +ₕ inl

Fin'-min : (n : N) → Fin' n
Fin'-min n = inl 0₁

Fin'-max : (n : N) → Fin' (s n)
Fin'-max n = inr (inr 0₁)

Fin'-suc : (n : N) → Fin' n → Fin' (s n)
Fin'-suc n x = {!!}

shift'r : (n : N) → Fin' n → Fin' n
shift'r n = {!!}
-}


-- Extending a section from 'Fin n' to 'Fin (s n)' on the right.
Fin-insr : {ℓ : Level}(n : N){C : Fin (s n) → Set ℓ}
              → ((i : Fin n) → C (Fin-emb n i)) → C (Fin-max n)
                → (i : Fin (s n)) → C i
Fin-insr n {C} f cₘ (inl x) = f x
Fin-insr n {C} f cₘ (inr 0₁) = cₘ

-- Extending a section from 'Fin n' to 'Fin (s n)' on the left.
Fin-insl : {ℓ : Level}(n : N){C : Fin (s n) → Set ℓ}
              → ((i : Fin n) → C (Fin-suc n i)) → C (Fin-min n)
                → (i : Fin (s n)) → C i
Fin-insl O {C} f c₀ (inr 0₁) = c₀
Fin-insl (s n) {C} f c₀ (inl x) = Fin-insl n {λ i → C (inl i)}
                                           (λ i → f (Fin-emb n i)) c₀ x
Fin-insl (s n) {C} f c₀ (inr 0₁) = f (Fin-max n)
-- 'Fin-insl f c Fin-min' reduces to 'c₀' only when 'n' is a numeral.


-- disjoint sum of a family of types

infix 3 _,_

data Σ {i j} (A : Set i) (B : A → Set j) : Set (i ⊔ j) where
   _,_ : (a : A) → B a → Σ A B

pj1 : ∀ {i j} {A : Set i} → {B : A → Set j} → Σ A B → A
pj1 (a , b) = a

pj2 : ∀ {i j} {A : Set i} → {B : A → Set j}  → (u : Σ A B) → (B (pj1 u))
pj2 (a , b) = b


-- binary product

data prod {i j} (A : Set i) (B : Set j) : Set (i ⊔ j) where
   pair : A → B → prod A B

prj1 : ∀ {i j} {A : Set i} → {B : Set j}  → prod A B → A
prj1 (pair a b) = a

prj2 : ∀ {i j} {A : Set i} → {B : Set j}  → prod A B → B
prj2 (pair a b) = b


-- Logic using propositions as types

False : Set
False = N₀

exfalso : (A : Set) → False → A
exfalso A u = N₀rec {C = λ z → A} u

True : Set
True = N₁

tt : True
tt = 0₁

implies : (A : Set) → (B : Set)  → Set
implies A B = A → B

impI : {A : Set} → {B : Set} → (A → B) → implies A B
impI f =  f

impE : {A : Set} → {B : Set} → (implies A B) → A → B
impE f a = f a

fun : (A : Set) → (B : Set)  → Set
fun A B = A → B

all : (A : Set) → (B : A → Set) → Set
all A B = (x : A) → B x

allI : {A : Set} → {B : A → Set} → ((a : A) → B a) → all A B
allI f =  f

and : (A : Set) → (B : Set) → Set
and A B = prod A B

andI :  {A : Set} → {B : Set} → (a : A) → (b : B) → and A B
andI a b = pair a  b

andL :  {A : Set} → {B : Set} → (and A B) → A
andL c = prj1 c

andR :  {A : Set} → {B : Set} → (and A B) → B
andR c = prj2 c

exists : (A : Set) → (B : A → Set) → Set
exists A B =  Σ A B

existsI : {A : Set} → {B : A → Set} → 
          (a : A) → (b : B a) → exists A B
existsI a b = ( a , b )

or  : (A : Set) → (B : Set) → Set
or A B = sum A B

orL  : {A : Set} → {B : Set} → A → or A B
orL a = inl a

orR  : {A : Set} → {B : Set} → B → or A B
orR b = inr b

orE : {A B : Set} → {C : (or A B) → Set}
   → ((a : A) → C (orL a)) → ((b : B) → C (orR b)) → (c : or A B) → C c
orE = sumEl


iff :  (A : Set) → (B : Set) → Set
iff A B = and (implies A B) (implies B A)

triviff : (A : Set) → iff A A
triviff A = andI (impI (λ x → x)) (impI (λ x → x))

not : (A : Set) → Set
not A = implies A False



-- type-theoretic equivalence relations

record is-tt-eqrel {ℓo ℓr : Level} {A : Set ℓo} (R : A → A → Set ℓr) : Set (ℓo ⊔ ℓr) where
  field
    refl : (x : A) → R x x
    sym : {x₁ x₂ : A} → R x₁ x₂ → R x₂ x₁
    tra : {x₁ x₂ x₃ : A} → R x₁ x₂ → R x₂ x₃ → R x₁ x₃

tt-eqrel-stable :  {ℓ ℓo ℓr : Level}{A' : Set ℓ}{A : Set ℓo}(f : A' → A)
                   {R : A → A → Set ℓr}(tteqrel : is-tt-eqrel R)
                     → is-tt-eqrel (λ x₁ x₂ → R (f x₁) (f x₂))
tt-eqrel-stable {A' = A'} {A} f {R} tteqrel = record
  { refl = λ x → R.refl (f x)
  ; sym = λ {x₁} {x₂} → R.sym {f x₁} {f x₂}
  ; tra = λ {x₁} {x₂} {x₃} → R.tra {f x₁} {f x₂} {f x₃}
  }
  where module R = is-tt-eqrel tteqrel
