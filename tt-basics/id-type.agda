
-- disable the K axiom:

{-# OPTIONS --without-K #-}

-- Agda version 2.5.4.1

module tt-basics.id-type where

open import tt-basics.basics
open import Agda.Primitive


-- Identity type

infix 8 _==_
data _==_ {ℓ : Level}{A : Set ℓ} (a : A) : A → Set where
  =rf : a == a


-- Paulin-Mohring eliminator

=J : {A : Set}{a₀ : A}(B : (a : A) → a₀ == a → Set)
        → B a₀ =rf → {a : A} → (p : a₀ == a) → B a p
=J B b₀ =rf = b₀

{-
check : {A : Set}{a : A}(p : a == a) → (p == refl)
check =rf = {!!}
-}


-- Some useful properties

=ap : {A B : Set}(f : A → B){a a' : A} → a == a' → f a == f a'
=ap f p = =J (λ x _ → f _ == f x) =rf p

=transp : {A : Set}(B : A → Set){a a' : A} → a == a' → B a → B a'
=transp B p b = =J (λ x _ → B _ → B x) (λ y → y) p b

infix 40 _•_

_•_ : {A : Set}(B : A → Set) {a a' : A} → a == a' → B a → B a'
B • p = =transp B p

=transpcnst : {A : Set}(B : Set){a a' : A}(p : a == a')(b : B) → ((λ _ → B) • p) b == b
=transpcnst B p b = =J (λ x q → ( ((λ _ → B) • q) b == b )) =rf p

=apd : {A : Set}{B : A → Set}(f : (a : A) → B a){a a' : A}(p : a == a') → (B • p) (f a) == f a'
=apd f p = =J (λ x p → (_ • p) (f _) == f x) =rf p

=sym : {A : Set}{a a' : A} → a == a' → a' == a
=sym p = ((λ x → x == _) • p) =rf

=tra : {A : Set}{a₁ a₂ a₃ : A} → a₁ == a₂ → a₂ == a₃ → a₁ == a₃
=tra p q = ((λ x → _ == x) • q) p


-- Equational reasoning

--infix 3 /_==[_]∎_∎
--infix  3 _∎
infixr 2 /_==[_]_
infixr 1 =proof_==[_]_

=proof_==[_]_ : {A : Set}(a₁ {a₂ a₃} : A) → a₁ == a₂ → a₂ == a₃ → a₁ == a₃
=proof a ==[ pf ] pf' = =tra pf pf'

--_∎ : {A : Set}(a : A) → a == a
--a ∎ = =rf

/_==[_]_ : {A : Set}(a₁ {a₂ a₃} : A) → a₁ == a₂ → a₂ == a₃ → a₁ == a₃
/ a₁ ==[ pf ] pf' = =tra pf pf'

=eqreasend : {A : Set}(a₁ a₂ : A) → a₁ == a₂ → a₁ == a₂
=eqreasend _ _ pf = pf 

syntax =eqreasend a b pf = / a ==[ pf ]∎ b ∎

-- Notation for inverses and concatenation

infix 60 _⁻¹

_⁻¹ : {A : Set}{a a' : A} → a == a' → a' == a
p ⁻¹ = =sym p

infixr 50 _■_

_■_ : {A : Set}{a₁ a₂ a₃ : A} → a₁ == a₂ → a₂ == a₃ → a₁ == a₃
p ■ q = =tra p q


-- Groupoid laws

■tr : {A : Set}(B : A → Set){a₁ a₂ a₃ : A}(p₁ : a₁ == a₂)(p₂ : a₂ == a₃)(b : B a₁)
         → (B • (p₁ ■ p₂)) b == (B • p₂) ((B • p₁) b)
■tr B p₁ p₂ b = =J (λ x u → (B • p₁ ■ u) b == (B • u) ((B • p₁) b)) =rf p₂

■idr : {A : Set}{a a' : A}(p : a == a') → p ■ =rf == p
■idr p = =rf

■idl : {A : Set}{a a' : A}(p : a == a') → =rf ■ p == p
■idl p = =J (λ _ u → =rf ■ u == u) =rf p

■invr : {A : Set}{a a' : A}(p : a == a') → p ■ p ⁻¹ == =rf
■invr = =J (λ _ u → u ■ u ⁻¹ == =rf) =rf

■invl : {A : Set}{a a' : A}(p : a == a') → p ⁻¹ ■ p == =rf
■invl = =J (λ _ u → u ⁻¹ ■ u == =rf) =rf

■ass : {A : Set}{a₁ a₂ a₃ a₄ : A}(p₁ : a₁ == a₂)(p₂ : a₂ == a₃)(p₃ : a₃ == a₄)
           → p₁ ■ (p₂ ■ p₃) == (p₁ ■ p₂) ■ p₃
■ass p₁ p₂ p₃ = ■tr _ p₂ p₃ p₁

■ass⁻¹ : {A : Set}{a₁ a₂ a₃ a₄ : A}(p₁ : a₁ == a₂)(p₂ : a₂ == a₃)(p₃ : a₃ == a₄)
--(p₁ : a₁ == a₂)(p₂ : a₂ == a₃)(p₃ : a₃ == a₄)
           → (p₁ ■ p₂) ■ p₃ == p₁ ■ (p₂ ■ p₃)
■ass⁻¹ p₁ p₂ p₃ = ■ass p₁ p₂ p₃ ⁻¹


-- Some equations between proof of equations

■extl : {A : Set}{a₁ a₂ : A}(p : a₁ == a₂){a₃ : A}{p₁ : a₂ == a₃}{p₂ : a₂ == a₃}
           → p₁ == p₂ → p ■ p₁ == p ■ p₂
■extl p = =ap (λ u → p ■ u)

■extr : {A : Set}{a₂ a₃ : A}(p : a₂ == a₃){a₁ : A}{p₁ : a₁ == a₂}{p₂ : a₁ == a₂}
           → p₁ == p₂ → p₁ ■ p == p₂ ■ p
■extr p = =ap (λ u → u ■ p)


■idlg : {A : Set}{a₁ a₂ a₃ : A}{p₁ : a₁ == a₁}{p₂ : a₁ == a₂}{p₃ : a₁ == a₂}
         → p₁ == =rf → p₁ ■ p₂ == p₃ → p₂ == p₃
■idlg {p₁ = p₁} {p₂} {p₃} hrf h = =proof p₂         ==[ ■idl p₂ ⁻¹ ] /
                                       =rf ■ p₂   ==[ ■extr p₂ (hrf ⁻¹) ] /
                                       p₁ ■ p₂    ==[ h ]∎
                                       p₃ ∎

■idrg : {A : Set}{a₁ a₂ a₃ : A}{p₁ : a₁ == a₂}{p₂ : a₂ == a₂}{p₃ : a₁ == a₂}
         → p₂ == =rf → p₁ ■ p₂ == p₃ → p₁ == p₃
■idrg {p₁ = p₁} {p₂} {p₃} hrf h = =proof p₁         ==[ ■idr p₁ ⁻¹ ] /
                                         p₁ ■ =rf   ==[ ■extl p₁ (hrf ⁻¹) ] /
                                         p₁ ■ p₂    ==[ h ]∎
                                         p₃ ∎


■lc : {A : Set}{a₁ a₂ : A}{p : a₁ == a₂}{a₃ : A}{p₁ : a₂ == a₃}{p₂ : a₂ == a₃}
          → p ■ p₁ == p ■ p₂ → p₁ == p₂
■lc {p = p} {_} {p₁} {p₂} h = =proof p₁           ==[ (■idl p₁ ⁻¹ ■ ■extr p₁ (■invl p ⁻¹)) ■ ■ass⁻¹ _ _ p₁ ] /
                                 p ⁻¹ ■ p ■ p₁    ==[ ■extl (p ⁻¹) h ] /
                                 p ⁻¹ ■ p ■ p₂    ==[ ■ass _ _ p₂ ■ ■extr p₂ (■invl p) ■ ■idl p₂ ]∎
                                 p₂ ∎

■rc : {A : Set}{a₁ a₂ a₃ : A}{p : a₂ == a₃}{a₁ : A}{p₁ : a₁ == a₂}{p₂ : a₁ == a₂}
          → p₁ ■ p == p₂ ■ p → p₁ == p₂
■rc {p = p} {_} {p₁} {p₂} h = =proof p₁           ==[ ■idr p₁ ⁻¹ ■ ■extl p₁ (■invr p ⁻¹) ] /
                                 p₁ ■ p ■ p ⁻¹    ==[ ■ass _ _ (p ⁻¹)  ■ ■extr (p ⁻¹) h ■ ■ass⁻¹ _ _ (p ⁻¹)  ] /
                                 p₂ ■ p ■ p ⁻¹    ==[ ■extl p₂ (■invr p) ■ ■idr p₂ ]∎
                                 p₂ ∎



-- Equal functions are homotopic

=2htpy : {A : Set}{B : A → Set}{f g : (a : A) → B a} → f == g → (a : A) → f a == g a
=2htpy {f = f} p a = ((λ x → f a == x a) • p) =rf



--part of Lemma 2.9.6 in HoTT book

HoTTLemma2-9-6 : {A : Set}{B C : A → Set}{a a' : A}(p : a == a')
                 {f : B a → C a}{g : B a' → C a'}
                   → ((λ x → B x → C x) • p) f == g → (y : B a) → (C • p) (f y) == g ((B • p) y)
HoTTLemma2-9-6 {A} {B} {C} {a} {a'} p = =J JEl JElrf p
  where JEl : (x : A) → a == x → Set
        JEl x u = {f : B a → C a}{g : B x → C x} →
                     ((λ x → B x → C x) • u) f == g → (y : B a) → (C • u) (f y) == g ((B • u) y)
        JElrf : JEl a =rf
        JElrf = =2htpy


{-
-- transport of fibrewise functions is pointwise
•ptw : {A : Set}{B C : A → Set}(f : (a : A) → B a → C a)
       {a a' : A}(p : a == a')(b : B a')
          → ((λ x → B x → C x) • p) (f a) b == (C • p) (f a ((B • p ⁻¹) b))
•ptw f p b = let ψ : _
                 ψ = {!!}
             in {!!}
-}


-- Contractibility & Co.

isContr : (A : Set) → Set
isContr A = Σ A (λ a₀ → (a : A) → a == a₀ )

contr₀ : {A : Set} → isContr A → A
contr₀ = pj1

contr= : {A : Set}(cnt : isContr A)(a : A) → a == contr₀ cnt
contr= = pj2

N₁-isContr : isContr N₁
N₁-isContr = 0₁ , N₁rec =rf

isProp : (A : Set) → Set
isProp A = (a a' : A) → a == a'

isContr→isProp : {A : Set} → isContr A → isProp A
isContr→isProp cnt = λ a a' → (contr= cnt a) ■ (contr= cnt a' ⁻¹)

isContr→=isContr : {A : Set} → isContr A → {a a' : A} → isContr (a == a')
isContr→=isContr cnt = isContr→isProp cnt _ _ , =J (λ x u → u == isContr→isProp cnt _ _) (■invr (contr= cnt _) ⁻¹)


-- Identities of products

prdη : {A B : Set}(z : prod A B) → pair (prj1 z) (prj2 z) == z
prdη (pair a b) = =rf

prdη⁻¹ : {A B : Set}(z : prod A B) → z == pair (prj1 z) (prj2 z)
prdη⁻¹ (pair a b) = =rf

=prdchar : {A B : Set}{z z' : prod A B}
             → prj1 z == prj1 z' → prj2 z == prj2 z'
               → z == z'
=prdchar pf₁ pf₂ = auxAB pf₁ _ pf₂ ■ prdη _ where

                   auxB : {A B : Set}{z : prod A B}(b : B)
                             → prj2 z == b → z == pair (prj1 z) b
                   auxB {z = z} b pf = =J (λ b' pf' → z == pair (prj1 z) b') (prdη⁻¹ _) pf
                   
                   auxAB : {A B : Set}{z : prod A B}{a : A} → prj1 z == a
                               → (b : B) → prj2 z == b → z == pair a b
                   auxAB {z = z} pf₁ = =J (λ a' pf' → (b' : _) → prj2 z == b' → z == pair a' b')
                                          (auxB) pf₁


-- UIP stuff

UIP UIPrf  : (A : Set) → Set
UIP A = {a a' : A} → isProp (a == a')
UIPrf A = {a : A} (p : a == a) → p == =rf

UIP→UIPrf : {A : Set} → UIP A → UIPrf A
UIP→UIPrf {A} uip p = uip p =rf

UIPrf→UIP : {A : Set} → UIPrf A → UIP A
UIPrf→UIP {A} uiprf {a} = λ p q → =J (λ x u → (v : a == x) → v == u) uiprf q p


HoTT-Thm7-2-2-aux : {A : Set} {R : A → A → Set} (Rrf : ∀ a → R a a)
                (Risprop : ∀ a a' → isProp (R a a')) (R→== : ∀ a a' → R a a' → a == a')
                 → UIPrf A
HoTT-Thm7-2-2-aux {A} {R} Rrf Risprop R→== {a} p = ■lc {p = R→== a a (Rrf a)} (q' (Rrf a) ■ ■idr _ ⁻¹)
  where D : A → Set
        D x = R a x → a == x
        q : (D • p) (R→== a a) == R→== a a
        q = =apd {B = D} (R→== a) p
        q' : (e : R a a) → ((_==_ a) • p) (R→== a a e) == R→== a a e --(((R a) • p) e)
        q' e = HoTTLemma2-9-6 p q e ■ =ap (R→== a a) (Risprop a a _ _)


HoTT-Thm7-2-2 : {A : Set} {R : A → A → Set} (Rrf : ∀ a → R a a)
                (Risprop : ∀ a a' → isProp (R a a')) (R→== : ∀ a a' → R a a' → a == a')
                 → UIP A
HoTT-Thm7-2-2 Rrf Risprop R→== = UIPrf→UIP (HoTT-Thm7-2-2-aux Rrf Risprop R→==)
