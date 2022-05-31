
{-# OPTIONS --without-K #-}

module tt-basics.id-type where

open import Agda.Primitive
open import tt-basics.basics


-- Identity type

infix 1 _==_
data _==_ {ℓ : Level}{A : Set ℓ}(a : A) : A → Set ℓ where
  =rf : a == a


-- Paulin-Mohring eliminator

=J : {ℓ ℓ' : Level}{A : Set ℓ}{a₀ : A}(B : (a : A) → a₀ == a → Set ℓ')
        → B a₀ =rf → {a : A} → (p : a₀ == a) → B a p
=J B b₀ =rf = b₀

{-
check : {A : Set}{a : A}(p : a == a) → (p == refl)
check =rf = {!!}
-}


-- Some useful properties

=ap : {ℓ ℓ' : Level}{A : Set ℓ}{B : Set ℓ'}(f : A → B){a a' : A}
         → a == a' → f a == f a'
=ap f {a} = =J (λ x _ → f _ == f x) =rf

=transp : {ℓ ℓ' : Level}{A : Set ℓ}(B : A → Set ℓ'){a a' : A}
             → a == a' → B a → B a'
=transp B {a} = =J (λ x _ → B a → B x) (λ y → y)

infix 40 _●_

_●_ : {ℓ ℓ' : Level}{A : Set ℓ}(B : A → Set ℓ'){a a' : A}
         → a == a' → B a → B a'
B ● p = =transp B p

=transpcnst : {ℓ ℓ' : Level}{A : Set ℓ}(B : Set ℓ'){a a' : A}
              (p : a == a')(b : B) → ((λ _ → B) ● p) b == b
=transpcnst B p b = =J (λ x q → ( ((λ _ → B) ● q) b == b )) =rf p

=apd : {ℓ ℓ' : Level}{A : Set ℓ}{B : A → Set ℓ'}
       (f : (a : A) → B a){a a' : A}(p : a == a')
         → (B ● p) (f a) == f a'
=apd f p = =J (λ x p → (_ ● p) (f _) == f x) =rf p

=sym : {ℓ : Level}{A : Set ℓ}{a a' : A}
          → a == a' → a' == a
=sym p = ((λ x → x == _) ● p) =rf

=tra : {ℓ : Level}{A : Set ℓ}{a₁ a₂ a₃ : A}
          → a₁ == a₂ → a₂ == a₃ → a₁ == a₃
=tra p q = ((λ x → _ == x) ● q) p

=transp² : {ℓ₁ ℓ₂ ℓ₃ : Level}{A : Set ℓ₁}{B : A → Set ℓ₂}(C : (x : A) → B x → Set ℓ₃)
           {a a' : A}{b : B a}{b' : B a'}(p : a == a')
             → (B ● p) b == b' → C a b → C a' b'
=transp² {A = A} {B} C {a} {a'} {b} {b'} p q c =
  =transp (λ y → C a' y) q (=J (λ x u → C x ((B ● u) b)) c p)
-- it is the composite C a b → C a' (B●p b) → C a' b'

=transp²cnst¹ : {ℓ₁ ℓ₂ ℓ₃ : Level}{A : Set ℓ₁}{B : Set ℓ₂}(C : A → B → Set ℓ₃){a a' : A}{b b' : B}
                 → a == a' →  b == b' → C a b → C a' b'
=transp²cnst¹ {A = A} {B} C {a} {a'} {b} {b'} p q = =transp² {B = λ _ → B}
                                                             C
                                                             p
                                                             (=tra (=transpcnst B p b) q)


-- Equational reasoning

--infix 3 /_==[_]∎_∎
--infix  3 _∎
infixr 2 /_==[_]_
infixr 1 =proof_==[_]_

=proof_==[_]_ : {ℓ : Level}{A : Set ℓ}(a₁ {a₂ a₃} : A)
                   → a₁ == a₂ → a₂ == a₃ → a₁ == a₃
=proof a ==[ pf ] pf' = =tra pf pf'

--_∎ : {A : Set}(a : A) → a == a
--a ∎ = =rf

/_==[_]_ : {ℓ : Level}{A : Set ℓ}(a₁ {a₂ a₃} : A)
              → a₁ == a₂ → a₂ == a₃ → a₁ == a₃
/ a₁ ==[ pf ] pf' = =tra pf pf'

=eqreasend : {ℓ : Level}{A : Set ℓ}(a₁ a₂ : A)
                → a₁ == a₂ → a₁ == a₂
=eqreasend _ _ pf = pf 

syntax =eqreasend a b pf = / a ==[ pf ]∎ b ∎


-- Notation for inverses and concatenation

infix 60 _⁻¹

_⁻¹ : {ℓ : Level}{A : Set ℓ}{a a' : A} → a == a' → a' == a
p ⁻¹ = =sym p

infixr 50 _■_

_■_ : {ℓ : Level}{A : Set ℓ}{a₁ a₂ a₃ : A} → a₁ == a₂ → a₂ == a₃ → a₁ == a₃
p ■ q = =tra p q


-- Groupoid laws

■tr : {ℓ ℓ' : Level}{A : Set ℓ}(B : A → Set ℓ'){a₁ a₂ a₃ : A}
      (p₁ : a₁ == a₂)(p₂ : a₂ == a₃)(b : B a₁)
         → (B ● (p₁ ■ p₂)) b == (B ● p₂) ((B ● p₁) b)
■tr B p₁ p₂ b = =J (λ x u → (B ● p₁ ■ u) b == (B ● u) ((B ● p₁) b)) =rf p₂

■idr : {ℓ : Level}{A : Set ℓ}{a a' : A}(p : a == a') → p ■ =rf == p
■idr p = =rf

■idl : {ℓ : Level}{A : Set ℓ}{a a' : A}(p : a == a') → =rf ■ p == p
■idl p = =J (λ _ u → =rf ■ u == u) =rf p

■invr : {ℓ : Level}{A : Set ℓ}{a a' : A}(p : a == a') → p ■ p ⁻¹ == =rf
■invr = =J (λ _ u → u ■ u ⁻¹ == =rf) =rf

■invl : {ℓ : Level}{A : Set ℓ}{a a' : A}(p : a == a') → p ⁻¹ ■ p == =rf
■invl = =J (λ _ u → u ⁻¹ ■ u == =rf) =rf

■ass : {ℓ : Level}{A : Set ℓ}{a₁ a₂ a₃ a₄ : A}(p₁ : a₁ == a₂)(p₂ : a₂ == a₃)(p₃ : a₃ == a₄)
           → p₁ ■ (p₂ ■ p₃) == (p₁ ■ p₂) ■ p₃
■ass p₁ p₂ p₃ = ■tr _ p₂ p₃ p₁

■ass⁻¹ : {ℓ : Level}{A : Set ℓ}{a₁ a₂ a₃ a₄ : A}(p₁ : a₁ == a₂)(p₂ : a₂ == a₃)(p₃ : a₃ == a₄)
--(p₁ : a₁ == a₂)(p₂ : a₂ == a₃)(p₃ : a₃ == a₄)
           → (p₁ ■ p₂) ■ p₃ == p₁ ■ (p₂ ■ p₃)
■ass⁻¹ p₁ p₂ p₃ = ■ass p₁ p₂ p₃ ⁻¹


-- Some equations between proofs of equations

■extl : {ℓ : Level}{A : Set ℓ}{a₁ a₂ : A}(p : a₁ == a₂){a₃ : A}{p₁ : a₂ == a₃}{p₂ : a₂ == a₃}
           → p₁ == p₂ → p ■ p₁ == p ■ p₂
■extl p = =ap (λ u → p ■ u)

■extr : {ℓ : Level}{A : Set ℓ}{a₂ a₃ : A}(p : a₂ == a₃){a₁ : A}{p₁ : a₁ == a₂}{p₂ : a₁ == a₂}
           → p₁ == p₂ → p₁ ■ p == p₂ ■ p
■extr p = =ap (λ u → u ■ p)

■ext : {ℓ : Level}{A : Set ℓ}{a₁ a₂ a₃ : A}(p₁ {p₂} : a₁ == a₂)({p₁'} p₂' :  a₂ == a₃)
           → p₁ == p₂ → p₁' == p₂' → p₁ ■ p₁' == p₂ ■ p₂'
■ext p₁ p₂' pf pf' = (■extl p₁ pf') ■ (■extr p₂' pf)


■idlg : {ℓ : Level}{A : Set ℓ}{a₁ a₂ a₃ : A}{p₁ : a₁ == a₁}{p₂ : a₁ == a₂}{p₃ : a₁ == a₂}
         → p₁ == =rf → p₁ ■ p₂ == p₃ → p₂ == p₃
■idlg {p₁ = p₁} {p₂} {p₃} hrf h = =proof p₂         ==[ ■idl p₂ ⁻¹ ] /
                                       =rf ■ p₂   ==[ ■extr p₂ (hrf ⁻¹) ] /
                                       p₁ ■ p₂    ==[ h ]∎
                                       p₃ ∎

■idrg : {ℓ : Level}{A : Set ℓ}{a₁ a₂ a₃ : A}{p₁ : a₁ == a₂}{p₂ : a₂ == a₂}{p₃ : a₁ == a₂}
         → p₂ == =rf → p₁ ■ p₂ == p₃ → p₁ == p₃
■idrg {p₁ = p₁} {p₂} {p₃} hrf h = =proof p₁         ==[ ■idr p₁ ⁻¹ ] /
                                         p₁ ■ =rf   ==[ ■extl p₁ (hrf ⁻¹) ] /
                                         p₁ ■ p₂    ==[ h ]∎
                                         p₃ ∎


■lc : {ℓ : Level}{A : Set ℓ}{a₁ a₂ : A}{p : a₁ == a₂}{a₃ : A}{p₁ : a₂ == a₃}{p₂ : a₂ == a₃}
          → p ■ p₁ == p ■ p₂ → p₁ == p₂
■lc {p = p} {_} {p₁} {p₂} h = =proof p₁           ==[ (■idl p₁ ⁻¹ ■ ■extr p₁ (■invl p ⁻¹)) ■ ■ass⁻¹ _ _ p₁ ] /
                                 p ⁻¹ ■ p ■ p₁    ==[ ■extl (p ⁻¹) h ] /
                                 p ⁻¹ ■ p ■ p₂    ==[ ■ass _ _ p₂ ■ ■extr p₂ (■invl p) ■ ■idl p₂ ]∎
                                 p₂ ∎

■rc : {ℓ : Level}{A : Set ℓ}{a₁ a₂ a₃ : A}{p : a₂ == a₃}{a₁ : A}{p₁ : a₁ == a₂}{p₂ : a₁ == a₂}
          → p₁ ■ p == p₂ ■ p → p₁ == p₂
■rc {p = p} {_} {p₁} {p₂} h = =proof p₁           ==[ ■idr p₁ ⁻¹ ■ ■extl p₁ (■invr p ⁻¹) ] /
                                 p₁ ■ p ■ p ⁻¹    ==[ ■ass _ _ (p ⁻¹)  ■ ■extr (p ⁻¹) h ■ ■ass⁻¹ _ _ (p ⁻¹)  ] /
                                 p₂ ■ p ■ p ⁻¹    ==[ ■extl p₂ (■invr p) ■ ■idr p₂ ]∎
                                 p₂ ∎



-- Equal functions are homotopic

=2htpy : {ℓ ℓ' : Level}{A : Set ℓ}{B : A → Set ℓ'}{f g : (a : A) → B a}
            → f == g → (a : A) → f a == g a
=2htpy {f = f} p a = ((λ x → f a == x a) ● p) =rf

-- part of Lemma 2.9.6 in HoTT book, i.e. same for indexed functions

HoTTLemma2-9-6 : {ℓ ℓ' ℓ'' : Level}{A : Set ℓ}{B : A → Set ℓ'}{C : A → Set ℓ''}
                 {a a' : A}(p : a == a'){f : B a → C a}{g : B a' → C a'}
                   → ((λ x → B x → C x) ● p) f == g → (y : B a) → (C ● p) (f y) == g ((B ● p) y)
HoTTLemma2-9-6 {ℓ} {ℓ'} {ℓ''} {A = A} {B} {C} {a} {a'} p = =J claim claim-rf p
  where claim : (x : A) → a == x → Set (ℓ' ⊔ ℓ'')
        claim x u = {f : B a → C a}{g : B x → C x} → ((λ x → B x → C x) ● u) f == g
                     → (y : B a) → (C ● u) (f y) == g ((B ● u) y)
        claim-rf : claim a =rf
        claim-rf = =2htpy


{-
-- transport of fibrewise functions is pointwise
●ptw : {ℓ : Level}{A : Set ℓ}{B C : A → Set}(f : (a : A) → B a → C a)
       {a a' : A}(p : a == a')(b : B a')
          → ((λ x → B x → C x) ● p) (f a) b == (C ● p) (f a ((B ● p ⁻¹) b))
●ptw f p b = let ψ : _
                 ψ = {!!}
             in {!!}
-}


-- Contractibility and propositions

isContr : {ℓ : Level}(A : Set ℓ) → Set ℓ
isContr A = Σ A (λ a₀ → (a : A) → a == a₀ )

contr₀ : {ℓ : Level}{A : Set ℓ} → isContr A → A
contr₀ = pj1

contr= : {ℓ : Level}{A : Set ℓ}(cnt : isContr A)(a : A)
            → a == contr₀ cnt
contr= = pj2

N₁-isContr : isContr N₁
N₁-isContr = 0₁ , N₁rec =rf

Fin1-isContr : isContr (Fin one)
Fin1-isContr = Fin-singlel , (Finsrec O {λ x → x == Fin-singlel} N₀rec =rf)

isProp : {ℓ : Level}(A : Set ℓ) → Set ℓ
isProp A = (a a' : A) → a == a'

isContr→isProp : {ℓ : Level}{A : Set ℓ} → isContr A → isProp A
isContr→isProp cnt = λ a a' → (contr= cnt a) ■ (contr= cnt a' ⁻¹)

isContr→=isContr : {ℓ : Level}{A : Set ℓ}
                      → isContr A → {a a' : A} → isContr (a == a')
isContr→=isContr cnt = isContr→isProp cnt _ _ , =J (λ x u → u == isContr→isProp cnt _ _)
                                                    (■invr (contr= cnt _) ⁻¹)


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


=inl+ : {ℓ₁ : Level}{A : Set ℓ₁}{ℓ₂ : Level}(B : A → Set ℓ₂){ℓ₃ : Level}(C : A → Set ℓ₃)
        {a a' : A}(p : a == a')
               → (λ b → (B +/ C ● p) (inl b)) == (λ b → inl ((B ● p) b))
=inl+ {A = A} B C {a} = =J (λ a' p → (λ b → (B +/ C ● p) (inl b)) == (λ b → inl ((B ● p) b)))
                           =rf

=inl+-htpy : {ℓ₁ : Level}{A : Set ℓ₁}{ℓ₂ : Level}(B : A → Set ℓ₂){ℓ₃ : Level}(C : A → Set ℓ₃)
             {a a' : A}(p : a == a')(b : B a)
                 → (B +/ C ● p) (inl b) == inl ((B ● p) b)
=inl+-htpy {A = A} B C p = =2htpy (=inl+ B C p)


=inr+ : {ℓ₁ : Level}{A : Set ℓ₁}{ℓ₂ : Level}(B : A → Set ℓ₂){ℓ₃ : Level}(C : A → Set ℓ₃)
         {a a' : A}(p : a == a')
                → (λ c → (B +/ C ● p) (inr c)) == (λ c → inr ((C ● p) c))
=inr+ {A = A} B C {a} = =J (λ a' p → (λ c → (B +/ C ● p) (inr c)) == (λ c → inr ((C ● p) c)))
                           =rf

=inr+-htpy : {ℓ₁ : Level}{A : Set ℓ₁}{ℓ₂ : Level}(B : A → Set ℓ₂){ℓ₃ : Level}(C : A → Set ℓ₃)
             {a a' : A}(p : a == a')(c : C a)
                → (B +/ C ● p) (inr c) == inr ((C ● p) c)
=inr+-htpy {A = A} B C p = =2htpy (=inr+ B C p)



Fin-emb-=nat : {x y : N}(p : x == y)
             → (λ i → (Fin ● =ap s p) (Fin-emb x i)) == (λ i → Fin-emb y ((Fin ● p) i))
Fin-emb-=nat {x} = =J (λ y p → (λ i → (Fin ● =ap s p) (Fin-emb x i)) == (λ i → Fin-emb y ((Fin ● p) i)))
                      =rf

Fin-emb-=nat-hty : {x y : N}(p : x == y)(i : Fin x)
                      → (Fin ● =ap s p) (Fin-emb x i) == Fin-emb y ((Fin ● p) i)
Fin-emb-=nat-hty p = =2htpy (Fin-emb-=nat p)


Fin-max-=nat : {x y : N}(p : x == y)
             → (Fin ● =ap s p) (Fin-max x) == Fin-max y
Fin-max-=nat {x} = =J (λ y p → (Fin ● =ap s p) (Fin-max x) == Fin-max y)
                      =rf


-- UIP stuff

UIP UIPrf  : {ℓ : Level}(A : Set ℓ) → Set ℓ
UIP A = {a a' : A} → isProp (a == a')
UIPrf A = {a : A} (p : a == a) → p == =rf

UIP→UIPrf : {ℓ : Level}{A : Set ℓ} → UIP A → UIPrf A
UIP→UIPrf {A = A} uip p = uip p =rf

UIPrf→UIP : {ℓ : Level}{A : Set ℓ} → UIPrf A → UIP A
UIPrf→UIP {A = A} uiprf {a} = λ p q → =J (λ x u → (v : a == x) → v == u) uiprf q p


HoTT-Thm7-2-2-aux : {ℓ ℓ' : Level}{A : Set ℓ}{R : A → A → Set ℓ'}(Rrf : ∀ a → R a a)
                    (Risprop : ∀ a a' → isProp (R a a'))(R→== : ∀ a a' → R a a' → a == a')
                      → UIPrf A
HoTT-Thm7-2-2-aux {ℓ} {ℓ'} {A = A} {R} Rrf Risprop R→== {a} p =
  ■lc {p = R→== a a (Rrf a)} (q' (Rrf a) ■ ■idr _ ⁻¹)
  where D : A → Set (ℓ ⊔ ℓ')
        D x = R a x → a == x
        q : (D ● p) (R→== a a) == R→== a a
        q = =apd {B = D} (R→== a) p
        q' : (e : R a a) → ((_==_ a) ● p) (R→== a a e) == R→== a a e --(((R a) ● p) e)
        q' e = HoTTLemma2-9-6 p q e ■ =ap (R→== a a) (Risprop a a _ _)


HoTT-Thm7-2-2 : {ℓ ℓ' : Level}{A : Set ℓ}{R : A → A → Set ℓ'}(Rrf : ∀ a → R a a)
                (Risprop : ∀ a a' → isProp (R a a'))(R→== : ∀ a a' → R a a' → a == a')
                 → UIP A
HoTT-Thm7-2-2 Rrf Risprop R→== = UIPrf→UIP (HoTT-Thm7-2-2-aux Rrf Risprop R→==)
