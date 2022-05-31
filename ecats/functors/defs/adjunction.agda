
{-# OPTIONS --without-K #-}

module ecats.functors.defs.adjunction where

open import tt-basics.setoids using (setoidmap; is-bij-pair)
open import ecats.basic-defs.ecat-def&not
open import ecats.basic-defs.isomorphism
open import ecats.basic-props.isomorphism
open import ecats.basic-defs.initial
open import ecats.finite-limits.defs.terminal
open import ecats.functors.defs.efunctor-d&n
open import ecats.functors.defs.natural-transformation
open import ecats.functors.defs.natural-iso
open import ecats.functors.defs.presheaf
open import ecats.functors.defs.representable
open import ecats.functors.props.representable
open import ecats.constructions.opposite
--open import ecats.constructions.slice-ecat
open import ecats.constructions.ecat-elements
open import ecats.concr-ecats.Std-lev


-- Adjunctions

record adjunction-bij {ℓₒ₁ ℓₐ₁ ℓ~₁}{ℂ : ecategoryₗₑᵥ ℓₒ₁ ℓₐ₁ ℓ~₁}{ℓₒ₂ ℓₐ₂ ℓ~₂}{𝔻 : ecategoryₗₑᵥ ℓₒ₂ ℓₐ₂ ℓ~₂}
                      (L : efunctorₗₑᵥ ℂ 𝔻) (R : efunctorₗₑᵥ 𝔻 ℂ)
                      : Set (ecat.ℓₐₗₗ ℂ ⊔ ecat.ℓₐₗₗ 𝔻)
                      where
  private
    module ℂ = ecat ℂ
    module 𝔻 = ecat 𝔻
    module L = efunctor-aux L
    module R = efunctor-aux R
  field
    lr : (A : ℂ.Obj)(B : 𝔻.Obj) → setoidmap (𝔻.Hom (L.ₒ A) B) (ℂ.Hom A (R.ₒ B))
    rl : (A : ℂ.Obj)(B : 𝔻.Obj) → setoidmap (ℂ.Hom A (R.ₒ B)) (𝔻.Hom (L.ₒ A) B)
    isbij : (A : ℂ.Obj)(B : 𝔻.Obj)
             → is-bij-pair (𝔻.Hom (L.ₒ A) B) (ℂ.Hom A (R.ₒ B)) (lr A B) (rl A B)  
  private module bij {A : ℂ.Obj}{B : 𝔻.Obj} = is-bij-pair (isbij A B)
  open bij public
  module lr {A : ℂ.Obj}{B : 𝔻.Obj} = setoidmap (lr A B) renaming (op to ap)
  module rl {A : ℂ.Obj}{B : 𝔻.Obj} = setoidmap (rl A B) renaming (op to ap)
  field
    lr-natl : (B : 𝔻.Obj){A A' : ℂ.Obj}(a : || ℂ.Hom A A' ||)(g : || 𝔻.Hom (L.ₒ A') B ||)
                 → lr.ap (g 𝔻.∘ L.ₐ a) ℂ.~ (lr.ap g) ℂ.∘ a
                 -- (lr ∘ 𝔻[─, L.ₐ a ₐ]).ap g ~ (ℂ[─, a ] ∘ lr).ap g
    lr-natr : (A : ℂ.Obj){B B' : 𝔻.Obj}(b : || 𝔻.Hom B B' ||)(g : || 𝔻.Hom (L.ₒ A) B ||)
                 → lr.ap (b 𝔻.∘ g) ℂ.~ R.ₐ b ℂ.∘ lr.ap g
    rl-natl : (B : 𝔻.Obj){A A' : ℂ.Obj}(a : || ℂ.Hom A A' ||)(f : || ℂ.Hom A' (R.ₒ B) ||)
                 → rl.ap (f ℂ.∘ a) 𝔻.~ (rl.ap f) 𝔻.∘ L.ₐ a
    rl-natr : (A : ℂ.Obj){B B' : 𝔻.Obj}(b : || 𝔻.Hom B B' ||)(f : || ℂ.Hom A (R.ₒ B) ||)
                 → rl.ap (R.ₐ b ℂ.∘ f) 𝔻.~ b 𝔻.∘ rl.ap f


infix 3 _⊣_
_⊣_ : {ℓₒ₁ ℓₐ₁ ℓ~₁ : Level}{ℂ : ecategoryₗₑᵥ ℓₒ₁ ℓₐ₁ ℓ~₁}
      {ℓₒ₂ ℓₐ₂ ℓ~₂ : Level}{𝔻 : ecategoryₗₑᵥ ℓₒ₂ ℓₐ₂ ℓ~₂}
                  → efunctorₗₑᵥ ℂ 𝔻 → efunctorₗₑᵥ 𝔻 ℂ → Set (ecat.ℓₐₗₗ ℂ ⊔ ecat.ℓₐₗₗ 𝔻)
L ⊣ R = adjunction-bij L R


-- via unit + counit + triangular identities

record adjunction-εη {ℓₒ₁ ℓₐ₁ ℓ~₁}{ℂ : ecategoryₗₑᵥ ℓₒ₁ ℓₐ₁ ℓ~₁}{ℓₒ₂ ℓₐ₂ ℓ~₂}{𝔻 : ecategoryₗₑᵥ ℓₒ₂ ℓₐ₂ ℓ~₂}
                     (L : efunctorₗₑᵥ ℂ 𝔻) (R : efunctorₗₑᵥ 𝔻 ℂ)
                     : Set (ecat.ℓₐₗₗ ℂ ⊔ ecat.ℓₐₗₗ 𝔻)
                     where
  private
    module ℂ = ecat ℂ
    module 𝔻 = ecat 𝔻
    module L = efunctorₗₑᵥ L
    module R = efunctorₗₑᵥ R
  field
    ηnt : natural-transformation IdF (R ○ L)
    εnt : natural-transformation (L ○ R) IdF
  module εnt = natural-transformation εnt
  module ηnt = natural-transformation ηnt
  field
    trid₁ : {X : ℂ.Obj} → εnt.fnc 𝔻.∘ (L.ₐ ηnt.fnc) 𝔻.~ 𝔻.idar (L.ₒ X)
    trid₂ : {A : 𝔻.Obj} → (R.ₐ εnt.fnc) ℂ.∘ ηnt.fnc ℂ.~ ℂ.idar (R.ₒ A)


module adjunction-bij-equat {ℓₒ₁ ℓₐ₁ ℓ~₁}{ℂ : ecategoryₗₑᵥ ℓₒ₁ ℓₐ₁ ℓ~₁}
                            {ℓₒ₂ ℓₐ₂ ℓ~₂}{𝔻 : ecategoryₗₑᵥ ℓₒ₂ ℓₐ₂ ℓ~₂}
                            {L : efunctorₗₑᵥ ℂ 𝔻}{R : efunctorₗₑᵥ 𝔻 ℂ}
                            (adjbij : adjunction-bij L R)
                            where
  private
    module ℂ = ecategory-aux ℂ
    module 𝔻 = ecategory-aux 𝔻
    module L = efunctor-aux L
    module R = efunctor-aux R
  open adjunction-bij adjbij

  lr-mono : {A : ℂ.Obj}{B : 𝔻.Obj}{f f' : || 𝔻.Hom (L.ₒ A) B ||}
               → lr.ap f ℂ.~ lr.ap f' → f 𝔻.~ f'
  lr-mono {A} {B} {f} {f'} eq = 𝔻.~proof f                  ~[ iddom f 𝔻.ˢ ] 𝔻./
                                          rl.ap (lr.ap f)    ~[ rl.ext eq ] 𝔻./
                                          rl.ap (lr.ap f')   ~[ iddom f' ]∎
                                          f' ∎

  rl-mono : {A : ℂ.Obj}{B : 𝔻.Obj}{g g' : || ℂ.Hom A (R.ₒ B) ||}
               → rl.ap g 𝔻.~ rl.ap g' → g ℂ.~ g'
  rl-mono {A} {B} {g} {g'} eq = ℂ.~proof g                  ~[ idcod g ℂ.ˢ ] ℂ./
                                          lr.ap (rl.ap g)    ~[ lr.ext eq ] ℂ./
                                          lr.ap (rl.ap g')   ~[ idcod g' ]∎
                                          g' ∎

  lr-sq : {A A' : ℂ.Obj}{B B' : 𝔻.Obj}{f : || 𝔻.Hom (L.ₒ A) B ||}{f' : || 𝔻.Hom (L.ₒ A') B' ||}
          {a : || ℂ.Hom A A' ||}{b : || 𝔻.Hom B B' ||}
            → f' 𝔻.∘ L.ₐ a 𝔻.~ b 𝔻.∘ f → lr.ap f' ℂ.∘ a ℂ.~ R.ₐ b ℂ.∘ lr.ap f
  lr-sq {A} {A'} {B} {B'} {f} {f'} {a} {b} pf = ~proof
    lr.ap f' ℂ.∘ a          ~[ lr-natl B' a f' ˢ ] /
    lr.ap (f' 𝔻.∘ L.ₐ a)    ~[ lr.ext pf ] /
    lr.ap (b 𝔻.∘ f)         ~[ lr-natr A b f ]∎
    R.ₐ b ℂ.∘ lr.ap f ∎
                                              where open ecategory-aux-only ℂ

  rl-sq : {A A' : ℂ.Obj}{B B' : 𝔻.Obj}{g : || ℂ.Hom A (R.ₒ B) ||}{g' : || ℂ.Hom A' (R.ₒ B') ||}
          {a : || ℂ.Hom A A' ||}{b : || 𝔻.Hom B B' ||}
            → g' ℂ.∘ a ℂ.~ R.ₐ b ℂ.∘ g → rl.ap g' 𝔻.∘ L.ₐ a 𝔻.~ b 𝔻.∘ rl.ap g
  rl-sq {A} {A'} {B} {B'} {g} {g'} {a} {b} pf = ~proof
    rl.ap g' 𝔻.∘ L.ₐ a          ~[ rl-natl B' a g' ˢ ] /
    rl.ap (g' ℂ.∘ a)           ~[ rl.ext pf ] /
    rl.ap (R.ₐ b ℂ.∘ g)         ~[ rl-natr A b g ]∎
    b 𝔻.∘ rl.ap g ∎
                                              where open ecategory-aux-only 𝔻

  rl-sq-inv : {A A' : ℂ.Obj}{B B' : 𝔻.Obj}{g : || ℂ.Hom A (R.ₒ B) ||}{g' : || ℂ.Hom A' (R.ₒ B') ||}
              {a : || ℂ.Hom A A' ||}{b : || 𝔻.Hom B B' ||}
                 → rl.ap g' 𝔻.∘ L.ₐ a 𝔻.~ b 𝔻.∘ rl.ap g → g' ℂ.∘ a ℂ.~ R.ₐ b ℂ.∘ g
  rl-sq-inv {A} {A'} {B} {B'} {g} {g'} {a} {b} pf = ~proof
    g' ℂ.∘ a                          ~[ ∘e r (idcod g' ˢ) ] /
    lr.ap (rl.ap g') ℂ.∘ a            ~[ lr-sq pf ] /
    R.ₐ b ℂ.∘ lr.ap (rl.ap g)         ~[ ∘e (idcod g) r ]∎
    R.ₐ b ℂ.∘ g ∎
                                              where open ecategory-aux-only ℂ


  lr-sq-inv : {A A' : ℂ.Obj}{B B' : 𝔻.Obj}{f : || 𝔻.Hom (L.ₒ A) B ||}{f' : || 𝔻.Hom (L.ₒ A') B' ||}
              {a : || ℂ.Hom A A' ||}{b : || 𝔻.Hom B B' ||}
                 → lr.ap f' ℂ.∘ a ℂ.~ R.ₐ b ℂ.∘ lr.ap f → f' 𝔻.∘ L.ₐ a 𝔻.~ b 𝔻.∘ f
  lr-sq-inv {A} {A'} {B} {B'} {f} {f'} {a} {b} pf = ~proof
    f' 𝔻.∘ L.ₐ a                  ~[ ∘e r (iddom f' ˢ) ] /
    rl.ap (lr.ap f') 𝔻.∘ L.ₐ a    ~[ rl-sq pf ] /
    b 𝔻.∘ rl.ap (lr.ap f)         ~[ ∘e (iddom f) r ]∎
    b 𝔻.∘ f ∎
                                              where open ecategory-aux-only 𝔻

  ηnt : natural-transformation IdF (R ○ L)
  ηnt = record
      { fnc = λ {A} → lr.ap (𝔻.idar (L.ₒ A))
      ; nat = λ {A} {A'} f → lr-sq (𝔻.lidgen 𝔻.ridˢ)
      }
  private module ηnt = natural-transformation ηnt


  εnt : natural-transformation (L ○ R) IdF
  εnt = record
      { fnc = λ {B} → rl.ap (ℂ.idar (R.ₒ B))
      ; nat = λ {B} {B'} g → rl-sq (ℂ.lidgen ℂ.ridˢ)
      }
  private module εnt = natural-transformation εnt

  ηeq : {A : ℂ.Obj}{B : 𝔻.Obj}(f : || 𝔻.Hom (L.ₒ A) B ||)
           → R.ₐ f ℂ.∘ ηnt.fnc {A} ℂ.~ lr.ap f
  ηeq {A} {B} f =  (ℂ.ridˢ ℂ.⊙ lr-sq (𝔻.ridgg 𝔻.ridˢ L.id)) ℂ.ˢ

  εeq : {A : ℂ.Obj}{B : 𝔻.Obj}(g : || ℂ.Hom A (R.ₒ B) ||)
           → εnt.fnc {B} 𝔻.∘ L.ₐ g 𝔻.~ rl.ap g
  εeq {A} {B} g = rl-sq (ℂ.lidggˢ ℂ.lid R.id) 𝔻.⊙ 𝔻.lid
  
  is-trid : adjunction-εη L R
  is-trid = record
    { ηnt = ηnt
    ; εnt = εnt
    ; trid₁ = trid₁
    ; trid₂ = trid₂
    }
    where trid₁ : {A : ℂ.Obj} → εnt.fnc {L.ₒ A} 𝔻.∘ L.ₐ (ηnt.fnc {A}) 𝔻.~ 𝔻.idar (L.ₒ A)
          trid₁ {A} = ~proof
            εnt.fnc {L.ₒ A} 𝔻.∘ L.ₐ (ηnt.fnc {A})   ~[ εeq (ηnt.fnc {A}) ] /
            rl.ap (ηnt.fnc {A})                     ~[ iddom (𝔻.idar (L.ₒ A)) ]∎
            𝔻.idar (L.ₒ A) ∎
                    where open ecategory-aux-only 𝔻              
          trid₂ : {B : 𝔻.Obj} → R.ₐ (εnt.fnc {B}) ℂ.∘ ηnt.fnc {R.ₒ B} ℂ.~ ℂ.idar (R.ₒ B)
          trid₂ {B} = ~proof
            R.ₐ (εnt.fnc {B}) ℂ.∘ ηnt.fnc {R.ₒ B}  ~[ ηeq (εnt.fnc {B}) ] /
            lr.ap (εnt.fnc {B})                    ~[ idcod (ℂ.idar (R.ₒ B)) ]∎
            ℂ.idar (R.ₒ B) ∎
                    where open ecategory-aux-only ℂ
-- end adjunction-bij-equat


adj-bij→trid : {ℓₒ₁ ℓₐ₁ ℓ~₁ : Level}{ℂ : ecategoryₗₑᵥ ℓₒ₁ ℓₐ₁ ℓ~₁}
                {ℓₒ₂ ℓₐ₂ ℓ~₂ : Level}{𝔻 : ecategoryₗₑᵥ ℓₒ₂ ℓₐ₂ ℓ~₂}
                {L : efunctorₗₑᵥ ℂ 𝔻}{R : efunctorₗₑᵥ 𝔻 ℂ}
                  → adjunction-bij L R → adjunction-εη L R
adj-bij→trid = adjunction-bij-equat.is-trid
                            



-- The natural iso formulation needs categories with hom-sets at the same universe level

record adjunction-iso {ℓₒ₁ ℓₐ ℓ~}{ℂ 𝔻 : ecategoryₗₑᵥ ℓₒ₁ ℓₐ ℓ~}{ℓₒ₂}{𝔻 : ecategoryₗₑᵥ ℓₒ₂ ℓₐ ℓ~}
                      (L : efunctorₗₑᵥ ℂ 𝔻)(R : efunctorₗₑᵥ 𝔻 ℂ)
                      : Set (ecat.ℓₐₗₗ ℂ ⊔ ecat.ℓₒ 𝔻)
                      where
  private
    module ℂ = ecat ℂ
    module 𝔻 = ecat 𝔻
    module L = efunctor-aux L
    module R = efunctor-aux R
    module Std = ecat (Stdₗₑᵥ ℓₐ ℓ~)
    module lrnatl-def (B : 𝔻.Obj) = natural-trans-defs (𝔻 [─, B ₒ] ○ L ᵒ) (ℂ [─, (R.ₒ B) ₒ])
    module lrnatr-def (A : ℂ.Obj) = natural-trans-defs (𝔻 [ₒ L.ₒ A ,─]) (ℂ [ₒ A ,─] ○ R)
    --module rlnatl-def (B : 𝔻.Obj) = natural-trans-defs (ℂ [─, (R.ₒ B) ₒ]) (𝔻 [─, B ₒ] ○ L.ᵒᵖ)
    --module rlnatr-def (A : ℂ.Obj) = natural-trans-defs (ℂ [ₒ A ,─] ○ R) (𝔻 [ₒ L.ₒ A ,─])    
  field
    liso : (B : 𝔻.Obj) → (𝔻 [─, B ₒ] ○ L ᵒ) ≅ₐ (ℂ [─, (R.ₒ B) ₒ])
    riso : (A : ℂ.Obj) →  (𝔻 [ₒ L.ₒ A ,─]) ≅ₐ (ℂ [ₒ A ,─] ○ R)
  module liso (B : 𝔻.Obj) = natural-iso (liso B)
  module riso (A : ℂ.Obj) = natural-iso (riso A)
  field
    lnat : (B : 𝔻.Obj) → lrnatl-def.is-natural B (liso.fnc B)
    rnat : (A : ℂ.Obj) → lrnatr-def.is-natural A (riso.fnc A)


-- Via universal properties of unit and counit.

-- I'd like to go through representability of (co)presheaves,
-- so we need to restrict to adjunctions between categories
-- with hom-sets at the same universe level.

-- Otherwise, use the defintion of category of elements as a slice over/under a functor
-- (no need to restrict to presheaves here), and prove the (co)unit initial/terminal there.
-- See below, commented out.

private      
  module coelem-aux {ℓₒ₁ ℓₐ ℓ~}{ℂ : ecategoryₗₑᵥ ℓₒ₁ ℓₐ ℓ~}{ℓₒ₂}{𝔻 : ecategoryₗₑᵥ ℓₒ₂ ℓₐ ℓ~}
                    (L : efunctorₗₑᵥ ℂ 𝔻)(R : efunctorₗₑᵥ 𝔻 ℂ)
                    (A : ecat.Obj ℂ) where
      [A,R─] : copresheafₗₑᵥ 𝔻
      [A,R─] = ℂ [ₒ A ,─] ○ R
      open ecategory-aux (ecat-coelmts [A,R─]) public
      open ecat-coelmts [A,R─] public
      open initial-defs (ecat-coelmts [A,R─]) public
      
  module elem-aux {ℓₒ₁ ℓₐ ℓ~}{ℂ : ecategoryₗₑᵥ ℓₒ₁ ℓₐ ℓ~}{ℓₒ₂}{𝔻 : ecategoryₗₑᵥ ℓₒ₂ ℓₐ ℓ~}
                  (L : efunctorₗₑᵥ ℂ 𝔻)(R : efunctorₗₑᵥ 𝔻 ℂ)
                  (B : ecat.Obj 𝔻) where
      [L─,B] : presheafₗₑᵥ ℂ 
      [L─,B] = 𝔻 [─, B ₒ] ○ L ᵒ      
      open ecategory-aux (ecat-elmts [L─,B]) public
      open ecat-elmts [L─,B]  public
      open terminal-defs (ecat-elmts [L─,B]) public
      

record adjunction-η {ℓₒ₁ ℓₐ ℓ~}{ℂ : ecategoryₗₑᵥ ℓₒ₁ ℓₐ ℓ~}{ℓₒ₂}{𝔻 : ecategoryₗₑᵥ ℓₒ₂ ℓₐ ℓ~}
                    (L : efunctorₗₑᵥ ℂ 𝔻)(R : efunctorₗₑᵥ 𝔻 ℂ)
                    : Set (ecat.ℓₐₗₗ ℂ ⊔ ecat.ℓₒ 𝔻)
                    where
  private
    module ℂ = ecat ℂ
    module 𝔻 = ecat 𝔻
    module L = efctr L
    module R = efctr R
    module ∫[ℂ,R─] (A : ℂ.Obj) = coelem-aux L R A
  field
    ηnt : natural-transformation IdF (R ○ L)
  module ηnt = natural-transformation ηnt
  field
    isinit : (A : ℂ.Obj) → ∫[ℂ,R─].is-initial A (∫[ℂ,R─].el/ A (ηnt.fnc {A}))
  module unv (A : ℂ.Obj){B : 𝔻.Obj}(g : || ℂ.Hom A (R.ₒ B) ||) where
    open ∫[ℂ,R─].is-initial A (isinit A)
    open ∫[ℂ,R─].ₐ A (ø (∫[ℂ,R─].el/ A g)) public
    uq : {f : || 𝔻.Hom (L.ₒ A) B ||}
            → R.ₐ f ℂ.∘ ηnt.fnc {A} ℂ.~ g → f 𝔻.~ ar
    uq {f} tr' = øuq (∫[ℂ,R─].ar/ A f tr')
    uqg : {f f' : || 𝔻.Hom (L.ₒ A) B ||}
             → R.ₐ f ℂ.∘ ηnt.fnc {A} ℂ.~ R.ₐ f' ℂ.∘ ηnt.fnc {A} → f 𝔻.~ f'
    uqg {f} {f'} pf = øuqg {f = ∫[ℂ,R─].ar/ A f pf}
                           {∫[ℂ,R─].ar/ A f' r}
                    where open ecategory-aux-only ℂ using (r)

      
record adjunction-ε {ℓₒ₁ ℓₐ ℓ~}{ℂ : ecategoryₗₑᵥ ℓₒ₁ ℓₐ ℓ~}{ℓₒ₂}{𝔻 : ecategoryₗₑᵥ ℓₒ₂ ℓₐ ℓ~}
                    (L : efunctorₗₑᵥ ℂ 𝔻)(R : efunctorₗₑᵥ 𝔻 ℂ)
                    : Set (ecat.ℓₐₗₗ ℂ ⊔ ecat.ℓₒ 𝔻)
                    where
  private
    module ℂ = ecat ℂ
    module 𝔻 = ecat 𝔻
    module L = efunctorₗₑᵥ L
    module R = efunctorₗₑᵥ R
    module ∫[L─,𝔻] (B : 𝔻.Obj) = elem-aux L R B    
  field
    εnt : natural-transformation (L ○ R) IdF
  module εnt = natural-transformation εnt
  field
    isterm : (B : 𝔻.Obj) → ∫[L─,𝔻].is-terminal B (∫[L─,𝔻].el/ B (εnt.fnc {B}))
  module unv (B : 𝔻.Obj){A : ℂ.Obj}(g : || 𝔻.Hom (L.ₒ A) B ||) where
    open ∫[L─,𝔻].is-terminal B (isterm B)
    open ∫[L─,𝔻].ₐ B (! (∫[L─,𝔻].el/ B g)) public
    uq : {f : || ℂ.Hom A (R.ₒ B) ||}
            → εnt.fnc {B} 𝔻.∘ L.ₐ f 𝔻.~ g → f ℂ.~ ar
    uq {f} tr' = !uniq (∫[L─,𝔻].ar/ B f tr')
    uqg : {f f' : || ℂ.Hom A (R.ₒ B) ||}
             → εnt.fnc {B} 𝔻.∘ L.ₐ f 𝔻.~ εnt.fnc {B} 𝔻.∘ L.ₐ f' → f ℂ.~ f'
    uqg {f} {f'} pf = !uqg {f = ∫[L─,𝔻].ar/ B f pf}
                           {∫[L─,𝔻].ar/ B f' r}
                    where open ecategory-aux-only 𝔻 using (r)


module bij→univ {ℓₒ₁ ℓₐ ℓ~}{ℂ : ecategoryₗₑᵥ ℓₒ₁ ℓₐ ℓ~}{ℓₒ₂}{𝔻 : ecategoryₗₑᵥ ℓₒ₂ ℓₐ ℓ~}
                 {L : efunctorₗₑᵥ ℂ 𝔻}{R : efunctorₗₑᵥ 𝔻 ℂ}(adjbij : adjunction-bij L R)
                 where
  private
    module ℂ = ecategory-aux ℂ
    module 𝔻 = ecategory-aux 𝔻
    module L = efunctor-aux L
    module R = efunctor-aux R
    module ∫[ℂ,R─] (A : ℂ.Obj) = coelem-aux L R A
    module ∫[L─,𝔻] (B : 𝔻.Obj) = elem-aux L R B    
  open adjunction-bij adjbij
  open adjunction-bij-equat adjbij
  
  private
    module ηnt = natural-transformation ηnt
    module εnt = natural-transformation εnt
    [_,R─] : (A : ℂ.Obj) → copresheafₗₑᵥ 𝔻
    [ A ,R─] = ∫[ℂ,R─].[A,R─] A
    [L─,_] : (B : 𝔻.Obj) → presheafₗₑᵥ ℂ 
    [L─, B ] = ∫[L─,𝔻].[L─,B] B

  HR-is-repres : (A : ℂ.Obj) → is-represble-copsheaf [ A ,R─]
  HR-is-repres A = record
    { Rob = L.ₒ A
    ; natiso = record
             { natt = record
               { fnc = λ {B} → rl A B
               ; nat = rl-natr A
               }
             ; natt⁻¹ = record
               { fnc = λ {B} → lr A B
               ; nat = lr-natr A 
               }
             ; isiso = record
               { iddom = idcod
               ; idcod = iddom
               }
             }
    }    

  ηinit : (A : ℂ.Obj) → ∫[ℂ,R─].is-initial A (∫[ℂ,R─].el/ A (ηnt.fnc {A}))
  ηinit A = isinit
          where open representable-copsheaf-props [ A ,R─]
                open has-initial (repres→init (HR-is-repres A))

  HL-is-repres : (B : 𝔻.Obj) → is-represble-copsheaf [L─, B ]
  HL-is-repres B = record
    { Rob = R.ₒ B
    ; natiso = record
             { natt = record
               { fnc = λ {A} → lr A B
               ; nat = lr-natl B
               }
             ; natt⁻¹ = record
               { fnc = λ {A} → rl A B
               ; nat = rl-natl B
               }
             ; isiso = record
               { iddom = iddom
               ; idcod = idcod
               }
             }
    }    

  εterm : (B : 𝔻.Obj) → ∫[L─,𝔻].is-terminal B (∫[L─,𝔻].el/ B (εnt.fnc {B}))
  εterm B = istrm
          where open representable-psheaf-props [L─, B ]
                open has-terminal (repres→term (HL-is-repres B))

  η : adjunction-η L R
  η = record
    { ηnt = ηnt
    ; isinit = ηinit
    }

  ε : adjunction-ε L R
  ε = record
    { εnt = εnt
    ; isterm = εterm
    }
  
-- end bij→univ



--   private
--     module ℂ↓R (A : ℂ.Obj) where
--       open ecategory-aux (A ₒ↓ R) public
--       open slice-funct-ecat R A public
--       open initial-defs (A ₒ↓ R) public
--     module L↓𝔻 (B : 𝔻.Obj) where
--       open ecategory-aux (L ↓ₒ B) public
--       open funct-slice-ecat L B public
--       open terminal-defs (L ↓ₒ B) public
--     module ∫𝔻[F─,B] where      

--   bijlr : (A : ℂ.Obj)(B : 𝔻.Obj) → setoidmap (𝔻.Hom (L.ₒ A) B) (ℂ.Hom A (R.ₒ B))
--   bijlr A B = record
--     { op = λ g → R.ₐ g ℂ.∘ ηnt.fnc {A}
--     ; ext = λ {g} {g'} eq → ∘e r (R.ext eq)
--     }
--     where open ecategory-aux-only ℂ
  
--   bijrl : (A : ℂ.Obj)(B : 𝔻.Obj) → setoidmap (ℂ.Hom A (R.ₒ B)) (𝔻.Hom (L.ₒ A) B)
--   bijrl A B = record
--     { op = λ f → εnt.fnc {B} 𝔻.∘ L.ₐ f
--     ; ext = λ {f} {f'} eq → ∘e (L.ext eq) r
--     }
--     where open ecategory-aux-only 𝔻
 
--   isbij : (A : ℂ.Obj)(B : 𝔻.Obj)
--              → is-bij-pair (𝔻.Hom (L.ₒ A) B) (ℂ.Hom A (R.ₒ B)) (bijlr A B) (bijrl A B)
--   isbij A B = record
--     { iddom = iddom
--     ; idcod = idcod
--     }
--     where iddom : < 𝔻.Hom (L.ₒ A) B ⇒ₛ 𝔻.Hom (L.ₒ A) B >
--                           std-cmp (bijrl A B) (bijlr A B) ~ std-id
--           iddom = λ g → ~proof
--                   εnt.fnc {B} 𝔻.∘ L.ₐ (R.ₐ g ℂ.∘ ηnt.fnc {A})        ~[ ∘e L.∘ax-rfˢ r ] /
--                   εnt.fnc {B} 𝔻.∘ L.ₐ (R.ₐ g) 𝔻.∘ L.ₐ (ηnt.fnc {A})  ~[ ass ⊙ ∘e r (εnt.nat g) ] /
--                   (g 𝔻.∘ εnt.fnc {L.ₒ A}) 𝔻.∘ L.ₐ (ηnt.fnc {A})      ~[ assˢ ⊙ ridgg r trid₁ ]∎
--                   g ∎
--                 where open ecategory-aux-only 𝔻
--           idcod : < (ℂ.Hom A (R.ₒ B)) ⇒ₛ (ℂ.Hom A (R.ₒ B)) >
--                              std-cmp (bijlr A B) (bijrl A B) ~ std-id
--           idcod = λ f → ~proof R.ₐ (εnt.fnc 𝔻.∘ L.ₐ f) ℂ.∘ ηnt.fnc       ~[ ∘e r R.∘ax-rfˢ ⊙ assˢ ] /
--                                 R.ₐ εnt.fnc ℂ.∘ R.ₐ  (L.ₐ f) ℂ.∘ ηnt.fnc   ~[ ∘e (ηnt.nat f ˢ) r ] /
--                                 R.ₐ εnt.fnc ℂ.∘ ηnt.fnc ℂ.∘ f             ~[ ass ⊙ lidgg r trid₂ ]∎
--                                 f ∎
--                 where open ecategory-aux-only ℂ

--   module bij {A : ℂ.Obj}{B : 𝔻.Obj} where
--     open is-bij-pair (isbij A B) public
--     module lr = setoidmap (bijlr A B) renaming (op to ap)
--     module rl = setoidmap (bijrl A B) renaming (op to ap)
    

--   η-initial : (A : ℂ.Obj) → ℂ↓R.is-initial A (ℂ↓R.ηcone A)
--   η-initial A = record
--     { 𝕚 = λ f → record
--         { arR = bij.rl.ap (ℂ↓R.ₒ.ar f)
--         ; tr = bij.idcod (ℂ↓R.ₒ.ar f) 
--         }
--     ; 𝕚uq = λ {f} g → ~proof ℂ↓R.ₐ.arR g                          ~[ bij.iddom (ℂ↓R.ₐ.arR g) ˢ ] /
--                               bij.rl.ap (bij.lr.ap (ℂ↓R.ₐ.arR g))  ~[ bij.rl.ext (ℂ↓R.ₐ.tr g) ]∎
--                               bij.rl.ap (ℂ↓R.ₒ.ar f) ∎
--     }
--     where open ecategory-aux-only 𝔻

--   ε-terminal : (B : 𝔻.Obj) → L↓𝔻.is-terminal B (L↓𝔻.εcone B)
--   ε-terminal B = record
--     { ! = λ g → record
--         { arL = bij.lr.ap (L↓𝔻.ₒ.ar g)
--         ; tr = bij.iddom (L↓𝔻.ₒ.ar g) 
--         }
--     ; !uniq = λ {g} f → ~proof L↓𝔻.ₐ.arL f                          ~[ bij.idcod (L↓𝔻.ₐ.arL f) ˢ ] /
--                                 bij.lr.ap (bij.rl.ap (L↓𝔻.ₐ.arL f))  ~[ bij.lr.ext (L↓𝔻.ₐ.tr f) ]∎
--                                 bij.lr.ap (L↓𝔻.ₒ.ar g) ∎
--     }
--     where open ecategory-aux-only ℂ  
-- -- end adjunction-univ-props
