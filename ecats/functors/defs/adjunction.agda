
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
open import ecats.constructions.ecat-elements
open import ecats.constructions.comma-ecat
open import ecats.concr-ecats.Std-lev


-- Adjunctions

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
  trid₁g : {X : ℂ.Obj}{A : 𝔻.Obj}(g : || 𝔻.Hom (L.ₒ X) A ||)
              → εnt.fnc 𝔻.∘ L.ₐ (R.ₐ g) 𝔻.∘ L.ₐ ηnt.fnc 𝔻.~ g
  trid₁g g = ~proof εnt.fnc 𝔻.∘ L.ₐ (R.ₐ g) 𝔻.∘ L.ₐ ηnt.fnc    ~[ ass ⊙ ∘e r (εnt.nat g) ⊙ assˢ ] /
                    g 𝔻.∘ εnt.fnc 𝔻.∘ L.ₐ ηnt.fnc              ~[ ridgg r trid₁ ]∎
                    g ∎
           where open ecategory-aux-only 𝔻
  trid₂g : {X : ℂ.Obj}{A : 𝔻.Obj}(f : || ℂ.Hom X (R.ₒ A) ||)
              → R.ₐ εnt.fnc ℂ.∘  R.ₐ (L.ₐ f) ℂ.∘ ηnt.fnc ℂ.~ f
  trid₂g f = ~proof R.ₐ εnt.fnc ℂ.∘  R.ₐ (L.ₐ f) ℂ.∘ ηnt.fnc    ~[ ∘e (ηnt.natˢ f) r ] /
                    R.ₐ εnt.fnc ℂ.∘ ηnt.fnc ℂ.∘ f               ~[ ass ⊙ lidgg r trid₂ ]∎
                    f ∎
           where open ecategory-aux-only ℂ
                              


-- notation

infix 3 _⊣_
_⊣_ : {ℓₒ₁ ℓₐ₁ ℓ~₁ : Level}{ℂ : ecategoryₗₑᵥ ℓₒ₁ ℓₐ₁ ℓ~₁}
      {ℓₒ₂ ℓₐ₂ ℓ~₂ : Level}{𝔻 : ecategoryₗₑᵥ ℓₒ₂ ℓₐ₂ ℓ~₂}
                  → efunctorₗₑᵥ ℂ 𝔻 → efunctorₗₑᵥ 𝔻 ℂ → Set (ecat.ℓₐₗₗ ℂ ⊔ ecat.ℓₐₗₗ 𝔻)
L ⊣ R = adjunction-εη L R

module adjunction-εη-equats {ℓₒ₁ ℓₐ₁ ℓ~₁}{ℂ : ecategoryₗₑᵥ ℓₒ₁ ℓₐ₁ ℓ~₁}
                            {ℓₒ₂ ℓₐ₂ ℓ~₂}{𝔻 : ecategoryₗₑᵥ ℓₒ₂ ℓₐ₂ ℓ~₂}
                            {L : efunctorₗₑᵥ ℂ 𝔻}{R : efunctorₗₑᵥ 𝔻 ℂ}
                            (L⊣R : adjunction-εη L R)
                            where
  open adjunction-εη L⊣R
  private
    module ℂ = ecat ℂ
    module 𝔻 = ecat 𝔻
    module L = efunctor-aux L
    module R = efunctor-aux R
    module RL = efunctor-aux (R ○ L)
    module LR = efunctor-aux (L ○ R)
    module ε = natural-transformation εnt
    module η = natural-transformation ηnt

  lr-sq : {A A' : ℂ.Obj}{B B' : 𝔻.Obj}{f : || 𝔻.Hom (L.ₒ A) B ||}{f' : || 𝔻.Hom (L.ₒ A') B' ||}
          {a : || ℂ.Hom A A' ||}{b : || 𝔻.Hom B B' ||}
            → f' 𝔻.∘ L.ₐ a 𝔻.~ b 𝔻.∘ f
              → R.ₐ f' ℂ.∘ η.fnc ℂ.∘ a ℂ.~ R.ₐ b ℂ.∘ R.ₐ f ℂ.∘ η.fnc
  lr-sq {A} {A'} {B} {B'} {f} {f'} {a} {b} pf = ~proof
    R.ₐ f' ℂ.∘ η.fnc ℂ.∘ a          ~[ ∘e (η.nat a) r ] /
    R.ₐ f' ℂ.∘ RL.ₐ a ℂ.∘ η.fnc     ~[ ass ⊙ ∘e r (R.∘∘ pf) ⊙ assˢ ]∎
    R.ₐ b ℂ.∘ R.ₐ f ℂ.∘ η.fnc ∎
                                              where open ecategory-aux-only ℂ

  rl-sq : {A A' : ℂ.Obj}{B B' : 𝔻.Obj}{g : || ℂ.Hom A (R.ₒ B) ||}{g' : || ℂ.Hom A' (R.ₒ B') ||}
          {a : || ℂ.Hom A A' ||}{b : || 𝔻.Hom B B' ||}
            → g' ℂ.∘ a ℂ.~ R.ₐ b ℂ.∘ g
              → ε.fnc 𝔻.∘ L.ₐ g' 𝔻.∘ L.ₐ a 𝔻.~ b 𝔻.∘ ε.fnc 𝔻.∘ L.ₐ g
  rl-sq {A} {A'} {B} {B'} {g} {g'} {a} {b} pf = ~proof
    ε.fnc 𝔻.∘ L.ₐ g' 𝔻.∘ L.ₐ a         ~[ ∘e (L.∘∘ pf) r ] /
    ε.fnc 𝔻.∘ LR.ₐ b 𝔻.∘ L.ₐ g         ~[ ass ⊙ ∘e r (ε.nat b) ⊙ assˢ ]∎
    b 𝔻.∘ ε.fnc 𝔻.∘ L.ₐ g ∎
                                              where open ecategory-aux-only 𝔻


  lr-mono : {A : ℂ.Obj}{B : 𝔻.Obj}{g g' : || 𝔻.Hom (L.ₒ A) B ||}
               → R.ₐ g ℂ.∘ η.fnc ℂ.~ R.ₐ g' ℂ.∘ η.fnc → g 𝔻.~ g'
  lr-mono {A} {B} {g} {g'} eq = ~proof
                              g                                  ~[ trid₁g g ˢ ] /
                              ε.fnc 𝔻.∘ LR.ₐ g 𝔻.∘ L.ₐ η.fnc    ~[ ∘e (L.∘∘ eq) r ] /
                              ε.fnc 𝔻.∘ LR.ₐ g' 𝔻.∘ L.ₐ η.fnc   ~[ trid₁g g' ]∎
                              g' ∎
                              where open ecategory-aux-only 𝔻

  rl-mono : {A : ℂ.Obj}{B : 𝔻.Obj}{f f' : || ℂ.Hom A (R.ₒ B) ||}
               → ε.fnc 𝔻.∘ L.ₐ f 𝔻.~ ε.fnc 𝔻.∘ L.ₐ f' → f ℂ.~ f'
  rl-mono {A} {B} {f} {f'} eq = ~proof
                              f                                  ~[ trid₂g f ˢ ] /
                              R.ₐ ε.fnc ℂ.∘ RL.ₐ f ℂ.∘ η.fnc     ~[ ass ⊙ ∘e r (R.∘∘ eq) ⊙ assˢ ] /
                              R.ₐ ε.fnc ℂ.∘ RL.ₐ f' ℂ.∘ η.fnc    ~[ trid₂g f' ]∎
                              f' ∎
                              where open ecategory-aux-only ℂ


  rl-sq-inv : {A A' : ℂ.Obj}{B B' : 𝔻.Obj}{g : || ℂ.Hom A (R.ₒ B) ||}{g' : || ℂ.Hom A' (R.ₒ B') ||}
              {a : || ℂ.Hom A A' ||}{b : || 𝔻.Hom B B' ||}
                 → ε.fnc 𝔻.∘ L.ₐ g' 𝔻.∘ L.ₐ a 𝔻.~ b 𝔻.∘ ε.fnc 𝔻.∘ L.ₐ g
                   → g' ℂ.∘ a ℂ.~ R.ₐ b ℂ.∘ g
  rl-sq-inv {A} {A'} {B} {B'} {g} {g'} {a} {b} pf = rl-mono (~proof
    ε.fnc 𝔻.∘ L.ₐ (g' ℂ.∘ a)         ~[ ∘e L.∘ax-rfˢ r ⊙ pf ] /
    b 𝔻.∘ ε.fnc 𝔻.∘ L.ₐ g           ~[ ass ⊙ ∘e r (ε.natˢ b) ⊙ assˢ ] /
    ε.fnc 𝔻.∘ LR.ₐ b 𝔻.∘ L.ₐ g      ~[ ∘e L.∘ax-rf r ]∎
    ε.fnc 𝔻.∘ L.ₐ (R.ₐ b ℂ.∘ g) ∎)
                                                  where open ecategory-aux-only 𝔻

  lr-sq-inv : {A A' : ℂ.Obj}{B B' : 𝔻.Obj}{f : || 𝔻.Hom (L.ₒ A) B ||}{f' : || 𝔻.Hom (L.ₒ A') B' ||}
              {a : || ℂ.Hom A A' ||}{b : || 𝔻.Hom B B' ||}
                 → R.ₐ f' ℂ.∘ η.fnc ℂ.∘ a ℂ.~ R.ₐ b ℂ.∘ R.ₐ f ℂ.∘ η.fnc
                   → f' 𝔻.∘ L.ₐ a 𝔻.~ b 𝔻.∘ f
  lr-sq-inv {A} {A'} {B} {B'} {f} {f'} {a} {b} pf = lr-mono (~proof
    R.ₐ (f' 𝔻.∘ L.ₐ a) ℂ.∘ η.fnc    ~[ ∘e r R.∘ax-rfˢ ⊙ (assˢ ⊙ ∘e (η.natˢ a) r) ] /
    R.ₐ f' ℂ.∘ η.fnc ℂ.∘ a           ~[ pf ] /    
    R.ₐ b ℂ.∘ R.ₐ f ℂ.∘ η.fnc        ~[ ass ⊙ ∘e r R.∘ax-rf ]∎
    R.ₐ (b 𝔻.∘ f) ℂ.∘ η.fnc ∎)
                                                  where open ecategory-aux-only ℂ

-- end adjunction-εη-equats


record is-right-adjoint {ℓₒ₁ ℓₐ₁ ℓ~₁ : Level}{ℂ : ecategoryₗₑᵥ ℓₒ₁ ℓₐ₁ ℓ~₁}
                        {ℓₒ₂ ℓₐ₂ ℓ~₂ : Level}{𝔻 : ecategoryₗₑᵥ ℓₒ₂ ℓₐ₂ ℓ~₂}
                        (F : efunctorₗₑᵥ ℂ 𝔻)
                        : Set (ecat.ℓₐₗₗ ℂ ⊔ ecat.ℓₐₗₗ 𝔻)
                        where
  private
    module ℂ = ecat ℂ
    module 𝔻 = ecat 𝔻
    module F = efctr F
  field
    left : efunctorₗₑᵥ 𝔻 ℂ
    areadj : left ⊣ F
  module left = efunctor-aux left
  open adjunction-εη areadj public
  open adjunction-εη-equats areadj public

record is-left-adjoint {ℓₒ₁ ℓₐ₁ ℓ~₁ : Level}{ℂ : ecategoryₗₑᵥ ℓₒ₁ ℓₐ₁ ℓ~₁}
                       {ℓₒ₂ ℓₐ₂ ℓ~₂ : Level}{𝔻 : ecategoryₗₑᵥ ℓₒ₂ ℓₐ₂ ℓ~₂}
                       (F : efunctorₗₑᵥ ℂ 𝔻)
                       : Set (ecat.ℓₐₗₗ ℂ ⊔ ecat.ℓₐₗₗ 𝔻)
                       where
  private
    module ℂ = ecat ℂ
    module 𝔻 = ecat 𝔻
    module F = efctr F
  field
    right : efunctorₗₑᵥ 𝔻 ℂ
    areadj : F ⊣ right
  module right = efunctor-aux right
  open adjunction-εη areadj public
  open adjunction-εη-equats areadj public

record adjunction-εη-btw {ℓₒ₁ ℓₐ₁ ℓ~₁}(ℂ : ecategoryₗₑᵥ ℓₒ₁ ℓₐ₁ ℓ~₁)
                         {ℓₒ₂ ℓₐ₂ ℓ~₂}(𝔻 : ecategoryₗₑᵥ ℓₒ₂ ℓₐ₂ ℓ~₂)
                         : Set (ecat.ℓₐₗₗ ℂ ⊔ ecat.ℓₐₗₗ 𝔻)
                         where
  private
    module ℂ = ecat ℂ
    module 𝔻 = ecat 𝔻
  field
    left : efunctorₗₑᵥ ℂ 𝔻
    right : efunctorₗₑᵥ 𝔻 ℂ
    areadj : left ⊣ right
  module left = efunctor-aux left
  module right = efunctor-aux right
  open adjunction-εη areadj public
  open adjunction-εη-equats areadj public






-- via natural bijections between hom-setoids

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
    lr-natr : (A : ℂ.Obj){B B' : 𝔻.Obj}(b : || 𝔻.Hom B B' ||)(g : || 𝔻.Hom (L.ₒ A) B ||)
                 → lr.ap (b 𝔻.∘ g) ℂ.~ R.ₐ b ℂ.∘ lr.ap g
    rl-natl : (B : 𝔻.Obj){A A' : ℂ.Obj}(a : || ℂ.Hom A A' ||)(f : || ℂ.Hom A' (R.ₒ B) ||)
                 → rl.ap (f ℂ.∘ a) 𝔻.~ (rl.ap f) 𝔻.∘ L.ₐ a
    rl-natr : (A : ℂ.Obj){B B' : 𝔻.Obj}(b : || 𝔻.Hom B B' ||)(f : || ℂ.Hom A (R.ₒ B) ||)
                 → rl.ap (R.ₐ b ℂ.∘ f) 𝔻.~ b 𝔻.∘ rl.ap f







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
                            


module adjunction-as-universal-props {ℓₒ₁ ℓₐ₁ ℓ~₁}{ℂ : ecategoryₗₑᵥ ℓₒ₁ ℓₐ₁ ℓ~₁}
                                     {ℓₒ₂ ℓₐ₂ ℓ~₂}{𝔻 : ecategoryₗₑᵥ ℓₒ₂ ℓₐ₂ ℓ~₂}
                                     (L : efunctorₗₑᵥ ℂ 𝔻)(R : efunctorₗₑᵥ 𝔻 ℂ)
                                     where                 
  private
    module ℂ = ecat ℂ
    module 𝔻 = ecat 𝔻
    module L = efunctor-aux L
    module R = efunctor-aux R
    module RL = efunctor-aux (R ○ L)
    module LR = efunctor-aux (L ○ R)
    module ℂ↓R (A : ℂ.Obj) where
      open ecategory-aux (A ₒ↓ R) public
      open slice-funct-ecat R A public
      open initial-defs (A ₒ↓ R) public
    module L↓𝔻 (B : 𝔻.Obj) where
      open ecategory-aux (L ↓ₒ B) public
      open funct-slice-ecat L B public
      open terminal-defs (L ↓ₒ B) public

  -- currently adjunction-η and adjucntion-ε are defined using (co)reprentability of presheaves.
  -- here comma categories are used to avoid restrictions on universe levels
  
  RLar2slob : {A : ℂ.Obj}{B : 𝔻.Obj} → || ℂ.Hom A (R.ₒ B) || → ℂ↓R.Obj A
  RLar2slob {A} {B} f = record
    { R = B
    ; ar = f
    }
  LRar2slob : {A : ℂ.Obj}{B : 𝔻.Obj} → || 𝔻.Hom (L.ₒ A) B || → L↓𝔻.Obj B
  LRar2slob {A} {B} g = record
    { L = A
    ; ar = g
    }
  RLtr2slar : {A : ℂ.Obj}{B B' : 𝔻.Obj}{f : || ℂ.Hom A (R.ₒ B) ||}{f' : || ℂ.Hom A (R.ₒ B') ||}
              {b : || 𝔻.Hom B B' ||} → R.ₐ b ℂ.∘ f ℂ.~ f'
                → || ℂ↓R.Hom A (RLar2slob f) (RLar2slob f') ||
  RLtr2slar {b = b} tr = record
    { arR = b
    ; tr = tr
    }
  LRtr2slar : {A A' : ℂ.Obj}{B : 𝔻.Obj}{g : || 𝔻.Hom (L.ₒ A) B ||}{g' : || 𝔻.Hom (L.ₒ A') B ||}
              {a : || ℂ.Hom A A' ||} → g' 𝔻.∘ L.ₐ a 𝔻.~ g
                → || L↓𝔻.Hom B (LRar2slob g) (LRar2slob g') ||
  LRtr2slar {a = a} tr = record
    { arL = a
    ; tr = tr
    }
  RLnt2sl : natural-transformation IdF (R ○ L) → (A : ℂ.Obj) → ℂ↓R.Obj A
  RLnt2sl α A = RLar2slob (α.fnc {A})
              where module α = natural-transformation α
  LRnt2sl : natural-transformation (L ○ R) IdF → (B : 𝔻.Obj) → L↓𝔻.Obj B
  LRnt2sl β B = LRar2slob (β.fnc {B})
              where module β = natural-transformation β


  module unvη2adj (ηnt : natural-transformation IdF (R ○ L))
                  (ηin : (A : ℂ.Obj) → ℂ↓R.is-initial A (RLnt2sl ηnt A))
                  where
    private
      module η where
        open natural-transformation ηnt public
        cn : (A : ℂ.Obj) → ℂ↓R.Obj A
        cn A = RLnt2sl ηnt A
        module unv (A : ℂ.Obj) where
          open ℂ↓R.is-initial A (ηin A) renaming (ø to øar) public -- ; øuq to uq; øuqg to uqg
          uar : {B : 𝔻.Obj}(f : || ℂ.Hom A (R.ₒ B) ||)
                  → || 𝔻.Hom (L.ₒ A) B ||
          uar {B} f = ℂ↓R.ₐ.arR (øar (RLar2slob f))
          tr : {B : 𝔻.Obj}{f : || ℂ.Hom A (R.ₒ B) ||}
                  → R.ₐ (uar f) ℂ.∘ fnc ℂ.~ f
          tr {B} {f} = ℂ↓R.ₐ.tr (øar (RLar2slob f))

    εnt : natural-transformation (L ○ R) IdF
    εnt = record
      { fnc = fnc
      ; nat = λ {B} {B'} b → η.unv.øuqg (R.ₒ B) {RLar2slob (R.ₐ b)}
                                         {RLtr2slar (inv1 b)}
                                         {RLtr2slar (inv2 b)}
      }
      where fnc : {B : 𝔻.Obj} → || 𝔻.Hom (L.ₒ (R.ₒ B)) B ||
            fnc {B} = η.unv.uar (R.ₒ B) (ℂ.idar (R.ₒ B))
            tr : {B : 𝔻.Obj} → R.ₐ fnc ℂ.∘ η.fnc ℂ.~ ℂ.idar (R.ₒ B)
            tr {B} = η.unv.tr (R.ₒ B)
            inv1 : {B B' : 𝔻.Obj}(b : || 𝔻.Hom B B' ||)
                     → R.ₐ (fnc 𝔻.∘ L.ₐ (R.ₐ b)) ℂ.∘ η.fnc ℂ.~ R.ₐ b
            inv1 {B} {B'} b = ~proof
                            R.ₐ (fnc 𝔻.∘ LR.ₐ b) ℂ.∘ η.fnc      ~[ ∘e r R.∘ax-rfˢ ⊙ assˢ ] /
                            R.ₐ fnc ℂ.∘ RL.ₐ (R.ₐ b) ℂ.∘ η.fnc   ~[ ∘e (η.nat (R.ₐ b) ˢ) r ] /
                            R.ₐ fnc ℂ.∘ η.fnc ℂ.∘ R.ₐ b          ~[ ass ⊙ lidgg r tr ]∎
                            R.ₐ b ∎
                            where open ecategory-aux-only ℂ
            inv2 : {B B' : 𝔻.Obj}(b : || 𝔻.Hom B B' ||)
                     → R.ₐ (b 𝔻.∘ fnc) ℂ.∘ η.fnc ℂ.~ R.ₐ b
            inv2 {B} {B'} b = ~proof
                            R.ₐ (b 𝔻.∘ fnc) ℂ.∘ η.fnc     ~[ ∘e r R.∘ax-rfˢ ⊙ assˢ ] /
                            R.ₐ b ℂ.∘ R.ₐ fnc ℂ.∘ η.fnc    ~[ ridgg r tr ]∎
                            R.ₐ b ∎
                            where open ecategory-aux-only ℂ
    private module ε = natural-transformation εnt

    trid₁ : {A : ℂ.Obj} → ε.fnc 𝔻.∘ L.ₐ η.fnc 𝔻.~ 𝔻.idar (L.ₒ A)
    trid₁ {A} = η.unv.øuqg A
                           {f = RLtr2slar (~proof
                              R.ₐ (ε.fnc 𝔻.∘ L.ₐ η.fnc) ℂ.∘ η.fnc     ~[ ∘e r R.∘ax-rfˢ ⊙ assˢ ] /
                              R.ₐ ε.fnc ℂ.∘ RL.ₐ η.fnc ℂ.∘ η.fnc  ~[ ∘e (η.nat η.fnc ˢ) r ] /
                              R.ₐ ε.fnc ℂ.∘ η.fnc ℂ.∘ η.fnc   ~[ ass ⊙ lidgg r (η.unv.tr (R.ₒ (L.ₒ A))) ]∎
                              η.fnc ∎)}
                           {RLtr2slar (lidgg r R.id)}
              where open ecategory-aux-only ℂ
    trid₂ : {B : 𝔻.Obj} → R.ₐ ε.fnc ℂ.∘ η.fnc ℂ.~ ℂ.idar (R.ₒ B)
    trid₂ {B} = η.unv.tr (R.ₒ B)
  -- end unvη2adj


  module unvε2adj (εnt : natural-transformation (L ○ R) IdF)
                  (εtm : (B : 𝔻.Obj) → L↓𝔻.is-terminal B (LRnt2sl εnt B))
                  where
    private
      module ε where
        open natural-transformation εnt public
        cn : (B : 𝔻.Obj) → L↓𝔻.Obj B
        cn B = LRnt2sl εnt B
        module unv (B : 𝔻.Obj) where
          open L↓𝔻.is-terminal B (εtm B) renaming (! to !ar; !uniq to !uq) public -- ; !uqg to uqg
          uar : {A : ℂ.Obj}(g : || 𝔻.Hom (L.ₒ A) B ||)
                  → || ℂ.Hom A (R.ₒ B) ||
          uar {A} g = L↓𝔻.ₐ.arL (!ar (LRar2slob g))
          tr : {A : ℂ.Obj}{g : || 𝔻.Hom (L.ₒ A) B ||}
                  → fnc 𝔻.∘ L.ₐ (uar g) 𝔻.~ g
          tr {A} {g} = L↓𝔻.ₐ.tr (!ar (LRar2slob g))

    ηnt : natural-transformation IdF (R ○ L)
    ηnt = record
      { fnc = fnc
      ; nat = λ {A'} {A} a → ε.unv.!uqg (L.ₒ A) {LRar2slob (L.ₐ a)}
                                         {LRtr2slar (inv2 a)}
                                         {LRtr2slar (inv1 a)}
      }
      where fnc : {A : ℂ.Obj} → || ℂ.Hom A (R.ₒ (L.ₒ A)) ||
            fnc {A} = ε.unv.uar (L.ₒ A) (𝔻.idar (L.ₒ A))
            tr : {A : ℂ.Obj} → ε.fnc 𝔻.∘ L.ₐ fnc 𝔻.~ 𝔻.idar (L.ₒ A)
            tr {A} = ε.unv.tr (L.ₒ A)
            inv1 : {A' A : ℂ.Obj}(a : || ℂ.Hom A' A ||)
                     → ε.fnc 𝔻.∘ L.ₐ (RL.ₐ a ℂ.∘ fnc) 𝔻.~ L.ₐ a
            inv1 {A'} {A} a = ~proof
                 ε.fnc 𝔻.∘ L.ₐ (RL.ₐ a ℂ.∘ fnc)         ~[ ∘e L.∘ax-rfˢ r ] /
                 ε.fnc 𝔻.∘ LR.ₐ (L.ₐ a) 𝔻.∘ L.ₐ fnc     ~[ ass ⊙ ∘e r (ε.nat (L.ₐ a)) ⊙ assˢ ] /
                 L.ₐ a 𝔻.∘ ε.fnc 𝔻.∘ L.ₐ fnc            ~[ ridgg r tr ]∎
                 L.ₐ a ∎
                            where open ecategory-aux-only 𝔻
            inv2 : {A' A : ℂ.Obj}(a : || ℂ.Hom A' A ||)
                     → ε.fnc 𝔻.∘ L.ₐ (fnc ℂ.∘ a) 𝔻.~ L.ₐ a
            inv2 {A'} {A} a = ~proof
                            ε.fnc 𝔻.∘ L.ₐ (fnc ℂ.∘ a)      ~[ ∘e L.∘ax-rfˢ r ] /
                            ε.fnc 𝔻.∘ L.ₐ fnc 𝔻.∘ L.ₐ a    ~[ ass ⊙ lidgg r tr ]∎
                            L.ₐ a ∎
                            where open ecategory-aux-only 𝔻
    private module η = natural-transformation ηnt

    trid₁ : {A : ℂ.Obj} → ε.fnc 𝔻.∘ L.ₐ η.fnc 𝔻.~ 𝔻.idar (L.ₒ A)
    trid₁ {A} = ε.unv.tr (L.ₒ A)
    trid₂ : {B : 𝔻.Obj} → R.ₐ ε.fnc ℂ.∘ η.fnc ℂ.~ ℂ.idar (R.ₒ B)
    trid₂ {B} = ε.unv.!uqg B {LRnt2sl εnt B}
                             {LRtr2slar (~proof
              ε.fnc 𝔻.∘ L.ₐ (R.ₐ ε.fnc ℂ.∘ η.fnc)  ~[ ∘e L.∘ax-rfˢ r ] /
              ε.fnc 𝔻.∘ LR.ₐ ε.fnc 𝔻.∘ L.ₐ η.fnc  ~[ ass ⊙ (∘e r (ε.nat ε.fnc) ⊙ assˢ) ] /
              ε.fnc 𝔻.∘ ε.fnc 𝔻.∘ L.ₐ η.fnc       ~[ ridgg r (ε.unv.tr (LR.ₒ B)) ]∎
              ε.fnc ∎)}
                             {LRtr2slar (ridgg r L.id)}
              where open ecategory-aux-only 𝔻
  -- end unvη2adj

  unvη→adj : (ηnt : natural-transformation IdF (R ○ L))
              (ηin : (A : ℂ.Obj) → ℂ↓R.is-initial A (RLnt2sl ηnt A))
                   → adjunction-εη L R
  unvη→adj ηnt ηin = record
    { ηnt = ηnt
    ; εnt = εnt
    ; trid₁ = trid₁
    ; trid₂ = trid₂
    }
    where open unvη2adj ηnt ηin
  
  unvε→adj : (εnt : natural-transformation (L ○ R) IdF)
              (εtm : (B : 𝔻.Obj) → L↓𝔻.is-terminal B (LRnt2sl εnt B))
                   → adjunction-εη L R
  unvε→adj εnt εtm = record
    { ηnt = ηnt
    ; εnt = εnt
    ; trid₁ = trid₁
    ; trid₂ = trid₂
    }
    where open unvε2adj εnt εtm


  module adj2unv (adj : adjunction-εη L R) where
    open adjunction-εη adj
    open adjunction-εη-equats adj
    private
      module η = natural-transformation ηnt
      module ε = natural-transformation εnt

    η-initial : (A : ℂ.Obj) → ℂ↓R.is-initial A (RLnt2sl ηnt A)
    η-initial A = record
      { ø = λ ff → RLtr2slar {A} {b = ε.fnc 𝔻.∘ L.ₐ (ℂ↓R.ₒ.ar ff)}
                             (ℂx.∘e ℂx.r R.∘ax-rfˢ ℂx.⊙ ℂx.assˢ ℂx.⊙ trid₂g (ℂ↓R.ₒ.ar ff))
      ; øuq = λ {ff} a → ~proof
            ℂ↓R.ₐ.arR a                                        ~[ trid₁g (ℂ↓R.ₐ.arR a) ˢ ] /
            ε.fnc 𝔻.∘ LR.ₐ (ℂ↓R.ₐ.arR a) 𝔻.∘ L.ₐ ηnt.fnc      ~[ ∘e (L.∘ax (ℂ↓R.ₐ.tr a)) r ]∎
            ε.fnc 𝔻.∘ L.ₐ (ℂ↓R.ₒ.ar ff) ∎
      }
      where open ecategory-aux-only 𝔻
            module ℂx = ecategory-aux-only ℂ

    ε-terminal : (B : 𝔻.Obj) → L↓𝔻.is-terminal B (LRnt2sl εnt B)
    ε-terminal B = record
      { ! = λ gg → LRtr2slar {a = R.ₐ (L↓𝔻.ₒ.ar gg) ℂ.∘ η.fnc}
                              (𝔻x.∘e L.∘ax-rfˢ 𝔻x.r 𝔻x.⊙ trid₁g (L↓𝔻.ₒ.ar gg))
      ; !uniq = λ {gg} b → ~proof
              L↓𝔻.ₐ.arL b                                 ~[ trid₂g (L↓𝔻.ₐ.arL b) ˢ ] /
              R.ₐ ε.fnc ℂ.∘ RL.ₐ (L↓𝔻.ₐ.arL b) ℂ.∘ η.fnc   ~[ ass ⊙ ∘e r (R.∘ax (L↓𝔻.ₐ.tr b)) ]∎
              R.ₐ (L↓𝔻.ₒ.ar gg) ℂ.∘ η.fnc ∎
      }
      where open ecategory-aux-only ℂ
            module 𝔻x = ecategory-aux-only 𝔻
  -- end adj2unv

  

  module adj-bij2unv (adj : adjunction-bij L R) where
    open adjunction-bij adj
    open adjunction-bij-equat adj
    private
      module η = natural-transformation ηnt
      module ε = natural-transformation εnt

    η-initial : (A : ℂ.Obj) → ℂ↓R.is-initial A (RLnt2sl ηnt A)
    η-initial A = record
      { ø = λ f → record
          { arR = rl.ap (ℂ↓R.ₒ.ar f)
          ; tr = ηeq (rl.ap (ℂ↓R.ₒ.ar f)) ℂx.⊙ idcod (ℂ↓R.ₒ.ar f)
          }
      ; øuq = λ {f} g → ~proof ℂ↓R.ₐ.arR g                               ~[ iddom (ℂ↓R.ₐ.arR g) ˢ ] /
                                rl.ap (lr.ap (ℂ↓R.ₐ.arR g))              ~[ rl.ext (ηeq (ℂ↓R.ₐ.arR g)) ˢ ] /
                                rl.ap (R.ₐ (ℂ↓R.ₐ.arR g) ℂ.∘ η.fnc {A}) ~[ rl.ext (ℂ↓R.ₐ.tr g) ]∎
                                rl.ap (ℂ↓R.ₒ.ar f) ∎
      }
      where module ℂx = ecategory-aux-only ℂ
            open ecategory-aux-only 𝔻

    ε-terminal : (B : 𝔻.Obj) → L↓𝔻.is-terminal B (LRnt2sl εnt B)
    ε-terminal B = record
      { ! = λ g → record
          { arL = lr.ap (L↓𝔻.ₒ.ar g)
          ; tr = εeq (lr.ap (L↓𝔻.ₒ.ar g)) 𝔻x.⊙ iddom (L↓𝔻.ₒ.ar g)
          }
      ; !uniq = λ {g} f → ~proof L↓𝔻.ₐ.arL f                  ~[ idcod (L↓𝔻.ₐ.arL f) ˢ ] /
                                  lr.ap (rl.ap (L↓𝔻.ₐ.arL f))  ~[ lr.ext (εeq (L↓𝔻.ₐ.arL f)) ˢ ] /
                                  lr.ap (ε.fnc 𝔻.∘ L.ₐ (L↓𝔻.ₐ.arL f)) ~[ lr.ext (L↓𝔻.ₐ.tr f) ]∎
                                  lr.ap (L↓𝔻.ₒ.ar g) ∎
      }
      where open ecategory-aux-only ℂ
            module 𝔻x = ecategory-aux-only 𝔻
  -- end adj-bij2unv
-- end adjunction-as-universal-props



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

-- Here I'd like to go through representability of (co)presheaves,
-- so we need to restrict to adjunctions between categories
-- with hom-sets at the same universe level.

-- Otherwise, use the defintion of category of elements as a slice over/under a functor
-- (no need to restrict to presheaves here), and prove the (co)unit initial/terminal there.
-- See above.

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
