
{-# OPTIONS --without-K #-}

module ecats.concr-ecats.adjunctions-Cat-Std where

open import tt-basics.basics
open import tt-basics.setoids renaming (||_|| to ||_||std)
open import ecats.basic-defs.ecat-def&not
open import ecats.basic-defs.preorder
open import ecats.isomorphism
open import ecats.functors.defs.efunctor-d&n
open import ecats.functors.defs.natural-transformation
open import ecats.functors.defs.natural-iso
open import ecats.functors.defs.adjunction
open import ecats.functors.defs.basic-defs
open import ecats.functors.props.efunctor
open import ecats.concr-ecats.ecat-ecats
open import ecats.concr-ecats.Type-lev
open import ecats.concr-ecats.Std-lev


-----------------------------------------------------------------------
-- The obvious "functor" from Cat to Type is not extensional
-----------------------------------------------------------------------
{-
attempt : efunctor Cat Type
attempt = record
  { FObj = ecat.Obj
  ; FHom = efctr.ₒ
  ; isF = record
        { ext = λ {f = F} {F'} natiso → {!!} -- it's just FX ≅ F'X, not FX == F'X as required.
        ; id = λ {ℂ} X → =rf
        ; cmp = λ F G X → =rf
        }
  }
-}


-- From ecategories to setoids

module obj-up-to-iso {ℓ₁ ℓ₂ ℓ₃ : Level}(ℂ : ecategoryₗₑᵥ ℓ₁ ℓ₂ ℓ₃) where
  private
    module ℂ where
       open ecat ℂ public
       open iso-d&p ℂ public
  Obj/≅ₒ : setoid {ℓ₁} {ℓ₂ ⊔ ℓ₃}
  Obj/≅ₒ = record
         { object = ℂ.Obj
         ; _∼_ = λ X Y → X ℂ.≅ₒ Y
         ; istteqrel = record
                     { refl = ℂ.≅ₒrefl
                     ; sym = ℂ.≅ₒsym
                     ; tra = ℂ.≅ₒtra
                     }
         }
  module Obj/≅ₒ = setoid-aux Obj/≅ₒ
-- end obj-up-to-iso

module efctrs-are-ext {ℓ₁ₒ ℓ₁ₐ ℓ₁~}{ℂ : ecategoryₗₑᵥ ℓ₁ₒ ℓ₁ₐ ℓ₁~}
                      {ℓ₂ₒ ℓ₂ₐ ℓ₂~}{𝔻 : ecategoryₗₑᵥ ℓ₂ₒ ℓ₂ₐ ℓ₂~}
                      (F : efunctorₗₑᵥ ℂ 𝔻)
                      where
  private
    module ℂ where
      open ecat ℂ public
      open iso-d&p ℂ public
    module 𝔻 where
      open ecat 𝔻 public
      open iso-d&p 𝔻 public
    module F where
      open efctr F public
      open efunctor-lev-props F public
  open obj-up-to-iso
  ₒ/≅ₒ : setoidmap (Obj/≅ₒ ℂ) (Obj/≅ₒ 𝔻)
  ₒ/≅ₒ = record
    { op = F.ₒ
    ; ext = F.pres≅ₒ
    }
-- end efctrs-are-ext

module making-efctrs-ext-is-ext {ℓ₁ₒ ℓ₁ₐ ℓ₁~}{ℂ : ecategoryₗₑᵥ ℓ₁ₒ ℓ₁ₐ ℓ₁~}
                                {ℓ₂ₒ ℓ₂ₐ ℓ₂~}{𝔻 : ecategoryₗₑᵥ ℓ₂ₒ ℓ₂ₐ ℓ₂~}
                                {F G : efunctorₗₑᵥ ℂ 𝔻}(natiso : F ≅ₐ G)
                                where
  private
    module ℂ where
      open ecat ℂ public
      open iso-d&p ℂ public
    module 𝔻 where
      open ecat 𝔻 public
      open iso-d&p 𝔻 public
    module F where
      open efctr F public
      open efunctor-lev-props F public
    module G where
      open efctr G public
      open efunctor-lev-props G public
    module F≅G = natural-iso natiso
  ≅ptw : (X : ℂ.Obj) → F.ₒ X 𝔻.≅ₒ G.ₒ X
  ≅ptw X = record
    { a12 = F≅G.fnc
    ; a21 = F≅G.fnc⁻¹
    ; isop = F≅G.isiso
    }
-- end making-efctrs-ext-is-ext


--------------------------------------------------------------
-- Objects functor from categories to setoids, at every level
--------------------------------------------------------------

Ob/≅ₒ : (ℓₒ ℓₐ ℓ~ : Level) → efunctor (CATₗₑᵥ ℓₒ ℓₐ ℓ~) (Stdₗₑᵥ ℓₒ (ℓₐ ⊔ ℓ~))
Ob/≅ₒ ℓₒ ℓₐ ℓ~ = record
  { FObj = Obj/≅ₒ
  ; FHom = ₒ/≅ₒ
  ; isF = record
        { ext = ≅ptw
        ; id = λ {ℂ} X → Obj/≅ₒ.r ℂ {X}
        ; cmp = λ {ℂ} {𝔻} {𝔼} F G X → Obj/≅ₒ.r 𝔼 {_}
        }
  }
  where open obj-up-to-iso
        open efctrs-are-ext
        open making-efctrs-ext-is-ext



-- From setoid to ecategories

Disc-ecat : {ℓₒ ℓᵣ : Level} → setoid {ℓₒ} {ℓᵣ} → ecategoryₗₑᵥ ℓₒ ℓᵣ 0ₗₑᵥ
Disc-ecat A = record
  { Obj = || A ||std
  ; Hom = λ a b → codisc-std (a A.~ b)
  ; isecat = record
               { _∘_ = λ g f → A.tra f g
               ; idar = A.refl
               ; ∘ext = λ _ _ _ _ _ _ → 0₁
               ; lidax = λ _ → 0₁
               ; ridax = λ _ → 0₁
               ; assoc = λ _ _ _ → 0₁
               }
  }
  where module A where
          open setoid A public
          open setoid-aux A public

Disc-is-preord : {ℓₒ ℓᵣ : Level}(A : setoid {ℓₒ} {ℓᵣ}) → is-preorder (Disc-ecat A)
Disc-is-preord A = record { pf = 0₁ }

Disc-map : {ℓₒ₁ ℓᵣ₁ : Level}{A : setoid {ℓₒ₁} {ℓᵣ₁}}{ℓₒ₂ ℓᵣ₂ : Level}{B : setoid {ℓₒ₂} {ℓᵣ₂}}
                → setoidmap A B → efunctorₗₑᵥ (Disc-ecat A) (Disc-ecat B)
Disc-map {A = A} {B = B} f = record
  { FObj = f.op
  ; FHom = f.ext
  ; isF = record
        { ext = λ _ → 0₁
        ; id = λ {_} → 0₁
        ; cmp = λ _ _ → 0₁
        }
  }
  where module f = setoidmap f

module Disc-is-functorial (ℓₒ ℓᵣ : Level) where
  private
    module CAT = ecat (CATₗₑᵥ ℓₒ ℓᵣ 0ₗₑᵥ)
    module Std = ecat (Stdₗₑᵥ ℓₒ ℓᵣ)

  ext : {A B : Std.Obj}{f f' : || Std.Hom A B ||}
           → f Std.~ f' → (Disc-map f) CAT.~ (Disc-map f')
  ext {A} {B} {f} {f'} eq = record
    { natt = record { fnc = λ {X} → eq X ; nat = λ _ → 0₁ }
    ; natt⁻¹ = record { fnc = λ {X} → eq X B.ˢ ; nat = λ _ → 0₁ }
    ; isiso = record { iddom = 0₁ ; idcod = 0₁ }
    }
    where module A where
            open setoid A public
            open setoid-aux A public
          module B where
            open setoid B public
            open setoid-aux B public
          module f = setoidmap f

  idax : {A : Std.Obj} → Disc-map (Std.idar A) ≅ₐ CAT.idar (Disc-ecat A)
  idax {A} = record
    { natt = record { fnc = A.r ; nat = λ _ → 0₁ }
    ; natt⁻¹ = record { fnc = A.r ; nat = λ _ → 0₁ }
    ; isiso = record { iddom = 0₁ ; idcod = 0₁ }
    }
    where module A where
            open setoid A public
            open setoid-aux A public

  cmpax : {A B C : Std.Obj}(f : || Std.Hom A B ||)(g : || Std.Hom B C ||)
             → (Disc-map g) CAT.∘ (Disc-map f) CAT.~ Disc-map (g Std.∘ f)
  cmpax {A} {B} {C} f g = record
    { natt = record { fnc = C.r ; nat = λ _ → 0₁ }
    ; natt⁻¹ = record { fnc = C.r ; nat = λ _ → 0₁ }
    ; isiso = record { iddom = 0₁ ; idcod = 0₁ }
    }
    where module C where
            open setoid C public
            open setoid-aux C public
-- end Disc-is-functorial


---------------------------------------------------------------
-- Discrete functor from setoids to categories, at every level
---------------------------------------------------------------

DiscCat : (ℓₒ ℓᵣ : Level) → efunctor (Stdₗₑᵥ ℓₒ ℓᵣ) (CATₗₑᵥ ℓₒ ℓᵣ 0ₗₑᵥ)
DiscCat ℓₒ ℓᵣ = record
  { FObj = Disc-ecat
  ; FHom = Disc-map
  ; isF = record
        -- implicit are explicit because of symmetry
        { ext = λ {A} {B} → ext {A} {B}
        ; id = λ {A} → idax {A}
        ; cmp = cmpax
        }
  }
  where open Disc-is-functorial ℓₒ ℓᵣ


module dicrete-adjunction (ℓₒ ℓₐ : Level) where
  private
    module CAT = ecat (CATₗₑᵥ ℓₒ ℓₐ 0ₗₑᵥ)
    module Std = ecat (Stdₗₑᵥ ℓₒ ℓₐ)
    module Δ = efctr (DiscCat ℓₒ ℓₐ)
    module U = efctr (Ob/≅ₒ ℓₒ ℓₐ 0ₗₑᵥ)

  module ~isiso (A : Std.Obj) where
    private
      module A where
        open setoid A public
        open setoid-aux A public
      module ΔA where
        open ecat (Δ.ₒ A) public
        open iso-d&p (Δ.ₒ A) public
    ~isiso : {a b : || A ||std} → a A.~ b → a ΔA.≅ₒ b
    ~isiso eq = record
      { a12 = eq
      ; a21 = eq A.ˢ
      ; isop = record { iddom = 0₁ ; idcod = 0₁ }
      }
  -- end ~isiso
  open ~isiso

  module lr (A : Std.Obj)(ℂ : CAT.Obj)(F : efunctor (Δ.ₒ A) ℂ) where
    private
      module F where
        open efctr F public
        open efunctor-lev-props F public
    ar : || Std.Hom A (U.ₒ ℂ) ||std
    ar = record
       { op = F.ₒ
       ; ext = λ eq → F.pres≅ₒ (~isiso A eq)
       }
  -- end lr
  lr : (A : Std.Obj)(ℂ : CAT.Obj) → setoidmap (CAT.Hom (Δ.ₒ A) ℂ) (Std.Hom A (U.ₒ ℂ))
  lr A ℂ = record
    { op = ar
    ; ext = λ natiso a → ≅ₐ2≅ₒ natiso {a}
    }
    where open lr A ℂ

  module rl (A : Std.Obj)(ℂ : CAT.Obj)(g : setoidmap A (U.ₒ ℂ)) where
    private
      module A where
        open setoid A public
        open setoid-aux A public
      {-module Uℂ where
        open setoid (U.ₒ ℂ) public
        open setoid-aux (U.ₒ ℂ) public
      module ΔA where
        open ecat (Δ.ₒ A) public
        open iso-d&p (Δ.ₒ A) public-}
      module ℂ where
        open ecat ℂ public
        open iso-d&p ℂ public
      module g where
        open setoidmap g public
        module ext {a b : || A ||std}(eq : a A.~ b) = ℂ._≅ₒ_ (ext eq)
      
    ar : || CAT.Hom (Δ.ₒ A) ℂ ||
    ar = record
      { FObj = g.op
      ; FHom = λ eq → g.ext.a21 A.r ℂ.∘ g.ext.a12 eq
      ; isF = record
            -- not extensional because the setoid on arrows is not free..?
            { ext = {!!}
            ; id = g.ext.iddom A.r
            -- not split either? Here freeness doesn't help...
            ; cmp = {!!}
            }
      }
  -- end rl
  rl : (A : Std.Obj)(ℂ : CAT.Obj) → setoidmap (Std.Hom A (U.ₒ ℂ)) (CAT.Hom (Δ.ₒ A) ℂ)
  rl A ℂ = record
    { op = {!!}
    ; ext = {!!}
    }
    where 

-- end dicrete-adjunction

DiscAdj : (ℓₒ ℓₐ : Level) → adjunction-bij (DiscCat ℓₒ ℓₐ) (Ob/≅ₒ ℓₒ ℓₐ 0ₗₑᵥ)
DiscAdj ℓₒ ℓₐ = record
                  { lr = lr
                  ; rl = {!!}
                  ; isbij = {!!}
                  ; lr-natl = {!!}
                  ; lr-natr = {!!}
                  ; rl-natl = {!!}
                  ; rl-natr = {!!}
                  }
                  where open dicrete-adjunction ℓₒ ℓₐ


{-
module (ℓₒ ℓₐ ℓ~ : Level) where
  private
    module CAT = ecat (CATₗₑᵥ ℓₒ ℓₐ ℓ~)
    module Std = ecat (Stdₗₑᵥ ℓₒ (ℓₐ ⊔ ℓ~))
    module O/≅ = efctr (Ob/≅ₒ  ℓₒ ℓₐ ℓ~)
    module ecat&iso (𝕏 : CAT.Obj) where
      open ecat 𝕏 public
      open iso-d&p 𝕏 public

  module {𝔸 𝔹 : CAT.Obj}{F G : || CAT.Hom 𝔸 𝔹 ||}(eq : O/≅.ₐ F Std.~ O/≅.ₐ G) where
    private
      module 𝔸 = ecat&iso 𝔸
      module 𝔹 = ecat&iso 𝔹
      module F = efctr F
      module G = efctr G
      module eq (X : 𝔸.Obj) = 𝔹._≅ₒ_ (eq X)
-}








{-
module Setoid-of-arrows {ℓ₁ ℓ₂ ℓ₃ : Level}(ℂ : ecategoryₗₑᵥ ℓ₁ ℓ₂ ℓ₃) where
  private module ℂ = ecat ℂ

  Arr-ty : Set (ℓ₁ ⊔ ℓ₂)
  Arr-ty = Σ (prod ℂ.Obj ℂ.Obj) (λ XY → || ℂ.Hom (prj1 XY) (prj2 XY) ||)

  Arr-eq : Arr-ty → Arr-ty → Set 
  Arr-eq u u' = {!!}

  Arr : setoid {ℓ₁ ⊔ ℓ₂}
  Arr = record
      { object = Arr-ty
      ; _∼_ = {!!}
      ; istteqrel = {!!}
      }

-- end Setoid-of-arrows
-}
