{-# OPTIONS --without-K #-}

module ecats.constructions.comma-ecat where

open import tt-basics.basics using (prod; pair)
open import tt-basics.setoids hiding (||_||)
open import ecats.basic-defs.ecat-def&not
open import ecats.functors.defs.efunctor-d&n
open import ecats.functors.defs.natural-transformation


module comma-ecat-defs {ℓₒl ℓₐl ℓ~l}{𝕃 : ecategoryₗₑᵥ ℓₒl ℓₐl ℓ~l}{ℓₒc ℓₐc ℓ~c}
                       {ℂ : ecategoryₗₑᵥ ℓₒc ℓₐc ℓ~c}{ℓₒr ℓₐr ℓ~r}{ℝ : ecategoryₗₑᵥ ℓₒr ℓₐr ℓ~r}
                       (F : efunctorₗₑᵥ 𝕃 ℂ)(G : efunctorₗₑᵥ ℝ ℂ)
                       where
  private
    module 𝕃 = ecategory-aux 𝕃
    module ℂ = ecategory-aux ℂ
    module ℝ = ecategory-aux ℝ
    module F = efunctor-aux F
    module G = efunctor-aux G

  record ↓Obj : Set (𝕃.ℓₒ ⊔ ℝ.ℓₒ ⊔ ℂ.ℓₐᵣᵣ) where
    field
      L : 𝕃.Obj
      R : ℝ.Obj
      ar : || ℂ.Hom (F.ₒ L) (G.ₒ R) ||

  record ||↓Hom|| (A B : ↓Obj) : Set (𝕃.ℓₐᵣᵣ ⊔ ℝ.ℓₐᵣᵣ ⊔ ℂ.ℓ~) where
    private
      module A = ↓Obj A
      module B = ↓Obj B
    field
      arL : || 𝕃.Hom A.L B.L ||
      arR : || ℝ.Hom A.R B.R ||
      sq : B.ar ℂ.∘ F.ₐ arL ℂ.~ G.ₐ arR ℂ.∘ A.ar

  frgt-sq : {A B : ↓Obj} → ||↓Hom|| A B
               → prod || 𝕃.Hom (↓Obj.L A) (↓Obj.L B) || || ℝ.Hom (↓Obj.R A) (↓Obj.R B) ||
  frgt-sq f = pair f.arL f.arR
            where module f = ||↓Hom|| f
      
  ↓Hom : ↓Obj → ↓Obj → setoid {𝕃.ℓₐᵣᵣ ⊔ ℝ.ℓₐᵣᵣ ⊔ ℂ.ℓ~} {𝕃.ℓ~ ⊔ ℝ.ℓ~} -- ⊔ ℓ₄
  ↓Hom A B = sub-setoid (prod-std (𝕃.Hom A.L B.L) (ℝ.Hom A.R B.R))
                        (frgt-sq {A} {B})
    where module A = ↓Obj A
          module B = ↓Obj B

  ↓idar : (A : ↓Obj) → || ↓Hom A A ||
  ↓idar A = record
    { arL = 𝕃.idar A.L
    ; arR = ℝ.idar A.R
    ; sq = ~proof A.ar ℂ.∘ F.ₐ (𝕃.idar A.L)   ~[ ∘e F.id r ] /
                  A.ar ℂ.∘ ℂ.idar (F.ₒ A.L)    ~[ ridgen lidˢ ] /
                  ℂ.idar (G.ₒ A.R) ℂ.∘ A.ar    ~[ ∘e r (G.id ˢ) ]∎
                  G.ₐ (ℝ.idar A.R) ℂ.∘ A.ar ∎
    }
    where open ecategory-aux-only ℂ
          module A = ↓Obj A
  
  ↓cmp : {A B C : ↓Obj} → || ↓Hom B C || → || ↓Hom A B || → || ↓Hom A C ||
  ↓cmp {A} {B} {C} g f = record
    { arL = g.arL 𝕃.∘ f.arL
    ; arR = g.arR ℝ.∘ f.arR
    ; sq = ~proof C.ar ℂ.∘ F.ₐ (g.arL 𝕃.∘ f.arL)     ~[ ∘e (F.cmpˢ _ _) r ] /
                  C.ar ℂ.∘ F.ₐ g.arL ℂ.∘ F.ₐ f.arL    ~[ ass ⊙ ∘e r g.sq ⊙ assˢ ] /
                  G.ₐ g.arR ℂ.∘ B.ar ℂ.∘ F.ₐ f.arL    ~[ ∘e f.sq r ] /
                  G.ₐ g.arR ℂ.∘ G.ₐ f.arR ℂ.∘ A.ar    ~[ ass ⊙ ∘e r (G.cmp _ _) ]∎
                  G.ₐ (g.arR ℝ.∘ f.arR) ℂ.∘ A.ar ∎
    }
    where open ecategory-aux-only ℂ
          module A = ↓Obj A
          module B = ↓Obj B
          module C = ↓Obj C
          module f = ||↓Hom|| f
          module g = ||↓Hom|| g

  ↓cmp-ext : {A B C : ↓Obj}(f f' : || ↓Hom A B ||) (g g' : || ↓Hom B C ||)
                → < ↓Hom A B > f ~ f' → < ↓Hom B C > g ~ g'
                  → < ↓Hom A C > ↓cmp g f ~ ↓cmp g' f'
  ↓cmp-ext {A} {B} {C} f f' g g' eqf eqg =
                       pair (𝕃.∘e (prod-stdeq.₁ (𝕃.Hom A.L B.L) (ℝ.Hom A.R B.R)
                                                {frgt-sq f} {frgt-sq f'} eqf)
                                   (prod-stdeq.₁ (𝕃.Hom B.L C.L) (ℝ.Hom B.R C.R)
                                                {frgt-sq g} {frgt-sq g'} eqg))
                            (ℝ.∘e (prod-stdeq.₂ (𝕃.Hom A.L B.L) (ℝ.Hom A.R B.R)
                                                {frgt-sq f} {frgt-sq f'} eqf)
                                   (prod-stdeq.₂ (𝕃.Hom B.L C.L) (ℝ.Hom B.R C.R)
                                                 {frgt-sq g} {frgt-sq g'} eqg))
                                         where module A = ↓Obj A
                                               module B = ↓Obj B
                                               module C = ↓Obj C          
-- end comma-ecat-defs


comma-ecat : {ℓₒl ℓₐl ℓ~l : Level}{𝕃 : ecategoryₗₑᵥ ℓₒl ℓₐl ℓ~l}{ℓₒc ℓₐc ℓ~c : Level}
             {ℂ : ecategoryₗₑᵥ ℓₒc ℓₐc ℓ~c}{ℓₒr ℓₐr ℓ~r : Level}{ℝ : ecategoryₗₑᵥ ℓₒr ℓₐr ℓ~r}
             (F : efunctorₗₑᵥ 𝕃 ℂ)(G : efunctorₗₑᵥ ℝ ℂ)
             → ecategoryₗₑᵥ (ecat.ℓₒ 𝕃 ⊔ ecat.ℓₒ ℝ ⊔ ecat.ℓₐᵣᵣ ℂ)
                            (ecat.ℓₐᵣᵣ 𝕃 ⊔ ecat.ℓₐᵣᵣ ℝ ⊔ ecat.ℓ~ ℂ)
                            (ecat.ℓ~ 𝕃 ⊔ ecat.ℓ~ ℝ)
comma-ecat {𝕃 = 𝕃} {ℂ = ℂ} {ℝ = ℝ} F G = record
  { Obj = ↓Obj
  ; Hom = ↓Hom
  ; isecat = record
           { _∘_ = ↓cmp
           ; idar = ↓idar
           ; ∘ext = ↓cmp-ext
           ; lidax = λ f → pair 𝕃.lid ℝ.lid
           ; ridax = λ f → pair 𝕃.rid ℝ.rid
           ; assoc = λ f g h → pair 𝕃.ass ℝ.ass
           }
  }
  where open comma-ecat-defs F G
        module 𝕃 = ecategory-aux 𝕃
        module ℂ = ecategory-aux ℂ
        module ℝ = ecategory-aux ℝ
        module F = efunctor-aux F
        module G = efunctor-aux G


infix 2 _↓_
_↓_ : {ℓₒl ℓₐl ℓ~l : Level}{𝕃 : ecategoryₗₑᵥ ℓₒl ℓₐl ℓ~l}{ℓₒc ℓₐc ℓ~c : Level}
      {ℂ : ecategoryₗₑᵥ ℓₒc ℓₐc ℓ~c}{ℓₒr ℓₐr ℓ~r : Level}{ℝ : ecategoryₗₑᵥ ℓₒr ℓₐr ℓ~r}
      (F : efunctorₗₑᵥ 𝕃 ℂ)(G : efunctorₗₑᵥ ℝ ℂ)
          → ecategoryₗₑᵥ (ecat.ℓₒ 𝕃 ⊔ ecat.ℓₒ ℝ ⊔ ecat.ℓₐᵣᵣ ℂ)
                         (ecat.ℓₐᵣᵣ 𝕃 ⊔ ecat.ℓₐᵣᵣ ℝ ⊔ ecat.ℓ~ ℂ)
                         (ecat.ℓ~ 𝕃 ⊔ ecat.ℓ~ ℝ)
F ↓ G = comma-ecat F G

module comma-ecat {ℓₒl ℓₐl ℓ~l : Level}{𝕃 : ecategoryₗₑᵥ ℓₒl ℓₐl ℓ~l}{ℓₒc ℓₐc ℓ~c : Level}
                  {ℂ : ecategoryₗₑᵥ ℓₒc ℓₐc ℓ~c}{ℓₒr ℓₐr ℓ~r : Level}{ℝ : ecategoryₗₑᵥ ℓₒr ℓₐr ℓ~r}
                  (F : efunctorₗₑᵥ 𝕃 ℂ)(G : efunctorₗₑᵥ ℝ ℂ)
                  where
  private
    module 𝕃 = ecategory-aux 𝕃
    module ℂ = ecategory-aux ℂ
    module ℝ = ecategory-aux ℝ
  open ecat (F ↓ G) using (Obj)
  open comma-ecat-defs F G
  module ₒ = ↓Obj
  module ₐ {A B : Obj} = ||↓Hom|| {A} {B}
  module ~ {A B : Obj}{f f' : ||↓Hom|| A B}
           = prod-stdeq (𝕃.Hom (ₒ.L A) (ₒ.L B)) (ℝ.Hom (ₒ.R A) (ₒ.R B)) {frgt-sq f} {frgt-sq f'}
           renaming (₁ to ₗ; ₂ to ᵣ)


-- forgetful functors

↓left comma-left : {ℓₒl ℓₐl ℓ~l : Level}{𝕃 : ecategoryₗₑᵥ ℓₒl ℓₐl ℓ~l}{ℓₒc ℓₐc ℓ~c : Level}
                   {ℂ : ecategoryₗₑᵥ ℓₒc ℓₐc ℓ~c}{ℓₒr ℓₐr ℓ~r : Level}{ℝ : ecategoryₗₑᵥ ℓₒr ℓₐr ℓ~r}
                   (F : efunctorₗₑᵥ 𝕃 ℂ)(G : efunctorₗₑᵥ ℝ ℂ)
                     → efunctorₗₑᵥ (F ↓ G) 𝕃
comma-left {𝕃 = 𝕃} {ℂ = ℂ} {ℝ = ℝ} F G = record
  { FObj = F↓G.ₒ.L
  ; FHom = F↓G.ₐ.arL
  ; isF = record
        { ext = λ {A} {B} {f} {f'} eq → F↓G.~.ₗ {f = f} {f' = f'} eq
        ; id = λ {A} → 𝕃.r
        ; cmp = λ f g → 𝕃.r
        }
  }
  where module 𝕃 = ecategory-aux 𝕃
        module F↓G = comma-ecat F G
↓left = comma-left

↓right comma-right : {ℓₒl ℓₐl ℓ~l : Level}{𝕃 : ecategoryₗₑᵥ ℓₒl ℓₐl ℓ~l}{ℓₒc ℓₐc ℓ~c : Level}
                     {ℂ : ecategoryₗₑᵥ ℓₒc ℓₐc ℓ~c}{ℓₒr ℓₐr ℓ~r : Level}{ℝ : ecategoryₗₑᵥ ℓₒr ℓₐr ℓ~r}
                     (F : efunctorₗₑᵥ 𝕃 ℂ)(G : efunctorₗₑᵥ ℝ ℂ)
                       → efunctorₗₑᵥ (F ↓ G) ℝ
comma-right {𝕃 = 𝕃} {ℂ = ℂ} {ℝ = ℝ} F G = record
  { FObj = F↓G.ₒ.R
  ; FHom = F↓G.ₐ.arR
  ; isF = record
        { ext = λ {A} {B} {f} {f'} eq → F↓G.~.ᵣ {f = f} {f' = f'} eq
        ; id = λ {A} → ℝ.r
        ; cmp = λ f g → ℝ.r
        }
  }
  where module ℝ = ecategory-aux ℝ
        module F↓G = comma-ecat F G
↓right = comma-right
  
                  




-- comma category whose right factor is constant

module funct-slice-ecat-defs {ℓ₁ ℓ₂ ℓ₃ : Level}{ℂ : ecategoryₗₑᵥ ℓ₁ ℓ₂ ℓ₃}
                             {ℓ₄ ℓ₅ ℓ₆ : Level}{𝔻 : ecategoryₗₑᵥ ℓ₄ ℓ₅ ℓ₆}
                             (F : efunctorₗₑᵥ ℂ 𝔻)(Y : ecat.Obj 𝔻)
                             where
  private
    module ℂ = ecategory-aux ℂ
    module 𝔻 = ecategory-aux 𝔻
    module F = efunctor-aux F

  --_ₒis-over : (X : ℂ.Obj) → Set ℓ₅
  --X ₒis-over = || 𝔻.Hom (F.ₒ X) Y ||

  record Obj/ : Set (ℂ.ℓₒ ⊔ 𝔻.ℓₐᵣᵣ) where
    field
      L : ℂ.Obj
      ar : || 𝔻.Hom (F.ₒ L) Y || -- L ₒis-over

{-
  _ₐis-over[_,_] : {X X' : ℂ.Obj}
                      → || ℂ.Hom X X' || → X ₒis-over → X' ₒis-over
                        → Set ℓ₆
  f ₐis-over[ x , x' ] = x' 𝔻.∘ F.ₐ f 𝔻.~ x
-}

  record ||Hom/|| (A B : Obj/) : Set (ℂ.ℓₐᵣᵣ ⊔ 𝔻.ℓ~) where
    private
      module A = Obj/ A
      module B = Obj/ B
    field
      arL : || ℂ.Hom A.L B.L ||
      tr : B.ar 𝔻.∘ F.ₐ arL 𝔻.~ A.ar -- arL ₐis-over[ A.ar , B.ar ]

  Hom/ :  Obj/ → Obj/ → setoid {ℂ.ℓₐᵣᵣ ⊔ 𝔻.ℓ~} {ℂ.ℓ~}
  Hom/ A B = sub-setoid (ℂ.Hom A.L B.L) (||Hom/||.arL {A} {B})
               where module A = Obj/ A
                     module B = Obj/ B

  idar/ :  (A : Obj/) → ||Hom/|| A A
  idar/ A = record
    { arL = ℂ.idar A.L
    ; tr = 𝔻.ridgg 𝔻.r F.id
    }
    where module A = Obj/ A
  
  cmp/ :  {A B C : Obj/}
             → ||Hom/|| B C → ||Hom/|| A B → ||Hom/|| A C
  cmp/ {A} {B} {C} g f = record
    { arL = g.arL ℂ.∘ f.arL
    ; tr = ~proof C.ar ∘  F.ₐ (g.arL ℂ.∘ f.arL)    ~[ ∘e (F.cmpˢ f.arL g.arL) r ] /
                   C.ar ∘ F.ₐ g.arL ∘ F.ₐ f.arL     ~[ ass ⊙ ∘e r g.tr ] /
                   B.ar ∘ F.ₐ f.arL                 ~[ f.tr ]∎
                   A.ar ∎
    }
    where module A = Obj/ A
          module B = Obj/ B
          module C = Obj/ C
          module f = ||Hom/|| f
          module g = ||Hom/|| g
          open ecategory-aux 𝔻  
-- end funct-slice-ecat-defs


funct-slice-ecat : {ℓ₁ ℓ₂ ℓ₃ : Level}{ℂ : ecategoryₗₑᵥ ℓ₁ ℓ₂ ℓ₃}
                   {ℓ₄ ℓ₅ ℓ₆ : Level}{𝔻 : ecategoryₗₑᵥ ℓ₄ ℓ₅ ℓ₆}
                   (F : efunctorₗₑᵥ ℂ 𝔻) → ecat.Obj 𝔻
                     → ecategoryₗₑᵥ (ecat.ℓₒ ℂ ⊔ ecat.ℓₐᵣᵣ 𝔻) (ecat.ℓₐᵣᵣ ℂ ⊔ ecat.ℓ~ 𝔻) (ecat.ℓ~ ℂ)
funct-slice-ecat {ℂ = ℂ} {𝔻} F Y = record
  { Obj = Obj/
  ; Hom = Hom/
  ; isecat = record
           { _∘_ = cmp/
           ; idar = idar/
           ; ∘ext = λ _ _ _ _ → ℂ.∘e
           ; lidax = λ _ → ℂ.lid
           ; ridax = λ _ → ℂ.rid
           ; assoc = λ _ _ _ → ℂ.ass
           }
  }
  where module ℂ = ecategory-aux ℂ
        open funct-slice-ecat-defs F Y

infix 2 _↓ₒ_
_↓ₒ_ : {ℓ₁ ℓ₂ ℓ₃ : Level}{ℂ : ecategoryₗₑᵥ ℓ₁ ℓ₂ ℓ₃}
       {ℓ₄ ℓ₅ ℓ₆ : Level}{𝔻 : ecategoryₗₑᵥ ℓ₄ ℓ₅ ℓ₆}
       (F : efunctorₗₑᵥ ℂ 𝔻) → ecat.Obj 𝔻
          → ecategoryₗₑᵥ (ecat.ℓₒ ℂ ⊔ ecat.ℓₐᵣᵣ 𝔻) (ecat.ℓₐᵣᵣ ℂ ⊔ ecat.ℓ~ 𝔻) (ecat.ℓ~ ℂ)
F ↓ₒ Y = funct-slice-ecat F Y

module funct-slice-ecat {ℓ₁ ℓ₂ ℓ₃ : Level}{ℂ : ecategoryₗₑᵥ ℓ₁ ℓ₂ ℓ₃}
                        {ℓ₄ ℓ₅ ℓ₆ : Level}{𝔻 : ecategoryₗₑᵥ ℓ₄ ℓ₅ ℓ₆}
                        (F : efunctorₗₑᵥ ℂ 𝔻)(Y : ecat.Obj 𝔻) where
  open ecat (F ↓ₒ Y) using (Obj; Hom)
  open funct-slice-ecat-defs F Y public --hiding (_ₒis-over; _ₐis-over[_,_])
  module ₒ = Obj/
  module ₐ {A B : Obj}(f : || Hom A B ||) = ||Hom/|| {A} {B} f
  --open funct-slice-ecat-defs F Y using (_ₒis-over; _ₐis-over[_,_]) public


-- the slice under a functor between locally small categories is locally small
funct-slice-ecat-lc : {ℂ 𝔻 : ecategory}(F : efunctor ℂ 𝔻) → ecat.Obj 𝔻
                     → ecategory
funct-slice-ecat-lc = funct-slice-ecat


-- forgetful functor

↓ₒfrgt : {ℓ₁ ℓ₂ ℓ₃ : Level}{ℂ : ecategoryₗₑᵥ ℓ₁ ℓ₂ ℓ₃}
         {ℓ₄ ℓ₅ ℓ₆ : Level}{𝔻 : ecategoryₗₑᵥ ℓ₄ ℓ₅ ℓ₆}
         (F : efunctorₗₑᵥ ℂ 𝔻)(Y : ecat.Obj 𝔻)
           → efunctorₗₑᵥ (F ↓ₒ Y) ℂ
↓ₒfrgt {ℂ = ℂ} {𝔻 = 𝔻} F Y = record
  { FObj = F↓Y.ₒ.L
  ; FHom = F↓Y.ₐ.arL
  ; isF = record
        { ext = λ {A} {B} {f} {f'} eq → eq
        ; id = λ {A} → ℂ.r
        ; cmp = λ f g → ℂ.r
        }
  }
  where module ℂ = ecategory-aux ℂ
        module F↓Y = funct-slice-ecat F Y

-- pushforward

module funct-slice-ecat-pushforward {ℓ₁ ℓ₂ ℓ₃ : Level}{ℂ : ecategoryₗₑᵥ ℓ₁ ℓ₂ ℓ₃}
                                    {ℓ₄ ℓ₅ ℓ₆ : Level}{𝔻 : ecategoryₗₑᵥ ℓ₄ ℓ₅ ℓ₆}
                                    (F : efunctorₗₑᵥ ℂ 𝔻){X Y : ecat.Obj 𝔻}(g : || ecat.Hom 𝔻 X Y ||)
                                    where
  private
    module ℂ = ecat ℂ
    module 𝔻 = ecat 𝔻
    module F = efctr F
    module F↓X where
      open ecat (F ↓ₒ X) public
      open funct-slice-ecat F X public
    module F↓Y where
      open ecat (F ↓ₒ Y) public
      open funct-slice-ecat F Y public

  pushf-ob : F↓X.Obj → F↓Y.Obj
  pushf-ob a = record
    { L = a.L
    ; ar = g 𝔻.∘ a.ar
    }
    where module a = F↓X.ₒ a

  pushf-ar : {a a' : F↓X.Obj} → || F↓X.Hom a a' || → || F↓Y.Hom (pushf-ob a) (pushf-ob a') ||
  pushf-ar {a} {a'} k = record
    { arL = k.arL
    ; tr = ~proof k!a'.ar 𝔻.∘ F.ₐ k.arL             ~[ assˢ ] /
                  g  𝔻.∘ (a'.ar 𝔻.∘ F.ₐ k.arL)      ~[ ∘e k.tr r ]∎
                  g 𝔻.∘ a.ar ∎
    }
    where module a = F↓X.ₒ a
          module a' = F↓X.ₒ a'
          module k = F↓X.ₐ k
          module k!a = F↓Y.ₒ (pushf-ob a)
          module k!a' = F↓Y.ₒ (pushf-ob a')
          open ecategory-aux-only 𝔻
-- end funct-slice-ecat-pushforward

↓ₒpushforward : {ℓ₁ ℓ₂ ℓ₃ : Level}{ℂ : ecategoryₗₑᵥ ℓ₁ ℓ₂ ℓ₃}
                {ℓ₄ ℓ₅ ℓ₆ : Level}{𝔻 : ecategoryₗₑᵥ ℓ₄ ℓ₅ ℓ₆}
                (F : efunctorₗₑᵥ ℂ 𝔻){X Y : ecat.Obj 𝔻}(g : || ecat.Hom 𝔻 X Y ||)
                  → efunctorₗₑᵥ (F ↓ₒ X) (F ↓ₒ Y)
↓ₒpushforward {ℂ = ℂ} {𝔻 = 𝔻} F g = record
  { FObj = pushf-ob
  ; FHom = pushf-ar
  ; isF = record
        { ext = λ eq → eq
        ; id = λ {_} → r
        ; cmp = λ _ _ → r
        }
  }
  where open funct-slice-ecat-pushforward F g
        open ecategory-aux-only ℂ using (r)



-- comma category whose left factor is constant
-- when the functor F is a presheaf, this is isomorphic to its category of elements

module slice-funct-ecat-defs {ℓ₁ ℓ₂ ℓ₃ : Level}{ℂ : ecategoryₗₑᵥ ℓ₁ ℓ₂ ℓ₃}
                             {ℓ₄ ℓ₅ ℓ₆ : Level}{𝔻 : ecategoryₗₑᵥ ℓ₄ ℓ₅ ℓ₆}
                             (F : efunctorₗₑᵥ ℂ 𝔻)(Y : ecat.Obj 𝔻)
                             where
  private
    module ℂ = ecategory-aux ℂ
    module 𝔻 = ecategory-aux 𝔻
    module F = efunctor-aux F

  record /Obj : Set (ℂ.ℓₒ ⊔ 𝔻.ℓₐᵣᵣ) where
    field
      R : ℂ.Obj
      ar : || 𝔻.Hom Y (F.ₒ R) ||

  record ||/Hom|| (A B : /Obj) : Set (ℂ.ℓₐᵣᵣ ⊔ 𝔻.ℓ~) where
    private
      module A = /Obj A
      module B = /Obj B
    field
      arR : || ℂ.Hom A.R B.R ||
      tr : F.ₐ arR 𝔻.∘ A.ar 𝔻.~ B.ar

  /Hom : /Obj → /Obj → setoid {ℂ.ℓₐᵣᵣ ⊔ 𝔻.ℓ~} {ℂ.ℓ~}
  /Hom A B = sub-setoid (ℂ.Hom A.R B.R) (||/Hom||.arR {A} {B})
               where module A = /Obj A
                     module B = /Obj B

  /idar : (A : /Obj) → ||/Hom|| A A
  /idar A = record
    { arR = ℂ.idar A.R
    ; tr = 𝔻.lidgg 𝔻.r F.id
    }
    where module A = /Obj A
  
  /cmp : {A B C : /Obj}
             → ||/Hom|| B C → ||/Hom|| A B → ||/Hom|| A C
  /cmp {A} {B} {C} g f = record
    { arR = g.arR ℂ.∘ f.arR
    ; tr = ~proof F.ₐ (g.arR ℂ.∘ f.arR) ∘ A.ar    ~[ ∘e r (F.cmpˢ f.arR g.arR) ⊙ assˢ ] /
                  F.ₐ g.arR ∘ F.ₐ f.arR ∘ A.ar     ~[ ∘e f.tr r ] /
                  F.ₐ g.arR ∘ B.ar                 ~[ g.tr ]∎
                  C.ar ∎
    }
    where module A = /Obj A
          module B = /Obj B
          module C = /Obj C
          module f = ||/Hom|| f
          module g = ||/Hom|| g
          open ecategory-aux 𝔻  
-- end slice-funct-ecat-defs


slice-funct-ecat : {ℓ₁ ℓ₂ ℓ₃ ℓ₄ ℓ₅ ℓ₆ : Level}{ℂ : ecategoryₗₑᵥ ℓ₁ ℓ₂ ℓ₃}{𝔻 : ecategoryₗₑᵥ ℓ₄ ℓ₅ ℓ₆}
                   (F : efunctorₗₑᵥ ℂ 𝔻) → ecat.Obj 𝔻
                     → ecategoryₗₑᵥ (ecat.ℓₒ ℂ ⊔ ecat.ℓₐᵣᵣ 𝔻) (ecat.ℓₐᵣᵣ ℂ ⊔ ecat.ℓ~ 𝔻) (ecat.ℓ~ ℂ)
slice-funct-ecat {ℂ = ℂ} {𝔻} F Y = record
  { Obj = /Obj
  ; Hom = /Hom
  ; isecat = record
           { _∘_ = /cmp
           ; idar = /idar
           ; ∘ext = λ _ _ _ _ → ℂ.∘e
           ; lidax = λ _ → ℂ.lid
           ; ridax = λ _ → ℂ.rid
           ; assoc = λ _ _ _ → ℂ.ass
           }
  }
  where module ℂ = ecategory-aux ℂ
        open slice-funct-ecat-defs F Y

infix 2 _ₒ↓_
_ₒ↓_ : {ℓ₁ ℓ₂ ℓ₃ : Level}{ℂ : ecategoryₗₑᵥ ℓ₁ ℓ₂ ℓ₃}{ℓ₄ ℓ₅ ℓ₆ : Level}{𝔻 : ecategoryₗₑᵥ ℓ₄ ℓ₅ ℓ₆}
       (Y : ecat.Obj 𝔻)(F : efunctorₗₑᵥ ℂ 𝔻)
          → ecategoryₗₑᵥ (ecat.ℓₒ ℂ ⊔ ecat.ℓₐᵣᵣ 𝔻) (ecat.ℓₐᵣᵣ ℂ ⊔ ecat.ℓ~ 𝔻) (ecat.ℓ~ ℂ)
Y ₒ↓ F = slice-funct-ecat F Y


module slice-funct-ecat {ℓ₁ ℓ₂ ℓ₃ : Level}{ℂ : ecategoryₗₑᵥ ℓ₁ ℓ₂ ℓ₃}
                        {ℓ₄ ℓ₅ ℓ₆ : Level}{𝔻 : ecategoryₗₑᵥ ℓ₄ ℓ₅ ℓ₆}
                        (F : efunctorₗₑᵥ ℂ 𝔻)(Y : ecat.Obj 𝔻) where
  open ecat (Y ₒ↓ F) using (Obj; Hom)
  open slice-funct-ecat-defs F Y
  module ₒ = /Obj
  module ₐ {A B : Obj}(f : || Hom A B ||) = ||/Hom|| {A} {B} f


-- forgetful functor

ₒ↓frgt : {ℓ₁ ℓ₂ ℓ₃ : Level}{ℂ : ecategoryₗₑᵥ ℓ₁ ℓ₂ ℓ₃}
         {ℓ₄ ℓ₅ ℓ₆ : Level}{𝔻 : ecategoryₗₑᵥ ℓ₄ ℓ₅ ℓ₆}
         (F : efunctorₗₑᵥ ℂ 𝔻)(Y : ecat.Obj 𝔻)
           → efunctorₗₑᵥ (Y ₒ↓ F) ℂ
ₒ↓frgt {ℂ = ℂ} {𝔻 = 𝔻} F Y = record
  { FObj = Y↓F.ₒ.R
  ; FHom = Y↓F.ₐ.arR
  ; isF = record
        { ext = λ {A} {B} {f} {f'} eq → eq
        ; id = λ {A} → ℂ.r
        ; cmp = λ f g → ℂ.r
        }
  }
  where module ℂ = ecategory-aux ℂ
        module Y↓F = slice-funct-ecat F Y

module slice-funct-ecat-pullback {ℓ₁ ℓ₂ ℓ₃ : Level}{ℂ : ecategoryₗₑᵥ ℓ₁ ℓ₂ ℓ₃}
                                 {ℓ₄ ℓ₅ ℓ₆ : Level}{𝔻 : ecategoryₗₑᵥ ℓ₄ ℓ₅ ℓ₆}
                                 (F : efunctorₗₑᵥ ℂ 𝔻){X Y : ecat.Obj 𝔻}(g : || ecat.Hom 𝔻 X Y ||)
                                 where
  private
    module ℂ = ecat ℂ
    module 𝔻 = ecat 𝔻
    module F = efctr F
    module X↓F where
      open ecat (X ₒ↓ F) public
      open slice-funct-ecat F X public
    module Y↓F where
      open ecat (Y ₒ↓ F) public
      open slice-funct-ecat F Y public

  pullb-ob : Y↓F.Obj → X↓F.Obj
  pullb-ob b = record
    { R = b.R
    ; ar = b.ar 𝔻.∘ g
    }
    where module b = Y↓F.ₒ b

  pullb-ar : {b b' : Y↓F.Obj} → || Y↓F.Hom b b' || → || X↓F.Hom (pullb-ob b) (pullb-ob b') ||
  pullb-ar {b} {b'} k = record
    { arR = k.arR
    ; tr = ~proof F.ₐ k.arR 𝔻.∘ k*b.ar            ~[ ass ] /
                  (F.ₐ k.arR 𝔻.∘ b.ar) 𝔻.∘ g     ~[ ∘e r k.tr ]∎
                  b'.ar 𝔻.∘ g ∎
    }
    where module b = Y↓F.ₒ b
          module b' = Y↓F.ₒ b'
          module k = Y↓F.ₐ k
          module k*b = X↓F.ₒ (pullb-ob b)
          module k*b' = X↓F.ₒ (pullb-ob b')
          open ecategory-aux-only 𝔻
-- end slice-funct-ecat-pullback

ₒ↓pullback : {ℓ₁ ℓ₂ ℓ₃ : Level}{ℂ : ecategoryₗₑᵥ ℓ₁ ℓ₂ ℓ₃}{ℓ₄ ℓ₅ ℓ₆ : Level}{𝔻 : ecategoryₗₑᵥ ℓ₄ ℓ₅ ℓ₆}
             (F : efunctorₗₑᵥ ℂ 𝔻){X Y : ecat.Obj 𝔻}(g : || ecat.Hom 𝔻 X Y ||)
               → efunctorₗₑᵥ (Y ₒ↓ F) (X ₒ↓ F)
ₒ↓pullback {ℂ = ℂ} {𝔻 = 𝔻} F g = record
  { FObj = pullb-ob
  ; FHom = pullb-ar
  ; isF = record
        { ext = λ eq → eq
        ; id = λ {_} → r
        ; cmp = λ _ _ → r
        }
  }
  where open slice-funct-ecat-pullback F g
        open ecategory-aux-only ℂ using (r)
                                 

                             
