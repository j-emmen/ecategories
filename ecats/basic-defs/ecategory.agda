
{-# OPTIONS --without-K #-}

module ecats.basic-defs.ecategory where


open import Agda.Primitive using (Level; _⊔_) renaming (lzero to 0ₗₑᵥ; lsuc to sucₗₑᵥ) public
open import tt-basics.setoids renaming (||_|| to ||_||std)


-- E-Categories

infix 3 ||_||
||_|| : {ℓo ℓr : Level} → setoid {ℓo} {ℓr} → Set ℓo
||_|| X = ||_||std X

record is-ecategory {ℓ₁ ℓ₂ ℓ₃ : Level}(Obj : Set ℓ₁)
                    (Hom : Obj → Obj → setoid {ℓ₂} {ℓ₃})
                    : Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃)
                    where
  -- notation
  infix 2 _~_
  _~_ : {a b : Obj} → (f f' : || Hom a b ||) → Set ℓ₃
  f ~ f' = < Hom _ _ > f ~ f'
  infixr 5 _∘_
  field
    _∘_ : {a b c : Obj} →  || Hom b c ||  → || Hom a b || → || Hom a c ||
    idar : (a : Obj) → || Hom a a ||
    ∘ext : {a b c : Obj} → (f f' : || Hom a b ||) → (g g' : || Hom b c ||)
              → f ~ f' → g ~ g' → g ∘ f ~ g' ∘ f'
    lidax : {a b : Obj} → (f : || Hom a b ||) → idar b ∘ f ~ f
    ridax : {a b : Obj} → (f : || Hom a b ||) → f ∘ idar a ~ f
    assoc : {a b c d : Obj} → (f : || Hom a b ||) → (g : || Hom b c ||) → (h : || Hom c d ||)
               → h ∘ (g ∘ f) ~ (h ∘ g) ∘ f
  ℓₒ ℓₐᵣᵣ ℓ~ ℓₕₒₘ ℓₙₒ~ ℓₐₗₗ : Level
  ℓₒ = ℓ₁
  ℓₐᵣᵣ = ℓ₂
  ℓ~ = ℓ₃
  ℓₕₒₘ = ℓₐᵣᵣ ⊔ ℓ~
  ℓₙₒ~ = ℓₒ ⊔ ℓₐᵣᵣ
  ℓₐₗₗ = ℓₒ ⊔ ℓₕₒₘ


record ecategoryₗₑᵥ (ℓ₁ ℓ₂ ℓ₃ : Level) : Set (sucₗₑᵥ (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃)) where
  field
    Obj : Set ℓ₁
    Hom : Obj → Obj → setoid {ℓ₂} {ℓ₃}
    isecat : is-ecategory Obj Hom
  open is-ecategory isecat public

1ₗₑᵥ 2ₗₑᵥ : Level
1ₗₑᵥ = sucₗₑᵥ 0ₗₑᵥ
2ₗₑᵥ = sucₗₑᵥ 1ₗₑᵥ

ecategory : Set₂
ecategory = ecategoryₗₑᵥ 1ₗₑᵥ 0ₗₑᵥ 0ₗₑᵥ
module ecategory (ℂ : ecategory) = ecategoryₗₑᵥ {1ₗₑᵥ} {0ₗₑᵥ} {0ₗₑᵥ} ℂ

small-ecategory : Set₁
small-ecategory = ecategoryₗₑᵥ 0ₗₑᵥ 0ₗₑᵥ 0ₗₑᵥ
module small-ecategory (ℂ : small-ecategory)= ecategoryₗₑᵥ {0ₗₑᵥ} {0ₗₑᵥ} {0ₗₑᵥ} ℂ

large-ecategory : Set₂
large-ecategory = ecategoryₗₑᵥ 1ₗₑᵥ 1ₗₑᵥ 1ₗₑᵥ
module large-ecategory (ℂ : large-ecategory) = ecategoryₗₑᵥ {1ₗₑᵥ} {1ₗₑᵥ} {1ₗₑᵥ} ℂ

Large-ecategory : Set₃
Large-ecategory = ecategoryₗₑᵥ 2ₗₑᵥ 1ₗₑᵥ 1ₗₑᵥ
module Large-ecategory (ℂ : Large-ecategory) = ecategoryₗₑᵥ {2ₗₑᵥ} {1ₗₑᵥ} {1ₗₑᵥ} ℂ


module hom-ext-prop-defs {ℓ₁ ℓ₂ ℓ₃ : Level}(ℂ : ecategoryₗₑᵥ ℓ₁ ℓ₂ ℓ₃) where
  open ecategoryₗₑᵥ ℂ
  is-hom-ext : {ℓ : Level}(Prp : {X Y : Obj} → || Hom X Y || → Set ℓ)
                  → Set (ℓₐₗₗ ⊔ ℓ)
  is-hom-ext Prp = {X Y : Obj} → is-ext-prop {X = Hom X Y} Prp
  module is-hom-ext {ℓ : Level}{Prp : {X Y : Obj} → || Hom X Y || → Set ℓ}
                    (ext : is-hom-ext Prp) {X} {Y}
                    = is-ext-prop (ext {X} {Y})

  mkis-hom-ext : {ℓ : Level}(Prp : {X Y : Obj} → || Hom X Y || → Set ℓ)
                 (trnsp : {X Y : Obj} {f f' : || Hom X Y ||}
                             → f ~ f' → Prp f → Prp f')
                   → is-hom-ext Prp
  mkis-hom-ext Prp trnsp {X} {Y} = record { trnsp = trnsp {X} {Y} }

  is-cmp-congr : {ℓ : Level}(Prp : {X Y : Obj} → || Hom X Y || → Set ℓ)
                      → Set (ℓₙₒ~ ⊔ ℓ)
  is-cmp-congr Prp = {X Y Z : Obj} {g : || Hom Y Z ||} {f :  || Hom X Y ||}
                        → Prp g → Prp f → Prp (g ∘ f)

  record is-ecat-congr {ℓ : Level}(Prp : {X Y : Obj} → || Hom X Y || → Set ℓ)
                       : Set (ℓₐₗₗ ⊔ ℓ)
                       where
    --constructor mkis-ecat-congr
    field
      -- extensional
      ext : is-hom-ext Prp
      -- closed under composition
      ∘congr : is-cmp-congr Prp
    open is-hom-ext ext public
    ∘c :  {X Y Z : Obj} {g : || Hom Y Z ||} {f :  || Hom X Y ||}
             → Prp g → Prp f → Prp (g ∘ f)
    ∘c = ∘congr
    ∘ce :  {X Y Z : Obj} {g : || Hom Y Z ||} {f :  || Hom X Y ||} {h : || Hom X Z ||}
              → g ∘ f ~ h → Prp g → Prp f → Prp h
    ∘ce tr gpf fpf = trnsp tr (∘c gpf fpf)

-- end hom-ext-prop-defs

{-
module hom-ext-prop-defs (ℂ : ecategory) where
  open ecategory ℂ
  is-hom-ext : {ℓ : Level}(Prp : {X Y : Obj} → || Hom X Y || → Set ℓ)
                  → Set (1ₗₑᵥ ⊔ ℓ)
  is-hom-ext Prp = {X Y : Obj} → is-ext-prop {X = Hom X Y} Prp
  module is-hom-ext {ℓ : Level}{Prp : {X Y : Obj} → || Hom X Y || → Set ℓ}
                    (ext : is-hom-ext Prp) {X} {Y}
                    = is-ext-prop (ext {X} {Y})

  mkis-hom-ext : {ℓ : Level}(Prp : {X Y : Obj} → || Hom X Y || → Set ℓ)
                 (trnsp : {X Y : Obj} {f f' : || Hom X Y ||}
                             → f ~ f' → Prp f → Prp f')
                   → is-hom-ext Prp
  mkis-hom-ext Prp trnsp {X} {Y} = record { trnsp = trnsp {X} {Y} }

  is-cmp-congr : {ℓ : Level}(Prp : {X Y : Obj} → || Hom X Y || → Set ℓ)
                      → Set (1ₗₑᵥ ⊔ ℓ)
  is-cmp-congr Prp = {X Y Z : Obj} {g : || Hom Y Z ||} {f :  || Hom X Y ||}
                        → Prp g → Prp f → Prp (g ∘ f)

  record is-ecat-congr {ℓ : Level}(Prp : {X Y : Obj} → || Hom X Y || → Set ℓ)
                       : Set (1ₗₑᵥ ⊔ ℓ)
                       where
    --constructor mkis-ecat-congr
    field
      -- extensional
      ext : is-hom-ext Prp
      -- closed under composition
      ∘congr : is-cmp-congr Prp
    open is-hom-ext ext public
    ∘c :  {X Y Z : Obj} {g : || Hom Y Z ||} {f :  || Hom X Y ||}
             → Prp g → Prp f → Prp (g ∘ f)
    ∘c = ∘congr
    ∘ce :  {X Y Z : Obj} {g : || Hom Y Z ||} {f :  || Hom X Y ||} {h : || Hom X Z ||}
              → g ∘ f ~ h → Prp g → Prp f → Prp h
    ∘ce tr gpf fpf = trnsp tr (∘c gpf fpf)

-- end hom-ext-prop-defs
-}


-- record is-hom-ext-rec {ℓₒ ℓₕ : Level}(ℂ : ecategoryₗₑᵥ ℓₒ ℓₕ)
--                       {ℓ : Level}(P : {X Y : ecat.Obj ℂ} → || ecat.Hom ℂ X Y || → Set ℓ)
--                       : Set (ℓₒ ⊔ ℓₕ ⊔ ℓ)
--                       where
--   open ecat ℂ
--   field
--     isext : {X Y : Obj} → is-ext-prop {X = Hom X Y} P
--   module ext {X Y : Obj} = is-ext-prop (isext {X} {Y})
--   open ext public


-- mkis-hom-ext-rec : {ℓₒ ℓₕ : Level}(ℂ : ecategoryₗₑᵥ ℓₒ ℓₕ){ℓ : Level}
--                    (Propos : {X Y : ecat.Obj ℂ} → || ecat.Hom ℂ X Y || → Set ℓ)
--                    (trnsp : {X Y : ecat.Obj ℂ} {f f' : || ecat.Hom ℂ X Y ||}
--                      → < ecat.Hom ℂ X Y > f ~ f' → Propos f → Propos f')
--                           → is-hom-ext-rec ℂ Propos
-- mkis-hom-ext-rec ℂ Propos trnsp = record { isext = record { trnsp = trnsp } }


-- record is-cmp-congr-rec {ℓₒ ℓₕ : Level}(ℂ : ecategoryₗₑᵥ ℓₒ ℓₕ){ℓ : Level}
--                     (Propos : {X Y : ecat.Obj ℂ} → || ecat.Hom ℂ X Y || → Set ℓ)
--                     : Set (ℓₒ ⊔ ℓₕ ⊔ ℓ)
--                     where
--   open ecat ℂ
--   field
--     ∘c : {X Y Z : Obj} {g : || Hom Y Z ||} {f :  || Hom X Y ||}
--             → Propos g → Propos f → Propos (g ∘ f)
    

-- record is-ecat-congr-rec {ℓₒ ℓₕ : Level}(ℂ : ecategoryₗₑᵥ ℓₒ ℓₕ){ℓ : Level}
--                      (Propos : {X Y : ecat.Obj ℂ} → || ecat.Hom ℂ X Y || → Set ℓ)
--                      : Set (ℓₒ ⊔ ℓₕ ⊔ ℓ)
--                      where
--   constructor mkis-ecat-congr
--   open ecat ℂ
--   field
--     -- extensional
--     ext : is-hom-ext-rec ℂ Propos
--     -- closed under composition
--     ∘congr : is-cmp-congr-rec ℂ Propos
--   open is-hom-ext-rec ext hiding (isext) public 
--   open is-cmp-congr-rec ∘congr public
--   ∘ce :  {X Y Z : Obj} {g : || Hom Y Z ||} {f :  || Hom X Y ||} {h : || Hom X Z ||}
--             → g ∘ f ~ h → Propos g → Propos f → Propos h
--   ∘ce tr gpf fpf = trnsp tr (∘c gpf fpf)

