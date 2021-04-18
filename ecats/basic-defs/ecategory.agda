
{-# OPTIONS --without-K #-}

module ecats.basic-defs.ecategory where


open import Agda.Primitive
open import tt-basics.setoids renaming (||_|| to ||_||std)


-- E-Categories

private
  0ₗₑᵥ 1ₗₑᵥ 2ₗₑᵥ : Level
  0ₗₑᵥ = lzero
  1ₗₑᵥ = lsuc 0ₗₑᵥ
  2ₗₑᵥ = lsuc 1ₗₑᵥ

infix 3 ||_||
||_|| : {ℓ : Level} → setoid {ℓ} → Set ℓ
||_|| {ℓ} X = ||_||std {ℓ} X
  
record is-ecategory {ℓ ℓ' : Level} (Obj : Set ℓ) (Hom : Obj → Obj → setoid {ℓ'}) : Set (ℓ ⊔ ℓ')
                    where
  -- notation
  infix 2 _~_
  _~_ : {a b : Obj} → (f f' : || Hom a b ||) → Set ℓ'
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

record ecategoryₗₑᵥ (ℓₒ ℓₕ : Level) : Set (lsuc (ℓₒ ⊔ ℓₕ)) where
  field
    Obj : Set ℓₒ
    Hom : Obj → Obj → setoid {ℓₕ}
    isecat : is-ecategory Obj Hom
  open is-ecategory isecat public

module ecat {ℓₒ ℓₕ : Level}(ℂ : ecategoryₗₑᵥ ℓₒ ℓₕ) = ecategoryₗₑᵥ {ℓₒ} {ℓₕ} ℂ


ecategory : Set₂
ecategory = ecategoryₗₑᵥ 1ₗₑᵥ 0ₗₑᵥ

small-ecategory : Set₁
small-ecategory = ecategoryₗₑᵥ 0ₗₑᵥ 0ₗₑᵥ

large-ecategory : Set₂
large-ecategory = ecategoryₗₑᵥ 1ₗₑᵥ 1ₗₑᵥ

Large-ecategory : Set₃
Large-ecategory = ecategoryₗₑᵥ 2ₗₑᵥ 1ₗₑᵥ


{-
record large-ecategory : Set₂ where
  field
    Obj : Set₁
    Hom : Obj → Obj → setoid {lsuc lzero}
    isecat : is-ecategory {lsuc lzero} {lsuc lzero} Obj Hom
  open is-ecategory isecat public

-- locally small ecategory

record ecategory : Set₂ where
  constructor mkecat
  field
    {Obj} : Set₁
    {Hom} : Obj → Obj → setoid {lzero}
    isecat : is-ecategory {lsuc lzero} {lzero} Obj Hom
  open is-ecategory isecat public


-- small ecategory

record small-ecategory : Set₁ where
  field
    Obj : Set
    Hom : Obj → Obj → setoid {lzero}
    isecat : is-ecategory {lzero} {lzero} Obj Hom
  open is-ecategory isecat public

-- Large ecategory

record Large-ecategory : Set₃ where
  field
    Obj : Set₂
    Hom : Obj → Obj → setoid {lsuc lzero}
    isecat : is-ecategory {lsuc (lsuc lzero)} {lsuc lzero} Obj Hom
  open is-ecategory isecat public
-}



record is-hom-ext {ℓₒ ℓₕ : Level}(ℂ : ecategoryₗₑᵥ ℓₒ ℓₕ){ℓ : Level}
                  (P : {X Y : ecat.Obj ℂ} → || ecat.Hom ℂ X Y || → Set ℓ)
                  : Set (ℓₒ ⊔ ℓₕ ⊔ ℓ)
                  where
  open ecat ℂ
  field
    isext : {X Y : Obj} → is-ext-prop {X = Hom X Y} P
  module ext {X Y : Obj} = is-ext-prop (isext {X} {Y})
  open ext public


mkis-hom-ext : {ℓₒ ℓₕ : Level}(ℂ : ecategoryₗₑᵥ ℓₒ ℓₕ){ℓ : Level}
               (Propos : {X Y : ecat.Obj ℂ} → || ecat.Hom ℂ X Y || → Set ℓ)
               (trnsp : {X Y : ecat.Obj ℂ} {f f' : || ecat.Hom ℂ X Y ||}
                           → < ecat.Hom ℂ X Y > f ~ f' → Propos f → Propos f')
                 → is-hom-ext ℂ Propos
mkis-hom-ext ℂ Propos trnsp = record { isext = record { trnsp = trnsp } }


record is-cmp-congr {ℓₒ ℓₕ : Level}(ℂ : ecategoryₗₑᵥ ℓₒ ℓₕ){ℓ : Level}
                    (Propos : {X Y : ecat.Obj ℂ} → || ecat.Hom ℂ X Y || → Set ℓ)
                    : Set (ℓₒ ⊔ ℓₕ ⊔ ℓ)
                    where
  open ecat ℂ
  field
    ∘c : {X Y Z : Obj} {g : || Hom Y Z ||} {f :  || Hom X Y ||}
            → Propos g → Propos f → Propos (g ∘ f)
    

record is-ecat-congr {ℓₒ ℓₕ : Level}(ℂ : ecategoryₗₑᵥ ℓₒ ℓₕ){ℓ : Level}
                     (Propos : {X Y : ecat.Obj ℂ} → || ecat.Hom ℂ X Y || → Set ℓ)
                     : Set (ℓₒ ⊔ ℓₕ ⊔ ℓ)
                     where
  constructor mkis-ecat-congr
  open ecat ℂ
  field
    -- extensional
    ext : is-hom-ext ℂ Propos
    -- closed under composition
    ∘congr : is-cmp-congr ℂ Propos
  open is-hom-ext ext hiding (isext) public 
  open is-cmp-congr ∘congr public
  ∘ce :  {X Y Z : Obj} {g : || Hom Y Z ||} {f :  || Hom X Y ||} {h : || Hom X Z ||}
            → g ∘ f ~ h → Propos g → Propos f → Propos h
  ∘ce tr gpf fpf = trnsp tr (∘c gpf fpf)

