
{-# OPTIONS --without-K #-}

module ecats.basic-defs.ecategory-not where

open import Agda.Primitive
open import tt-basics.setoids hiding (||_||)
open import ecats.basic-defs.ecategory



-- Notation

-- It seems it is more useful to have these levels defined within 'is-ecategory'
-- so that we let Agda compute them for us
{-
module ecat-levels {ℓ₁ ℓ₂ ℓ₃ : Level}(ℂ : ecategoryₗₑᵥ ℓ₁ ℓ₂ ℓ₃) where
    ℓₒ ℓₐᵣᵣ ℓ~ ℓₕₒₘ ℓₙₒ~ ℓₐₗₗ : Level
    ℓₒ = ℓ₁
    ℓₐᵣᵣ = ℓ₂
    ℓ~ = ℓ₃
    ℓₕₒₘ = ℓₐᵣᵣ ⊔ ℓ~
    ℓₙₒ~ = ℓₒ ⊔ ℓₐᵣᵣ
    ℓₐₗₗ = ℓₒ ⊔ ℓₕₒₘ
-- end ecat-levels
-}

module ecat {ℓ₁ ℓ₂ ℓ₃ : Level}(ℂ : ecategoryₗₑᵥ ℓ₁ ℓ₂ ℓ₃) where
  open ecategoryₗₑᵥ ℂ public
  --open ecat-levels ℂ public
--end ecat


module ecategory-aux-level {ℓ₁ ℓ₂ ℓ₃ : Level}
                           {Obj : Set ℓ₁} {Hom : Obj → Obj → setoid {ℓ₂} {ℓ₃}}
                           (isecat : is-ecategory Obj Hom)
                           where
  open is-ecategory isecat
  open setoid

-- Equational reasonig

  infix 1 eqreas-start ~proof_~[_]_
  eqreas-start ~proof_~[_]_ : {a b : Obj} (f₁ {f₂ f₃} : || Hom a b ||) → f₁ ~ f₂ → f₂ ~ f₃ → f₁ ~ f₃
  eqreas-start {a} {b} = H.eqreasstart
                       where module H = setoid-aux (Hom a b)
  ~proof f₁ ~[ pf ] pf' = eqreas-start f₁ pf pf'

  infixr 2 eqreas-mid /_~[_]_
  -- it seems that the / character is needed to avoid parenthesis for parsing
  eqreas-mid /_~[_]_ : {a b : Obj} (f₁ {f₂ f₃} : || Hom a b ||) → f₁ ~ f₂ → f₂ ~ f₃ → f₁ ~ f₃
  eqreas-mid {a} {b} = H.eqreasmid
                     where module H = setoid-aux (Hom a b)
  / f₁ ~[ pf ] pf' = eqreas-mid f₁ pf pf'

  theeqproof eqreas-end : {a b : Obj} (f f' : || Hom a b ||) → f ~ f' → f ~ f'
  theeqproof = H.eqreasend
            where module H = setoid-aux (Hom _ _)
  eqreas-end = theeqproof

  infix 1 theeqproof
  syntax theeqproof f f' pf = f ~[ pf ] f'
  infix 3 eqreas-end --/_~[_]∎_∎
  syntax eqreas-end f f' pf = / f ~[ pf ]∎ f' ∎

  r : {a b : Obj} {f : || Hom a b ||} → f ~ f
  r = refl (Hom _ _) _
  
  infix 40 ~sym _ˢ
  ~sym _ˢ :  {a b : Obj} {f₁ f₂ : || Hom a b ||} → f₁ ~ f₂ → f₂ ~ f₁
  ~sym {a} {b} = sym (Hom a b)
  pf ˢ = ~sym pf

  infixr 35 ~tra _⊙_
  ~tra _⊙_ : {a b : Obj} {f₁ f₂ f₃ : || Hom a b ||} → f₁ ~ f₂ → f₂ ~ f₃
                → f₁ ~ f₃
  ~tra {a} {b} = tra (Hom a b)
  pf₁ ⊙ pf₂ = ~tra pf₁ pf₂

  ∘e : {a b c : Obj} → {f f' : || Hom a b ||} {g g' : || Hom b c ||}
             → f ~ f' → g ~ g' → g ∘ f ~ (g' ∘ f')
  ∘e {f = f} {f' = f'} {g = g} {g' = g'} = ∘ext f f' g g'

  -- versions of the above keeping track of intermediate points
  syntax eqreas-start f₁ {f₂} {f₃} pf pf' = ~proof f₁ ~[ pf to f₂ , f₃ ] pf'
  syntax eqreas-mid f₁ {f₂} {f₃} pf pf' = / f₁ ~[ pf to f₂ , f₃ ] pf'

  infix 45 r[_]
  r[_] : {a b : Obj}(f : || Hom a b ||) → f ~ f
  r[ f ] = refl (Hom _ _) f  
  syntax ~sym {f₁ = f₁} {f₂} pf = pf ˢ[ f₁ , f₂ ]
  syntax ~tra {f₁ = f₁} {f₂} {f₃} pf₁ pf₂ = pf₁ ⊙ pf₂ [ f₁ , f₂ , f₃ ]
  syntax ∘e {f = f} {f' = f'} {g = g} {g' = g'} pf pf' = ∘e[ pf , pf' ]for[ f ~ f' , g ~ g' ]


  
-- left identity
  lid : {a b : Obj} {f : || Hom a b ||} → idar b ∘ f ~ f
  lid {f = f} = lidax f
  
  lidˢ : {a b : Obj} {f : || Hom a b ||} → f ~ (idar b) ∘ f
  lidˢ {f = f} = lidax f ˢ

  lidgen : {a b : Obj} {f f' : || Hom a b ||} → f ~ f'
              → (idar b) ∘ f ~ f'
  lidgen {f = f} pf = lid ⊙ pf

  lidgenˢ : {a b : Obj} {f f' : || Hom a b ||} → f ~ f'
              → f ~ (idar b) ∘ f'
  lidgenˢ {f' = f'} pf = pf ⊙ lidˢ

  lidcmp : {a b c : Obj} {f : || Hom a b ||} → {fˢ : || Hom b a ||} {g : || Hom c a ||}
               → fˢ ∘ f ~ (idar a)
                 → < Hom c a > (fˢ ∘ f) ∘ g ~ g
  lidcmp {g = g} pf = (∘e r pf) ⊙ lid

  lidgg : {a b : Obj} {f f' : || Hom a b ||} {g : || Hom b b ||}
             → f ~ f' → g ~ idar b
               → g ∘ f ~ f'
  lidgg pff pfg = ∘e r pfg ⊙ lidgen pff

  lidggˢ : {a b : Obj} {f f' : || Hom a b ||} {g : || Hom b b ||}
             → f ~ f' → g ~ idar b
               → f ~ g ∘ f'
  lidggˢ pff pfg = lidgenˢ pff ⊙ ∘e r (pfg ˢ)


-- right identity
  rid : {a b : Obj} {f : || Hom a b ||} → f ∘ idar a ~ f
  rid {f = f} = ridax f

  ridˢ : {a b : Obj} {f : || Hom a b ||} → f ~ f ∘ idar a
  ridˢ {f = f} = ridax f ˢ

  ridgen : {a b : Obj} {f f' : || Hom a b ||} → f ~ f'
              → f ∘ (idar a) ~ f'
  ridgen {f = f} {f'} pf = rid ⊙ pf

  ridgenˢ : {a b : Obj} {f f' : || Hom a b ||} → f ~ f'
                 → f ~ f' ∘ (idar a)
  ridgenˢ {f = f} {f'} pf = pf ⊙ ridˢ

  ridcmp : {a b c : Obj} {f : || Hom a b ||} → {fˢ : || Hom b a ||} {g : || Hom a c ||}
               → fˢ ∘ f ~ (idar a)
                 → g ∘ (fˢ ∘ f) ~ g
  ridcmp {g = g} pf = (∘e pf r) ⊙ rid


  ridgg : {a b : Obj} {f f' : || Hom a b ||} {g : || Hom a a ||}
             → f ~ f' → g ~ idar a
               → f ∘ g ~ f'
  ridgg pff pfg = ∘e pfg r ⊙ ridgen pff

  ridggˢ : {a b : Obj} {f f' : || Hom a b ||} {g : || Hom a a ||}
             → f ~ f' → g ~ idar a
               → f ~ f' ∘ g
  ridggˢ pff pfg = ridgenˢ pff ⊙ ∘e (pfg ˢ) r


-- associativity
  ass : {a b c d : Obj} {f : || Hom a b ||} {g : || Hom b c ||} {h : || Hom c d ||}
           → h ∘ (g ∘ f) ~ (h ∘ g) ∘ f
  ass {f = f} {g = g} {h = h} = assoc f g h
  
  assˢ : {a b c d : Obj} {f : || Hom a b ||} {g : || Hom b c ||} {h : || Hom c d ||}
                    → (h ∘ g) ∘ f ~ h ∘ (g ∘ f)
  assˢ = ass ˢ

  assgen : {a b c d : Obj} {f f' : || Hom a b ||} {g g' : || Hom b c ||} {h h' : || Hom c d ||}
                → f ~ f' → g ~ g' → h ~ h'
                  → h ∘ g ∘ f ~ (h' ∘ g') ∘ f'
  assgen pff pfg pfh = ass ⊙ (∘e pff (∘e pfg pfh))

  assgenˢ : {a b c d : Obj} {f f' : || Hom a b ||} {g g' : || Hom b c ||} {h h' : || Hom c d ||}
                   → f ~ f' → g ~ g' → h ~ h'
                     → (h ∘ g) ∘ f ~ h' ∘ g' ∘ f'
  assgenˢ pff pfg pfh = assˢ ⊙ (∘e (∘e pff pfg) pfh)

-- end ecategory-aux-level





module ecategory-aux-only {ℓ₁ ℓ₂ ℓ₃ : Level}(ℂ : ecategoryₗₑᵥ ℓ₁ ℓ₂ ℓ₃) where
  open ecategoryₗₑᵥ ℂ using (isecat)
  open ecategory-aux-level isecat public
-- end module ecategory-aux-only


module ecategory-aux {ℓ₁ ℓ₂ ℓ₃ : Level}(ℂ : ecategoryₗₑᵥ ℓ₁ ℓ₂ ℓ₃) where
  open ecat ℂ public
  open ecategory-aux-only ℂ public
-- end module ecategory-aux


{-
module small-ecategory-aux-only (𝕀 : small-ecategory) where
  open small-ecategory 𝕀 using (isecat)
  open ecategory-aux-level isecat public
-- end module ecategory-aux-only

module small-ecategory-aux (𝕀 : small-ecategory) where
  open small-ecategory 𝕀 public
  open small-ecategory-aux-only 𝕀 public
-- end module ecategory-aux


module large-ecategory-aux-only (ℂ : large-ecategory) where
  open large-ecategory ℂ using (isecat)
  open ecategory-aux-level isecat public
-- end module large-ecategory-aux-only

module large-ecategory-aux (ℂ : large-ecategory) where
  open large-ecategory ℂ public
  open large-ecategory-aux-only ℂ public
-- end module large-ecategory-aux


module Large-ecategory-aux-only (ℂ : Large-ecategory) where
  open Large-ecategory ℂ using (isecat)
  open ecategory-aux-level isecat public
-- end module Large-ecategory-aux-only

module Large-ecategory-aux (ℂ : Large-ecategory) where
  open Large-ecategory ℂ public
  open Large-ecategory-aux-only ℂ public
-- end module Large-ecategory-aux
-}
