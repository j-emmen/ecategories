
{-# OPTIONS --without-K #-}

module ecats.basic-defs.ecategory-not where

open import Agda.Primitive
open import tt-basics.setoids hiding (||_||)
open import ecats.basic-defs.ecategory



-- Notation

module ecategory-aux-level {ℓ ℓ' : Level} {Obj : Set ℓ} {Hom : Obj → Obj → setoid {ℓ'}}
                           (isecat : is-ecategory Obj Hom)
                           where
  open is-ecategory isecat
  open setoid

-- Equational reasonig

  infixr 2 /_~[_]_ -- the / character is needed to avoid parenthesis for parsing
  infix 1 ~proof_~[_]_

  /_~[_]_ : {a b : Obj} (f₁ {f₂ f₃} : || Hom a b ||) → f₁ ~ f₂ → f₂ ~ f₃ → f₁ ~ f₃
  / f₁ ~[ pf ] pf' = H./ f₁ ~[ pf ] pf'
                   where module H = setoid-aux (Hom _ _)
  
  ~proof_~[_]_ : {a b : Obj} (f₁ {f₂ f₃} : || Hom a b ||) → f₁ ~ f₂ → f₂ ~ f₃ → f₁ ~ f₃
  ~proof_~[_]_ {a} {b} f₁ pf pf' = H.~proof f₁ ~[ pf ] pf'
              --~proof f₁ ~[ pf ] pf' = H.~proof f₁ ~[ pf ] pf'
                                 where module H = setoid-aux (Hom a b)

  theeqproof eqres-end : {a b : Obj} (f f' : || Hom a b ||) → f ~ f' → f ~ f'
  theeqproof = H.eqreasend
            where module H = setoid-aux (Hom _ _)
  eqres-end = theeqproof

  infix 1 theeqproof
  syntax theeqproof f f' pf = f ~[ pf ] f'
  infix 3 eqres-end --/_~[_]∎_∎
  syntax eqres-end f f' pf = / f ~[ pf ]∎ f' ∎
  

  infixr 35 _⊙_
  infix 40 _ˢ
  r : {a b : Obj} {f : || Hom a b ||} → f ~ f
  r = refl (Hom _ _) _
  
  _ˢ :  {a b : Obj} {f₁ f₂ : || Hom a b ||} → f₁ ~ f₂ → f₂ ~ f₁
  pf ˢ = sym (Hom _ _) pf
  
  _⊙_ : {a b : Obj} {f₁ f₂ f₃ : || Hom a b ||} → f₁ ~ f₂ → f₂ ~ f₃
         → f₁ ~ f₃
  pf₁ ⊙ pf₂ = tra (Hom _ _) pf₁ pf₂

  ∘e : {a b c : Obj} → {f f' : || Hom a b ||} {g g' : || Hom b c ||}
             → f ~ f' → g ~ g' → g ∘ f ~ (g' ∘ f')
  ∘e {f = f} {f' = f'} {g = g} {g' = g'} = ∘ext f f' g g'
  
  
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

-- end module ecategory-aux-level





module ecategory-aux-only (ℂ : ecategory) where
  open ecategory ℂ
  open ecategory-aux-level isecat public
-- end module ecategory-aux-only


module ecategory-aux (ℂ : ecategory) where
  open ecategory ℂ public
  open ecategory-aux-only ℂ public
-- end module ecategory-aux




module small-ecategory-aux-only (𝕀 : small-ecategory) where
  open small-ecategory 𝕀
  open ecategory-aux-level isecat public
-- end module ecategory-aux-only


module small-ecategory-aux (𝕀 : small-ecategory) where
  open small-ecategory 𝕀 public
  open small-ecategory-aux-only 𝕀 public
-- end module ecategory-aux



module Large-ecategory-aux-only (ℂ : Large-ecategory) where
  open Large-ecategory ℂ
  open ecategory-aux-level isecat public
-- end module Large-ecategory-aux-only


module Large-ecategory-aux (ℂ : Large-ecategory) where
  open Large-ecategory ℂ public
  open Large-ecategory-aux-only ℂ public
-- end module Large-ecategory-aux

