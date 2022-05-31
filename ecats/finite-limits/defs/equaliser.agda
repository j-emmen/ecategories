
{-# OPTIONS --without-K #-}

module ecats.finite-limits.defs.equaliser where

open import ecats.basic-defs.ecat-def&not




-- Equalisers

module equaliser-defs {ℓₒ ℓₐ ℓ~ : Level}(ℂ : ecategoryₗₑᵥ ℓₒ ℓₐ ℓ~) where
  open ecat ℂ

  record is-equaliser {A B E : Obj} {f f' : || Hom A B ||} {e : || Hom E A ||}
                      (pfeq : f ∘ e ~ f' ∘ e) : Set ℓₐₗₗ where
    --constructor mkis-weql
    field
      _|[_] : {C : Obj} (h : || Hom C A ||) → f ∘ h ~ f' ∘ h → || Hom C E ||
      tr : {C : Obj} {h : || Hom C A ||} (pf : f ∘ h ~ f' ∘ h)
                  → e ∘ h |[ pf ] ~ h
      uq : {C : Obj} {h h' : || Hom C E ||} → e ∘ h ~ e ∘ h' → h ~ h'
                  

  record equaliser-of {A B : Obj} (f f' : || Hom A B ||) : Set ℓₐₗₗ where
    constructor mkeql-of
    field
      {Ob} : Obj
      {ar} : || Hom Ob A ||
      {eq} : f ∘ ar ~ f' ∘ ar
      iseql : is-equaliser eq
    open is-equaliser iseql public
  
-- end equaliser-defs


record has-equalisers {ℓₒ ℓₐ ℓ~ : Level}(ℂ : ecategoryₗₑᵥ ℓₒ ℓₐ ℓ~) : Set (ecat.ℓₐₗₗ ℂ) where
  open ecategory-aux ℂ
  open equaliser-defs ℂ
  field
    eql-of : {A B : Obj} (f f' : || Hom A B ||) → equaliser-of f f'
  module eql-of {A B : Obj} {f f' : || Hom A B ||} = equaliser-of (eql-of f f')
  open eql-of public
  [_~_] : {A B : Obj} (f f' : || Hom A B ||) → Obj
  [ f ~ f' ] = Ob {f = f} {f'}


{-
  field
    weq : has-weak-equalisers ℂ
  open has-weak-equalisers weq public renaming (weqob to eqob; weqar to eqar; wequniv to equniv;
                                                weqaxcommar to eqaxcommar; weqaxcommuniv to eqaxcommuniv)
  field
    eqaxuniq : {A B C : Obj} → (f g : || Hom A B  ||) → (k k' : || Hom C (eqob f g) ||)
                → < Hom C A > ((eqar f g) ∘ k) ~ (eqar f g) ∘ k'
                  → < Hom C (eqob f g) > k ~ k'
  -- notation
  Eql = eqob
  eqlᵢ = eqar
  eqlᵤ : {A B C : Obj} → {f g : || Hom A B  ||} → (h : || Hom C A ||) → < Hom C B > (f ∘ h) ~ (g ∘ h)
              → || Hom C (Eql f g) ||
  eqlᵤ = equniv _ _
  eql-eq : {A B : Obj} → {f g : || Hom A B  ||} → f ∘ eqlᵢ f g ~ g ∘ eqlᵢ f g
  eql-eq = eqaxcommar _ _
  eql-com : {A B C : Obj} → {f g : || Hom A B  ||} → {h : || Hom C A ||} → (pf : < Hom C B > (f ∘ h) ~ (g ∘ h))
               → eqlᵢ f g ∘ eqlᵤ h pf ~ h
  eql-com = eqaxcommuniv _ _ _
  eql-uq : {A B C : Obj} → {f g : || Hom A B  ||} → {k k' : || Hom C (eqob f g) ||}
              → (eqar f g) ∘ k ~ (eqar f g) ∘ k' → k ~ k'
  eql-uq = eqaxuniq _ _ _ _
-}
