
{-# OPTIONS --without-K #-}

module ecats.concr-ecats.finite-ecat where

open import tt-basics.all-basics renaming (||_|| to ||_||std)
open import ecats.basic-defs.ecat-def&not
--open import ecats.basic-defs.isomorphism
open import ecats.basic-defs.commut-shapes
open import ecats.basic-defs.preorder
open import ecats.isomorphism
open import ecats.constructions.discrete-ecat
open import ecats.constructions.free-ecat-on-graph
open import ecats.concr-ecats.Std-lev
open import ecats.functors.defs.efunctor-d&n
open import ecats.functors.props.efunctor
open import ecats.functors.defs.natural-iso
open import ecats.functors.defs.natural-transformation

----------------------------------------
--  discrete category on finite objects
----------------------------------------

1-cat : small-ecategory
1-cat = discrete-ecat N₁

module 1-cat-aux where
  private
    module 𝟙 where
      open ecat 1-cat public
      open iso-d&p 1-cat public
  cntr-ar : (x : N₁) → || 𝟙.Hom x 0₁ || × || 𝟙.Hom 0₁ x ||
  cntr-ar 0₁ = pair (𝟙.idar 0₁) (𝟙.idar 0₁)
  cntr-uq : {x y : N₁} (f g : || 𝟙.Hom x y ||) → f 𝟙.~ g
  cntr-uq = disc-set-is-poset N₁-ishSet
  cntr : (x : N₁) → x 𝟙.≅ₒ 0₁
  cntr x = record
    { a12 = prj1 (cntr-ar x)
    ; a21 = prj2 (cntr-ar x)
    ; isop = record
      { iddom = cntr-uq _ _
      ; idcod = cntr-uq _ _
      }
    }
  module cntr (x : N₁) = 𝟙._≅ₒ_ (cntr x)
  {-conn-gpd : (x y : N₁) → x 𝟙.≅ₒ y
  conn-gpd x 0₁ = cntr x
  module conn-gpd (x y : N₁) = 𝟙._≅ₒ_ (conn-gpd x y)-}
  -- {x y : N₁} (f : || 𝟙.Hom x y ||) → f 𝟙.~ conn-gpd.a12 x y

  private
    module aux1 {ℓₒ ℓₐ ℓ~ : Level} (ℂ : ecategoryₗₑᵥ ℓₒ ℓₐ ℓ~) where
      private
        module ℂ where
          open ecat ℂ public
          open iso-d&p ℂ public
      fctr2ob : efunctorₗₑᵥ 1-cat ℂ → ℂ.Obj
      fctr2ob F = F.ₒ 0₁
        where
          module F = efctr F
      ob2fctr : ecat.Obj ℂ → efunctorₗₑᵥ 1-cat ℂ
      ob2fctr A = cnstF 1-cat ℂ A
      -- NB: fctr2ob (ob2fctr A) = A
      fctr2ob2fctr : (F : efunctorₗₑᵥ 1-cat ℂ) → ob2fctr (fctr2ob F) ≅ₐ F
      fctr2ob2fctr F = record
        { natt = record
               { fnc = λ {x} →  F.ₐ (cntr.a21 x)
               ; nat = λ {x} {y} f → ℂa.~proof
                     F.ₐ (prj2 (cntr-ar y)) ℂ.∘ foF.ₐ f        ~[ ℂa.∘e F.idˢ ℂa.r ] ℂa./
                     F.ₐ (prj2 (cntr-ar y)) ℂ.∘ F.ₐ (𝟙.idar 0₁) ~[ F.∘∘ (cntr-uq _ _) ]∎
                     F.ₐ f ℂ.∘ F.ₐ (prj2 (cntr-ar x)) ∎
               }
        ; natt⁻¹ = record
                 { fnc = λ {x} →  F.ₐ (cntr.a12 x)
                 ; nat = λ {x} {y} f → ℂa.~proof
                     F.ₐ (prj1 (cntr-ar y)) ℂ.∘ F.ₐ f        ~[ F.∘∘ (cntr-uq _ _) ] ℂa./
                     F.ₐ (𝟙.idar 0₁) ℂ.∘ F.ₐ (prj1 (cntr-ar x))~[ ℂa.∘e ℂa.r F.id ]∎
                     foF.ₐ f ℂ.∘ F.ₐ (prj1 (cntr-ar x)) ∎
                 }
        ; isiso = λ {x} → ℂ.inv-iso-pair (F.pres-iso-pair (cntr.isop x)) 
        }
        where
          module F where
            open efunctor-aux F public
            open efunctor-lev-props F public
          module ℂa = ecategory-aux ℂ
          module foF = efctr (ob2fctr (fctr2ob F))
  private module aux2  {ℓₒ ℓₐ ℓ~ : Level} {ℂ : ecategoryₗₑᵥ ℓₒ ℓₐ ℓ~} = aux1 ℂ
  open aux2 public




1+1-cat : small-ecategory
1+1-cat = discrete-ecat (N₁ + N₁)
module 1+1-cat = ecat 1+1-cat

{- need binary coproducts
Fin-disc-cat : N → small-ecategory
Fin-disc-cat O = discrete-ecat N₀
Fin-disc-cat (s n) = {!!}
-}

---------------------------
--  the equaliser category
---------------------------

module equal-ecat where
  Ob : Set
  Ob = N₁ + N₁
  Ar : N₁ + N₁ → N₁ + N₁ → Set
  Ar (inl x₁) (inl x) = N₁
  Ar (inr x₁) (inl x) = N₀
  Ar (inl x₁) (inr x) = N₁ + N₁
  Ar (inr x₁) (inr x) = N₁
  H : N₁ + N₁ → N₁ + N₁ → setoid
  H i j = Freestd (Ar i j)
  cmp : {i j k : N₁ + N₁} → || H j k || → || H i j || → || H i k ||
  cmp {i} {inl 0₁} {inl 0₁} = λ _ f → f
  cmp {i} {inr x₁} {inl x} = N₀rec
  cmp {inl 0₁} {inl 0₁} {inr x} = λ g _ → g
  cmp {inr x₂} {inl x₁} {inr x} = λ g → N₀rec
  cmp {i} {inr 0₁} {inr 0₁} = λ _ f → f
  idar : (i : N₁ + N₁) → || H i i ||
  idar = sumrec {C = λ i → || H i i ||} (λ x → x) (λ x → x)
  ext : {a b c : N₁ + N₁} (f f' : || H a b ||) (g g' : || H b c ||)
           → < H a b > f ~ f' → < H b c > g ~ g'
             → < H a c > cmp {a} {b} {c} g f ~ cmp {a} {b} {c} g' f'
  ext {a} {inl 0₁} {inl 0₁} f f' g g' eqf eqg = eqf
  ext {inl 0₁} {inl 0₁} {inr x} f f' g g' eqf eqg = eqg
  ext {a} {inr 0₁} {inr 0₁} f f' g g' eqf eqg = eqf
  lid : {a b : N₁ + N₁}(f : || H a b ||)
           → < H a b > cmp {a} {b} {b} (idar b) f ~ f
  lid {a} {inl 0₁} = λ _ → setoid-aux.r (H a (inl 0₁))
  lid {a} {inr 0₁} = λ _ → setoid-aux.r (H a (inr 0₁))
  rid : {a b : N₁ + N₁}(f : || H a b ||)
           → < H a b > cmp {a} {a} {b} f (idar a) ~ f
  rid {inl 0₁} {inl 0₁} = λ f → pj2 N₁-isContr f ⁻¹
  rid {inr x₁} {inl x} = N₀rec
  rid {inl 0₁} {inr x} = λ f → =rf
  rid {inr 0₁} {inr 0₁} = λ f → pj2 N₁-isContr f ⁻¹
  ass : {a b c d : N₁ + N₁}(f : || H a b ||)(g : || H b c ||)(h : || H c d ||)
           → < H a d > cmp {a} {c} {d} h (cmp {a} {b} {c} g f)
                           ~ cmp {a} {b} {d} (cmp {b} {c} {d} h g) f
  ass {a} {b} {inl 0₁} {inl 0₁} = λ _ _ _ → setoid-aux.r (H a (inl 0₁))
  ass {a} {b} {inr x₁} {inl x} = λ _ _ → N₀rec
  ass {a} {inl 0₁} {inl 0₁} {inr x} = λ _ _ _ → setoid-aux.r (H a (inr x))
  ass {a} {inr x₂} {inl x₁} {inr x} = λ _ → N₀rec
  ass {a} {b} {inr 0₁} {inr 0₁} = λ _ _ _ → setoid-aux.r (H a (inr 0₁))
-- end equal-ecat

Eql-cat : small-ecategory
Eql-cat = record
     { Obj = Ob
     ; Hom = H
     ; isecat = record
                  { _∘_ = λ {a} {b} {c} → cmp {a} {b} {c}
                  ; idar = idar
                  ; ∘ext = λ {a} {b} {c} → ext {a} {b} {c}
                  ; lidax = λ {a} {b} → lid {a} {b}
                  ; ridax = λ {a} {b} → rid {a} {b}
                  ; assoc = λ {a} {b} {c} {d} → ass {a} {b} {c} {d}
                  }
     }
     where open equal-ecat

module Eql-cat where
  open ecat Eql-cat hiding (_~_) public
  <Hom_,_>_~_ : (A B : Obj)(f f' : || Hom A B ||) → Set
  <Hom A , B > f ~ f' = < Hom A B > f ~ f'
  [_,_,_]_∘_ : (A B C : Obj) → || Hom B C || → || Hom A B || → || Hom A C ||
  [ A , B , C ] g ∘ f = _∘_ {A} {B} {C} g f
  dom cod : Obj
  dom = inl 0₁
  cod = inr 0₁
  a₁ a₂ : {x x' y : N₁} → || Hom (inl x) (inr x') ||
  a₁ {x} {x'} {y} = inl y
  a₂ {x} {x'} {y} = inr y
  a₁0 a₂0 : || Hom dom cod ||
  a₁0 = a₁ {0₁} {0₁} {0₁}
  a₂0 = a₂ {0₁} {0₁} {0₁}

module Eql-graph where
  private module Eql = Eql-cat
  V : Set
  V = N₁ + N₁
  E : V → V → Set
  E v (inl x) = N₀
  E (inl x₁) (inr x) = N₁ + N₁
  E (inr x₁) (inr x) = N₀
  dom cod : V
  dom = inl 0₁
  cod = inr 0₁
  a₁ a₂ : E dom cod
  a₁ = inl 0₁
  a₂ = inr 0₁
  IE : {u v : V} → E u v → || Eql.Hom u v ||
  IE {u} {inl x} = N₀rec
  IE {inl x₁} {inr x} = λ z → z
  IE {inr x₁} {inr x} = N₀rec
  ES :(u v : V) → setoid {0ₗₑᵥ} {0ₗₑᵥ}
  ES u v = Freestd (E u v)
  _~_ : {u v : V}(uv uv' : E u v) → Set
  uv ~ uv' = ES._∼_ uv uv'
           where module ES {u v : V} = setoid (ES u v)  
  IE-ext : {u v : V}{uv uv' : E u v} → uv ~ uv' → < Eql-cat.Hom u v > IE uv ~ IE uv'
  IE-ext {u} {v} {uv} = =J (λ uv' _ → < Eql-cat.Hom u v > IE uv ~ IE uv')
                           (r {u} {v} {IE uv})
                      where open ecategory-aux Eql-cat using (r)
-- end Eql-graph


module Eql-cat-is-free-props {ℓ₁ ℓ₂ ℓ₃ : Level}(𝔻 : ecategoryₗₑᵥ ℓ₁ ℓ₂ ℓ₃)
                             {GO : Eql-cat.Obj → ecat.Obj 𝔻}
                             {GE : {u v : Eql-cat.Obj} → Eql-graph.E u v
                                        → || ecat.Hom 𝔻 (GO u) (GO v) ||}
                             (GEext : {u v : Eql-cat.Obj}{uv uv' : Eql-graph.E u v}
                                         → uv Eql-graph.~ uv'
                                           → < ecat.Hom 𝔻 (GO u) (GO v) > GE uv ~ GE uv')
                            where
  private
    module 𝔻 where
      open ecat 𝔻 public
      open ecategory-aux-only 𝔻 using (r) public
      open iso-defs 𝔻 public
      open iso-props 𝔻 public
    module EqlC = Eql-cat
    module EqlG = Eql-graph
    GH : {A B : EqlC.Obj} → || EqlC.Hom A B || → || 𝔻.Hom (GO A) (GO B) ||
    GH {inl 0₁} {inl 0₁} f = 𝔻.idar (GO (inl 0₁))
    GH {inr x₁} {inl x} f = N₀rec f
    GH {inl x₁} {inr x} f = sumrec (λ i → GE (inl i)) (λ i → GE (inr i)) f
    GH {inr 0₁} {inr 0₁} f = 𝔻.idar (GO (inr 0₁))

  lift  : efunctorₗₑᵥ Eql-cat 𝔻
  lift = record
       { FObj = GO
       ; FHom = GH
       ; isF = record
             { ext = λ {A} {B} → ext A B
             ; id = λ {A} → id A
             ; cmp = cmp
             }
       }
       where open ecategory-aux-only 𝔻 using (r; lid; rid)
             ext : (A B : EqlC.Obj){f f' : || EqlC.Hom A B ||}
                      → < EqlC.Hom A B > f ~ f' → GH f 𝔻.~ GH f'
             ext A B = free-std-is-min-pf (𝔻.Hom (GO A) (GO B)) GH
             id : (A : EqlC.Obj) → GH (EqlC.idar A) 𝔻.~ 𝔻.idar (GO A)
             id (inl 0₁) = r
             id (inr 0₁) = r
             cmp : {A B C : EqlC.Obj}(f : || EqlC.Hom A B ||)(g : || EqlC.Hom B C ||)
                      → < 𝔻.Hom (GO A) (GO C) > GH g 𝔻.∘ GH f ~ GH (EqlC.[ A , B , C ] g ∘ f)
             cmp {A} {inl 0₁} {inl 0₁} = λ _ _ → lid
             cmp {A} {inr x₁} {inl x} = λ _ → N₀rec
             cmp {inl 0₁} {inl 0₁} {inr x} = λ _ _ → rid
             cmp {inr x₂} {inl x₁} {inr x} = N₀rec
             cmp {A} {inr 0₁} {inr 0₁} = λ _ _ → lid
  private module lift = efunctorₗₑᵥ lift

  ar : (A : EqlC.Obj) → || 𝔻.Hom (lift.ₒ A) (GO A) ||
  ar A = 𝔻.idar (GO A)
  nat : {A B : EqlC.Obj} (AB : EqlG.E A B)
           → ar B 𝔻.∘ lift.ₐ (EqlG.IE AB) 𝔻.~  GE AB 𝔻.∘ ar A
  nat {A} {inl x} = N₀rec
  nat {inl 0₁} {inr 0₁} (inl x₂) = lidgen ridˢ
    where open ecategory-aux-only 𝔻 using (lidgen; ridˢ)
  nat {inl 0₁} {inr 0₁} (inr x₂) = lidgen ridˢ
    where open ecategory-aux-only 𝔻 using (lidgen; ridˢ)
  nat {inr x₁} {inr x} = N₀rec

  iso : (A : EqlC.Obj) → 𝔻.is-iso (ar A)
  iso A = 𝔻.idar-is-iso (GO A)

  uq : {H : efunctorₗₑᵥ Eql-cat 𝔻}
       (Hfnc : {A : EqlC.Obj} → || 𝔻.Hom (efctr.ₒ H A) (GO A) ||)
       (Hnat : {A B : EqlC.Obj}(AB : Eql-graph.E A B)
                   → Hfnc {B} 𝔻.∘ efctr.ₐ H (Eql-graph.IE AB) 𝔻.~ GE AB 𝔻.∘ Hfnc {A})
       (Hiso : {A : EqlC.Obj} → 𝔻.is-iso (Hfnc {A}))
          → H ≅ₐ lift
  uq {H} Hfnc Hnat Hiso = record
    { natt = record
             { fnc = Hfnc
             ; nat = λ {A} {B} → natfnc A B
             }
    ; natt⁻¹ = record
             { fnc = λ {A} → Hiso.invf A
             ; nat = λ {A} {B} f → 𝔻.iso-sq (Hiso.isisopair A) (Hiso.isisopair B) (natfnc A B f) 
             }
    ; isiso = λ {A} → Hiso.isisopair A
    }
    where module H = efctr H
          module Hiso (A : EqlC.Obj) = 𝔻.is-iso (Hiso {A})
          open ecategory-aux-only 𝔻
          natfnc : (A B : EqlC.Obj)(f : || EqlC.Hom A B ||)
                      → Hfnc {B} 𝔻.∘ H.ₐ f 𝔻.~ GH f 𝔻.∘ Hfnc {A}
          natfnc (inl 0₁) (inl 0₁) 0₁ = ridgg lidˢ H.id
          natfnc (inr x₁) (inl x) = N₀rec
          natfnc (inl 0₁) (inr 0₁) (inl x₂) = Hnat (inl x₂)
          natfnc (inl 0₁) (inr 0₁) (inr x₂) = Hnat (inr x₂)
          natfnc (inr 0₁) (inr 0₁) 0₁ = ridgg lidˢ H.id
-- end Eql-cat-is-free-props

Eql-cat-is-free : (ℓ₁ ℓ₂ ℓ₃ : Level)
  → Eql-cat is-free-category-on-graph Eql-graph.ES via Eql-graph.IE at-lev[ ℓ₁ , ℓ₂ , ℓ₃ ]
Eql-cat-is-free ℓ₁ ℓ₂ ℓ₃ = record
  { ext = IE-ext
  ; unvprop = λ 𝔻 GEext → record
            { fctr = lift 𝔻 GEext
            ; tr-fnc = λ {A} → ar 𝔻 GEext A
            ; tr-nat = nat 𝔻 GEext
            ; tr-iso = λ {A} → iso 𝔻 GEext A
            ; uq = uq 𝔻 GEext
            }
  }
  where open Eql-cat-is-free-props
        open Eql-graph using (IE-ext)

module Eql-cat-is-free {ℓ₁ ℓ₂ ℓ₃ : Level} = _is-free-category-on-graph_via_at-lev[_,_,_] (Eql-cat-is-free ℓ₁ ℓ₂ ℓ₃)


-- equaliser diagrams in a category

module Eql-in-ecat {ℓ₁ ℓ₂ ℓ₃ : Level}(ℂ : ecategoryₗₑᵥ ℓ₁ ℓ₂ ℓ₃) where
  private
    module ℂ where
      open ecategory-aux ℂ public
      open comm-shapes ℂ public
    module EqlC = Eql-cat
    module EqlG = Eql-graph

  module diag2arr (E : Eql-cat diag-in ℂ) where
    module E = efctr E
    src trg : ℂ.Obj
    src = E.ₒ Eql-cat.dom
    trg = E.ₒ Eql-cat.cod
    ar₁ ar₂ : || ℂ.Hom src trg ||
    ar₁ = E.ₐ Eql-cat.a₁0
    ar₂ = E.ₐ Eql-cat.a₂0
  -- end diag2arr
  
  arr2diag : {A B : ℂ.Obj}(f g : || ℂ.Hom A B ||) → Eql-cat diag-in ℂ
  arr2diag {A} {B} f g = Eql-cat-is-free.unv.fctr ℂ {FV} {FE} FEext
    where FV : EqlG.V → ℂ.Obj
          FV (inl x) = A
          FV (inr x) = B
          FE : {u v : EqlG.V} → EqlG.E u v → || ℂ.Hom (FV u) (FV v) ||
          FE {u} {inl x} = N₀rec
          FE {inl x₁} {inr x} = sumrec (λ _ → f) (λ _ → g)
          FE {inr x₁} {inr x} = N₀rec
          FEext : {u v : EqlG.V}{uv uv' : EqlG.E u v}
                     → uv EqlG.~ uv' → FE uv ℂ.~ FE uv'
          FEext {u} {v} = free-std-is-min-pf (ℂ.Hom (FV u) (FV v)) (FE {u} {v})
-- end Eql-in-ecat



-----------------------
-- the cospan category
-----------------------

module cospan-category where
-- inr (inl 0₁) → inl 0₁ ← inr (inr 0₁)

  Ob : Set
  Ob = N₁ + (N₁ + N₁)
  H : Ob → Ob → Set
  H (inl x) (inl y) = N₁
  H (inr (inl x)) (inr (inl y)) = N₁
  H (inr (inr x)) (inr (inr y)) = N₁
  H (inr x) (inl y) = N₁
  H (inl x) (inr y) = N₀
  H (inr (inl x)) (inr (inr y)) = N₀
  H (inr (inr x)) (inr (inl y)) = N₀  
  Hm : Ob → Ob → setoid {0ₗₑᵥ} {0ₗₑᵥ}
  Hm x y = Freestd (H x y)
  
  cmp :  {a b c : Ob} → || Hm b c || → || Hm a b || → || Hm a c ||
  cmp {inl 0₁} {inl 0₁} {c} g f = g
  cmp {inr x} {inl 0₁} {inl 0₁} g f = f
  cmp {inr (inl 0₁)} {inr (inl 0₁)} {c} g f = g
  cmp {inr (inr 0₁)} {inr (inr 0₁)} {c} g f = g  

  id : (a : Ob) → || Hm a a ||
  id (inl x) = 0₁
  id (inr (inl x)) = 0₁
  id (inr (inr x)) = 0₁

  ext : {a b c : Ob} (f f' : || Hm a b ||) (g g' : || Hm b c ||)
           → < Hm a b > f ~ f' → < Hm b c > g ~ g'
             → < Hm a c > cmp {a} {b} {c} g f ~ cmp {a} {b} {c} g' f'
  ext {inl 0₁} {inl 0₁} {c} f f' g g' eqf eqg = eqg
  ext {inr x} {inl 0₁} {inl 0₁} f f' g g' eqf eqg = eqf
  ext {inr (inl 0₁)} {inr (inl 0₁)} {c} f f' g g' eqf eqg = eqg
  ext {inr (inr 0₁)} {inr (inr 0₁)} {c} f f' g g' eqf eqg = eqg

  lid : {a b : Ob} (f : || Hm a b ||) → < Hm a b > cmp {a} {b} {b} (id b) f ~ f
  lid {inl 0₁} {inl 0₁} 0₁ = =rf
  lid {inr x} {inl 0₁} f = =rf
  lid {inr (inl 0₁)} {inr (inl 0₁)} 0₁ = =rf
  lid {inr (inr 0₁)} {inr (inr 0₁)} 0₁ = =rf

  rid : {a b : Ob} (f : || Hm a b ||) → < Hm a b > cmp {a} {a} {b} f (id a) ~ f
  rid {inl 0₁} {b} f = =rf
  rid {inr (inl 0₁)} {b} f = =rf
  rid {inr (inr 0₁)} {b} f = =rf

  ass : {a b c d : Ob} (f : || Hm a b ||) (g : || Hm b c ||)(h : || Hm c d ||)
           → < Hm a d > cmp h (cmp g f) ~ cmp (cmp h g) f
  ass {inl 0₁} {inl 0₁} {c} {d} f g h = =rf
  ass {inr (inl 0₁)} {inr (inl 0₁)} {c} {d} f g h = =rf
  ass {inr (inr 0₁)} {inr (inr 0₁)} {c} {d} f g h = =rf
  ass {inr (inl x)} {inl 0₁} {inl 0₁} {d} f g h = =rf
  ass {inr (inr x)} {inl 0₁} {inl 0₁} {d} f g h = =rf

-- end cospan-category

Cospan : small-ecategory
Cospan = record
     { Obj = Ob
     ; Hom = Hm
     ; isecat = record
                  { _∘_ = λ {a} {b} {c} → cmp {a} {b} {c}
                  ; idar = id
                  ; ∘ext = ext
                  ; lidax = lid
                  ; ridax = rid
                  ; assoc = ass
                  }
     }
     where open cospan-category

module Cospan-aux where
  open ecategory-aux Cospan public
  crn v₁ v₂ : Obj
  crn = inl 0₁
  v₁ = inr (inl 0₁)
  v₂ = inr (inr 0₁)
  a₁ : || Hom v₁ crn ||
  a₁ = 0₁
  a₂ : || Hom v₂ crn ||
  a₂ = 0₁

module Cospan-graph where
  private module Csp = Cospan-aux
  V : Set
  V = N₁ + (N₁ + N₁)
  E : V → V → Set
  E (inl x) y = N₀
  E (inr (inl x)) (inl y) = N₁
  E (inr (inl x)) (inr y) = N₀
  E (inr (inr x)) (inl y) = N₁
  E (inr (inr x)) (inr y) = N₀

  crn v₁ v₂ : V
  crn = inl 0₁
  v₁ = inr (inl 0₁)
  v₂ = inr (inr 0₁)
  a₁ : E v₁ crn
  a₁ = 0₁
  a₂ : E v₂ crn
  a₂ = 0₁

  IE : {u v : V} → E u v → || Csp.Hom u v ||
  IE {inr (inl x)} {inl y} uv = 0₁
  IE {inr (inr x)} {inl y} uv = 0₁

  ES :(u v : V) → setoid {0ₗₑᵥ} {0ₗₑᵥ}
  ES u v = Freestd (E u v)

  _~_ : {u v : V}(uv uv' : E u v) → Set
  uv ~ uv' = ES._∼_ uv uv'
           where module ES {u v : V} = setoid (ES u v)
  
  IE-ext : {u v : V}{uv uv' : E u v} → uv ~ uv' → IE uv Csp.~ IE uv'
  IE-ext {u} {v} {uv} {uv'} = =J (λ a _ → IE uv Csp.~ IE a) =rf
-- end Cospan-graph


module Cospan-is-free-props {ℓ₁ ℓ₂ ℓ₃ : Level}(𝔻 : ecategoryₗₑᵥ ℓ₁ ℓ₂ ℓ₃)
                            {GO : Cospan-aux.Obj → ecat.Obj 𝔻}
                            {GE : {u v : Cospan-aux.Obj} → Cospan-graph.E u v
                                       → || ecat.Hom 𝔻 (GO u) (GO v) ||}
                            (GEext : {u v : Cospan-aux.Obj}{uv uv' : Cospan-graph.E u v}
                                       → uv Cospan-graph.~ uv'
                                         → < ecat.Hom 𝔻 (GO u) (GO v) > GE uv ~ GE uv')
                            where
  --open Cospan-graph --using (IE; IE-ext)
  private
    module 𝔻 where
      open ecat 𝔻 public
      open ecategory-aux-only 𝔻 using (r) public
      open iso-defs 𝔻 public
      open iso-props 𝔻 public
    module CspC = Cospan-aux
    module CspG = Cospan-graph
    GH : {A B : CspC.Obj} → || CspC.Hom A B || → || 𝔻.Hom (GO A) (GO B) ||
    GH {inl 0₁} {inl 0₁} f = 𝔻.idar (GO (inl 0₁))
    GH {inr (inl x)} {inl y} f = GE CspG.a₁
    GH {inr (inl 0₁)} {inr (inl 0₁)} f = 𝔻.idar (GO (inr (inl 0₁)))
    GH {inr (inr x)} {inl y} f = GE CspG.a₂
    GH {inr (inr 0₁)} {inr (inr 0₁)} f = 𝔻.idar (GO (inr (inr 0₁)))
    
  lift  : efunctorₗₑᵥ Cospan 𝔻
  lift = record
       { FObj = GO
       ; FHom = GH
       ; isF = record
             { ext = ext
             ; id = λ {A} → id A
             ; cmp = cmp
             }
       }
       where open ecategory-aux-only 𝔻 using (r; lid; rid)
             ext : {A B : CspC.Obj}{f f' : || CspC.Hom A B ||} → f CspC.~ f' → GH f 𝔻.~ GH f'
             ext {inl 0₁} {inl 0₁} {f} {f'} eq = r
             ext {inr (inl x)} {inl x₁} {f} {f'} eq = r
             ext {inr (inl 0₁)} {inr (inl 0₁)} {f} {f'} eq = r
             ext {inr (inr x)} {inl x₁} {f} {f'} eq = r
             ext {inr (inr 0₁)} {inr (inr 0₁)} {f} {f'} eq = r
             id : (A : CspC.Obj) → GH (CspC.idar A) 𝔻.~ 𝔻.idar (GO A)
             id (inl 0₁) = r
             id (inr (inl 0₁)) = r
             id (inr (inr 0₁)) = r
             cmp : {A B C : CspC.Obj}(f : || CspC.Hom A B ||)(g : || CspC.Hom B C ||)
                      → GH g 𝔻.∘ GH f 𝔻.~ GH (g CspC.∘ f)
             cmp {inl 0₁} {inl 0₁} {inl 0₁} f g = rid
             cmp {inr (inl x)} {inl 0₁} {inl 0₁} f g = lid
             cmp {inr (inl 0₁)} {inr (inl 0₁)} {inl z} f g = rid
             cmp {inr (inl 0₁)} {inr (inl 0₁)} {inr (inl 0₁)} f g = rid
             cmp {inr (inr x)} {inl 0₁} {inl 0₁} f g = lid
             cmp {inr (inr 0₁)} {inr (inr 0₁)} {inl z} f g = rid
             cmp {inr (inr 0₁)} {inr (inr 0₁)} {inr (inr 0₁)} f g = rid
  private module lift = efunctorₗₑᵥ lift

  ar : {v : CspC.Obj} → || 𝔻.Hom (lift.ₒ v) (GO v) ||
  ar {v} = 𝔻.idar (GO v)
  nat : {u v : CspC.Obj} (uv : Cospan-graph.E u v)
           → ar 𝔻.∘ lift.ₐ (CspG.IE uv) 𝔻.~  GE uv 𝔻.∘ ar
  nat {inr (inl x)} {inl y} 0₁ = lidgen ridˢ
                               where open ecategory-aux-only 𝔻 using (lidgen; ridˢ)
  nat {inr (inr x)} {inl y} 0₁ = lidgen ridˢ
                               where open ecategory-aux-only 𝔻 using (lidgen; ridˢ)
  iso : {v : CspC.Obj} → 𝔻.is-iso (ar {v})
  iso {v} = 𝔻.idar-is-iso (GO v)

  uq : {H : efunctorₗₑᵥ Cospan 𝔻}
       (Hfnc : {v : CspC.Obj} → || 𝔻.Hom (efctr.ₒ H v) (GO v) ||)
       (Hnat : {u v : CspC.Obj}(uv : Cospan-graph.E u v)
                   → Hfnc 𝔻.∘ efctr.ₐ H (Cospan-graph.IE uv) 𝔻.~ GE uv 𝔻.∘ Hfnc)
       (Hiso : {v : CspC.Obj} → 𝔻.is-iso (Hfnc {v}))
          → H ≅ₐ lift
  uq {H} Hfnc Hnat Hiso = record
    { natt = record
             { fnc = Hfnc
             ; nat = natfnc
             }
    ; natt⁻¹ = record
             { fnc = Hiso.invf
             ; nat = λ {A} {B} f → 𝔻.iso-sq (Hiso.isisopair {A}) (Hiso.isisopair {B}) (natfnc f) 
             }
    ; isiso = Hiso.isisopair
    }
    where module H = efctr H
          module Hiso {v : CspC.Obj} = 𝔻.is-iso (Hiso {v})
          open ecategory-aux-only 𝔻
          natfnc : {A B : CspC.Obj} (f : || CspC.Hom A B ||)
                      → Hfnc 𝔻.∘ H.ₐ f 𝔻.~ lift.ₐ f 𝔻.∘ Hfnc
          natfnc {inl 0₁} {inl 0₁} 0₁ = ridgg (lidggˢ r lift.id) H.id
          natfnc {inr (inl x)} {inl x₁} 0₁ = Hnat CspG.a₁
          natfnc {inr (inl 0₁)} {inr (inl 0₁)} 0₁ = ridgg (lidggˢ r lift.id) H.id
          natfnc {inr (inr x)} {inl x₁} 0₁ = Hnat CspG.a₂
          natfnc {inr (inr 0₁)} {inr (inr 0₁)} 0₁ = ridgg (lidggˢ r lift.id) H.id          
-- end Cospan-is-free-props


-- To have a cospan diagram in ℂ is to have Cospan-graph → ℂ

Cospan-free : (ℓ₁ ℓ₂ ℓ₃ : Level)
  → Cospan is-free-category-on-graph Cospan-graph.ES via Cospan-graph.IE at-lev[ ℓ₁ , ℓ₂ , ℓ₃ ]
Cospan-free ℓ₁ ℓ₂ ℓ₃ = record
  { ext = IE-ext
  ; unvprop = λ 𝔻 GEext → record
            { fctr = lift 𝔻 GEext
            ; tr-fnc = ar 𝔻 GEext
            ; tr-nat = nat 𝔻 GEext
            ; tr-iso = iso 𝔻 GEext
            ; uq = uq 𝔻 GEext
            }
  }
  where open Cospan-is-free-props
        open Cospan-graph using (IE-ext)

module Cospan-free {ℓ₁ ℓ₂ ℓ₃ : Level} = _is-free-category-on-graph_via_at-lev[_,_,_] (Cospan-free ℓ₁ ℓ₂ ℓ₃)

{-
mk-cosp-diag : {ℓ₁ ℓ₂ ℓ₃ : Level}(ℂ : ecategoryₗₑᵥ ℓ₁ ℓ₂ ℓ₃)
               {FO : Cospan-aux.Obj → ecat.Obj ℂ}
               (FE : {u v : Cospan-aux.Obj} → Cospan-graph.E u v
                          → || ecat.Hom ℂ (FO u) (FO v) ||)
               (FEext : {u v : Cospan-aux.Obj}{uv uv' : Cospan-graph.E u v}
                        → uv Cospan-graph.~ uv'
                             → < ecat.Hom ℂ (FO u) (FO v) > FE uv ~ FE uv')
                   → Cospan diag-in ℂ
mk-cosp-diag {ℓ₁} {ℓ₂} {ℓ₃} ℂ FE FEext = unv.fctr ℂ FEext
                        where open _is-free-category-on-graph_via_at-lev[_,_,_] (Cospan-free ℓ₁ ℓ₂ ℓ₃)
-}

module cospan-in-ecat {ℓ₁ ℓ₂ ℓ₃ : Level}(ℂ : ecategoryₗₑᵥ ℓ₁ ℓ₂ ℓ₃) where
  private
    module ℂ where
      open ecategory-aux ℂ public
      open comm-shapes ℂ public
    module CspC = Cospan-aux
    module CspG = Cospan-graph
    
  diag2cosp : Cospan diag-in ℂ → ℂ.cospan
  diag2cosp cosp = record
    { O12 = cosp.ₒ CspC.crn
    ; cosp/ = record
            { O1 = cosp.ₒ CspC.v₁
            ; O2 = cosp.ₒ CspC.v₂
            ; a1 = cosp.ₐ CspC.a₁
            ; a2 = cosp.ₐ CspC.a₂
            }
    }
    where module cosp = diagram cosp

  cosp2diag : ℂ.cospan → Cospan diag-in ℂ
  cosp2diag cosp = Cospan-free.unv.fctr ℂ {FV} {FE} FEext
                 where module cosp = ℂ.cospan cosp
                       FV : CspG.V → ℂ.Obj
                       FV (inl x) = cosp.O12
                       FV (inr (inl x)) = cosp.O1
                       FV (inr (inr x)) = cosp.O2
                       FE : {u v : CspG.V} → CspG.E u v → || ℂ.Hom (FV u) (FV v) ||
                       FE {inr (inl x)} {inl y} uv = cosp.a1
                       FE {inr (inr x)} {inl y} uv = cosp.a2
                       FEext : {u v : CspG.V} {uv uv' : CspG.E u v}
                                  → uv CspG.~ uv' → FE uv ℂ.~ FE uv'
                       FEext {inr (inl x)} {inl x₁} {uv} {uv'} eq = ℂ.r
                       FEext {inr (inr x)} {inl x₁} {uv} {uv'} eq = ℂ.r

{-
                       FH : {A B : CspC.Obj} → || CspC.Hom A B || → || ℂ.Hom (FO A) (FO B) ||
                       FH {inl x} {inl y} f = ℂ.idar cosp.O12
                       FH {inr (inl x)} {inl y} f = cosp.a1
                       FH {inr (inl x)} {inr (inl y)} f = ℂ.idar cosp.O1
                       FH {inr (inr x)} {inl y} f = cosp.a2
                       FH {inr (inr x)} {inr (inr y)} f = ℂ.idar cosp.O2
                       FHext : {A B : CspC.Obj} {f f' : || CspC.Hom A B ||}
                                → f CspC.~ f' → FH f ℂ.~ FH f'
                       FHext {inl x} {inl x₁} {f} {f'} eq = ℂ.r
                       FHext {inr (inl x)} {inl y} {f} {f'} eq = ℂ.r
                       FHext {inr (inl x)} {inr (inl y)} {f} {f'} eq = ℂ.r
                       FHext {inr (inr x)} {inl y} {f} {f'} eq = ℂ.r
                       FHext {inr (inr x)} {inr (inr y)} {f} {f'} eq = ℂ.r
-}
{-
record
    { FObj = FO
    ; FHom = FH
    ; isF = record
          { ext = ext
          ; id = λ {A} → id A
          ; cmp = cmp
          }
    }
    where module cosp = ℂ.cospan cosp
          FO : Csp.Obj → ℂ.Obj
          FO (inl x) = cosp.O12
          FO (inr (inl x)) = cosp.O1
          FO (inr (inr x)) = cosp.O2
          FH : {A B : Csp.Obj} → || Csp.Hom A B || → || ℂ.Hom (FO A) (FO B) ||
          FH {inl x} {inl y} f = ℂ.idar cosp.O12
          FH {inr (inl x)} {inl y} f = cosp.a1
          FH {inr (inl x)} {inr (inl y)} f = ℂ.idar cosp.O1
          FH {inr (inr x)} {inl y} f = cosp.a2
          FH {inr (inr x)} {inr (inr y)} f = ℂ.idar cosp.O2

          ext : {A B : Csp.Obj} {f f' : || Csp.Hom A B ||}
                   → f Csp.~ f' → FH f ℂ.~ FH f'
          ext {inl x} {inl x₁} {f} {f'} eq = ℂ.r
          ext {inr (inl x)} {inl y} {f} {f'} eq = ℂ.r
          ext {inr (inl x)} {inr (inl y)} {f} {f'} eq = ℂ.r
          ext {inr (inr x)} {inl y} {f} {f'} eq = ℂ.r
          ext {inr (inr x)} {inr (inr y)} {f} {f'} eq = ℂ.r

          id : (A : Csp.Obj) → FH (Csp.idar A) ℂ.~ ℂ.idar (FO A)
          id (inl x) = ℂ.r
          id (inr (inl x)) = ℂ.r
          id (inr (inr x)) = ℂ.r

          cmp : {A B C : Csp.Obj}(f : || Csp.Hom A B ||)(g : || Csp.Hom B C ||)
                   → FH g ℂ.∘ FH f ℂ.~ FH (g Csp.∘ f)
          cmp {inl x} {inl y} {inl z} f g = ℂ.lid
          cmp {inr (inl x)} {inl x₁} {inl x₂} f g = ℂ.lid
          cmp {inr (inl x)} {inr (inl x₁)} {inl x₂} f g = ℂ.rid
          cmp {inr (inl x)} {inr (inl x₁)} {inr (inl x₂)} f g = ℂ.rid
          cmp {inr (inr x)} {inl x₁} {inl x₂} f g = ℂ.lid
          cmp {inr (inr x)} {inr (inr x₁)} {inl x₂} f g = ℂ.rid
          cmp {inr (inr x)} {inr (inr x₁)} {inr (inr x₂)} f g = ℂ.rid
-}

-- end cospan-in-ecat
