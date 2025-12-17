{-# OPTIONS --without-K #-}

module ecats.constructions.free-monoidal-on-cat where 

open import tt-basics.setoids hiding (||_||; _⇒_)
open import ecats.basic-defs.ecat-def&not
open import ecats.isomorphism
open import ecats.functors.defs.efunctor-d&n
open import ecats.functors.defs.natural-transformation
open import ecats.functors.defs.natural-iso
open import ecats.concr-ecats.ecat-ecats
open import ecats.constructions.functor-ecat
open import ecats.basic-defs.monoidal
open import ecats.functors.defs.monoidal
open import ecats.constructions.free-ecat-on-graph


-- when 𝕍 is free monoidal over ℂ via some ℂ → 𝕍

module free-monoidal-on-cat-defs {ℓₒ₁ ℓₐ₁ ℓ~₁ : Level} (ℂ : ecategoryₗₑᵥ ℓₒ₁ ℓₐ₁ ℓ~₁)
                                 {ℓₒ₂ ℓₐ₂ ℓ~₂ : Level} {𝕍 : ecategoryₗₑᵥ ℓₒ₂ ℓₐ₂ ℓ~₂}
                                 (𝕍mon : is-monoidal-cat 𝕍)
                                 (J : efunctorₗₑᵥ ℂ 𝕍)
                                 where
  private
    module ℂ = ecat ℂ
    module 𝕍 where
      open ecat 𝕍 public
      open is-monoidal-cat 𝕍mon public
    module unvprop-aux {ℓ₁' ℓ₂' ℓ₃' : Level}(𝕏 : ecategoryₗₑᵥ ℓ₁' ℓ₂' ℓ₃') where
      open ecat 𝕏 public
      open iso-defs 𝕏 public
      open iso-props 𝕏 public

  record is-free-monoidal-on-cat-univ-prop {ℓₒ₃ ℓₐ₃ ℓ~₃ : Level}{𝕎 : ecategoryₗₑᵥ ℓₒ₃ ℓₐ₃ ℓ~₃}
                                           (𝕎mon : is-monoidal-cat 𝕎) (F : efunctorₗₑᵥ ℂ 𝕎)
                                           : Set (ecat.ℓₙₒ~ ℂ ⊔ ecat.ℓₐₗₗ 𝕍 ⊔ ecat.ℓₐₗₗ 𝕎)
                                           where
    field
      fctr : efunctorₗₑᵥ 𝕍 𝕎
      tr : natural-iso (fctr ○ J) F
      mon : is-monoidal-functor fctr 𝕍mon 𝕎mon
      uq : {G : efunctorₗₑᵥ 𝕍 𝕎} → is-monoidal-functor G 𝕍mon 𝕎mon
                → G ○ J ≅ₐ F → G ≅ₐ fctr
    module fctr = efunctor-aux fctr
    module tr = natural-iso tr
    module mon = is-monoidal-functor mon
    module uq {G} (monG : is-monoidal-functor G 𝕍mon 𝕎mon) (trG : G ○ J ≅ₐ F)
           = natural-iso (uq {G} monG trG)
  -- end is-free-monoidal-on-cat-univ-prop
-- end free-monoidal-on-cat-defs


record _is-free-monoidal-on-cat_via_at-lev[_,_,_]
       {ℓₒ₂ ℓₐ₂ ℓ~₂ : Level} {𝕍 : ecategoryₗₑᵥ ℓₒ₂ ℓₐ₂ ℓ~₂}(𝕍mon : is-monoidal-cat 𝕍)
       {ℓₒ₁ ℓₐ₁ ℓ~₁ : Level} (ℂ : ecategoryₗₑᵥ ℓₒ₁ ℓₐ₁ ℓ~₁)
       (J : efunctorₗₑᵥ ℂ 𝕍) (ℓₒ' ℓₐ' ℓ~' : Level)
       : Set (ecat.ℓₐₗₗ ℂ ⊔ ecat.ℓₐₗₗ 𝕍 ⊔ sucₗₑᵥ (ℓₒ' ⊔ ℓₐ' ⊔  ℓ~'))
       where
  open free-monoidal-on-cat-defs ℂ 𝕍mon J
  field
    unvp : {𝕎 : ecategoryₗₑᵥ ℓₒ' ℓₐ' ℓ~'}
           (𝕎mon : is-monoidal-cat 𝕎) (F : efunctorₗₑᵥ ℂ 𝕎)
                → is-free-monoidal-on-cat-univ-prop 𝕎mon F
  open module unvp {𝕎 : ecategoryₗₑᵥ ℓₒ' ℓₐ' ℓ~'}
                   (𝕎mon : is-monoidal-cat 𝕎) (F : efunctorₗₑᵥ ℂ 𝕎)
                   = is-free-monoidal-on-cat-univ-prop (unvp 𝕎mon F) public

    
                                 
-- construction of the free monoidal category

module free-monoidal-ecat-on {ℓₒ ℓₐ ℓ~ : Level}(ℂ : ecategoryₗₑᵥ ℓₒ ℓₐ ℓ~) where
  private
    module ℂ = ecat ℂ


  infix 5 _⊗ₒ_ _l⊗ₐ_ _⊗rₐ_ _⊗ₐ_

  data Obj : Set ℓₒ where
    I : Obj
    iₒ : ℂ.Obj → Obj
    _⊗ₒ_ : Obj → Obj → Obj

  -- generators for the freen monoidal structure:
  -- using a single two-variable generator for the tensor,
  -- generators for identities seem to be needed to construct the tensor functor
  data HomGen : Obj → Obj → Set (ℓₒ ⊔ ℓₐ) where
    --idg : ∀ {M} → HomGen M M
    iₐg : ∀ {A B} → || ℂ.Hom A B || → HomGen (iₒ A) (iₒ B)
    l⊗ₐg : ∀ M {X Y} → HomGen X Y → HomGen (M ⊗ₒ X) (M ⊗ₒ Y)
    ⊗rₐg : ∀ N {X Y} → HomGen X Y → HomGen (X ⊗ₒ N) (Y ⊗ₒ N)
    --_⊗ₐg_ : ∀ {M₁ N₁ M₂ N₂} → HomGen M₁ N₁ → HomGen M₂ N₂
      --       → HomGen (M₁ ⊗ₒ M₂) (N₁ ⊗ₒ N₂)
    αg : ∀ M N L → HomGen ((M ⊗ₒ N) ⊗ₒ L) (M ⊗ₒ (N ⊗ₒ L))
    α⁻¹g : ∀ M N L → HomGen (M ⊗ₒ (N ⊗ₒ L)) ((M ⊗ₒ N) ⊗ₒ L)
    Iλg : ∀ M → HomGen (I ⊗ₒ M) M
    Iλ⁻¹g : ∀ M → HomGen M (I ⊗ₒ M)
    ρIg : ∀ M → HomGen (M ⊗ₒ I) M
    ρI⁻¹g : ∀ M → HomGen M (M ⊗ₒ I)

  HomGen-freestd : Obj → Obj → setoid {ℓₒ ⊔ ℓₐ} {ℓₒ ⊔ ℓₐ}
  HomGen-freestd M N = Freestd (HomGen M N)

  open free-ecat-on-graph-via-inductive-paths HomGen-freestd public
       using (emty; indv; apnd)
       renaming (fin-path to HomObj; path-id to id; path-cmp to cmp) 


  iₐ : ∀ {A B} → || ℂ.Hom A B || → HomObj (iₒ A) (iₒ B)
  iₐ f = indv (iₐg f)
  α : ∀ M N L → HomObj ((M ⊗ₒ N) ⊗ₒ L) (M ⊗ₒ (N ⊗ₒ L))
  α M N L = indv (αg M N L)
  α⁻¹ : ∀ M N L → HomObj (M ⊗ₒ (N ⊗ₒ L)) ((M ⊗ₒ N) ⊗ₒ L)
  α⁻¹ M N L = indv (α⁻¹g M N L)
  Iλ : ∀ M → HomObj (I ⊗ₒ M) M
  Iλ M = indv (Iλg M)
  Iλ⁻¹ : ∀ M → HomObj M (I ⊗ₒ M)
  Iλ⁻¹ M = indv (Iλ⁻¹g M)
  ρI : ∀ M → HomObj (M ⊗ₒ I) M
  ρI M = indv (ρIg M)
  ρI⁻¹ : ∀ M → HomObj M (M ⊗ₒ I)
  ρI⁻¹ M = indv (ρI⁻¹g M)
  _l⊗ₐ_ : ∀ M {N L} → HomObj N L → HomObj (M ⊗ₒ N) (M ⊗ₒ L)
  M l⊗ₐ emty = emty
  M l⊗ₐ apnd gg g = apnd (M l⊗ₐ gg) (l⊗ₐg M g)
  _⊗rₐ_ : ∀ {M L} → HomObj M L → ∀ N → HomObj (M ⊗ₒ N) (L ⊗ₒ N)
  emty ⊗rₐ N = emty
  apnd ff g ⊗rₐ N = apnd (ff ⊗rₐ N) (⊗rₐg N g)
  _⊗ₐ_ : ∀ {M₁ N₁ M₂ N₂} → HomObj M₁ N₁ → HomObj M₂ N₂ → HomObj (M₁ ⊗ₒ M₂) (N₁ ⊗ₒ N₂)
  emty ⊗ₐ gg = _ l⊗ₐ gg
  apnd ff g ⊗ₐ gg = apnd (ff ⊗ₐ gg) (⊗rₐg _ g)


  -- relations for the free monoidal structure
  data HomEqR : {M N : Obj} → HomObj M N → HomObj M N → Set ℂ.ℓₐₗₗ where

    -- congruence with respect to concatenation
    cmp-ext : {M N L : Obj} {p p' : HomObj M L}{q q' : HomObj L N}
                  → HomEqR p p' → HomEqR q q' → HomEqR (cmp q p) (cmp q' p')

    -- equivalence relation
    emty-rfl : ∀ {M} → HomEqR (id M) (id M)
    indv-rfl : {M N : Obj} {g : HomGen M N} → HomEqR (indv g) (indv g)
    HomEqR-tran : {M N : Obj} {p₁ p₂ p₃ : HomObj M N}
                    → HomEqR p₁ p₂ → HomEqR p₂ p₃ → HomEqR p₁ p₃
    HomEqR-sym :{M N : Obj} {p₁ p₂ : HomObj M N}
                  → HomEqR p₁ p₂ → HomEqR p₂ p₁

    -- functoriality of i
    iid : ∀ {A} → HomEqR (iₐ (ℂ.idar A)) (id (iₒ A))
    icmpext : ∀ {A B C} {f : || ℂ.Hom A B ||} {g : || ℂ.Hom B C ||} {h : || ℂ.Hom A C ||}
                → g ℂ.∘ f ℂ.~ h → HomEqR (cmp (iₐ g) (iₐ f)) (iₐ h)

    -- functoriality of ⊗
    ⊗ext : ∀ {M₁ N₁ M₂ N₂} {ff ff' : HomObj M₁ N₁} {gg gg' : HomObj M₂ N₂}
                    → HomEqR ff ff' → HomEqR gg gg' → HomEqR (ff ⊗ₐ gg) (ff' ⊗ₐ gg')
    ⊗sqg : ∀  {M₁ N₁ M₂ N₂} (g₁ : HomGen M₁ N₁) (g₂ : HomGen M₂ N₂)
                  → HomEqR (apnd (M₁ l⊗ₐ indv  g₂) (⊗rₐg N₂ g₁))
                            (apnd (indv g₁ ⊗rₐ M₂) (l⊗ₐg N₁ g₂))

    -- coherence isomorphisms
    α₁ : ∀ M N L → HomEqR (apnd (α M N L) (α⁻¹g M N L)) (id ((M ⊗ₒ N) ⊗ₒ L))
    α₂ : ∀ M N L → HomEqR (apnd (α⁻¹ M N L) (αg M N L)) (id (M ⊗ₒ (N ⊗ₒ L)))
    Iλ₁ : ∀ M → HomEqR (apnd (Iλ M) (Iλ⁻¹g M)) (id (I ⊗ₒ M))
    Iλ₂ : ∀ M → HomEqR (apnd (Iλ⁻¹ M) (Iλg M)) (id M)
    ρI₁ : ∀ M → HomEqR (apnd (ρI M) (ρI⁻¹g M)) (id (M ⊗ₒ I))
    ρI₂ : ∀ M → HomEqR (apnd (ρI⁻¹ M) (ρIg M)) (id M)

    -- their naturality
    αnat : ∀ {M N L M' N' L'}
             (ff : HomObj M M') (gg : HomObj N N') (hh : HomObj L L')
                → HomEqR (cmp (α M' N' L') ((ff ⊗ₐ gg) ⊗ₐ hh))
                         (cmp (ff ⊗ₐ (gg ⊗ₐ hh)) (α M N L))
    Iλnat : ∀ {M M'} (ff : HomObj M M')
                → HomEqR (cmp (Iλ M') (I l⊗ₐ ff))
                         (cmp ff (Iλ M))
    ρInat : ∀ {M M'} (ff : HomObj M M')
                  → HomEqR (cmp (ρI M') (ff ⊗rₐ I))
                           (cmp ff (ρI M))

    -- there may be some sense according to which it is better to phrase
    -- extensionality of ⊗ₐ and αnat using l⊗ₐ and ⊗rₐ instead ⊗ₐ
    -- although this would mean split αnat in three, and ⊗ₐ 's definition is not so bad

    -- the triangle
    IλαρI : ∀ {M N} → HomEqR (cmp (M l⊗ₐ (Iλ N)) (α M I N)) (ρI M ⊗rₐ N)
    -- the pentagon
    αpent : ∀ {M N L O} → HomEqR (cmp (M l⊗ₐ α N L O)
                                         (cmp (α M (N ⊗ₒ L) O) (α M N L ⊗rₐ O)))
                                  (cmp (α M N (L ⊗ₒ O)) (α (M ⊗ₒ N) L O))
  -- end HomEqR


  apnd-ext : {M N L : Obj} (g : HomGen N L) {p₁ p₂ : HomObj M N}
                  → HomEqR p₁ p₂ → HomEqR (apnd p₁ g) (apnd p₂ g)
  apnd-ext g eq = cmp-ext eq indv-rfl


  module cat-data where
    HomEqR-refl : {M N : Obj}(p : HomObj M N) → HomEqR p p
    HomEqR-refl emty = emty-rfl
    HomEqR-refl (apnd p g) = apnd-ext g (HomEqR-refl p)

    HomStd : Obj → Obj → setoid {ℓₒ ⊔ ℓₐ} {ℓₒ ⊔ ℓₐ ⊔ ℓ~}
    HomStd M N = record
      { object = HomObj M N
      ; _∼_ = HomEqR
      ; istteqrel = record
                  { refl = HomEqR-refl {M} {N}
                  ; sym = HomEqR-sym
                  ; tra = HomEqR-tran
                  }
      }


    cmp-rid : {M N : Obj} (p : HomObj M N) → HomEqR (cmp p (id M)) p
    cmp-rid emty = emty-rfl
    cmp-rid (apnd p g) = apnd-ext g (cmp-rid p)

    cmp-lid : {M N : Obj} (p : HomObj M N) → HomEqR (cmp (id N) p) p
    cmp-lid p = HomEqR-refl p

    cmp-ass : {M N L O : Obj}(p₁ : HomObj M N)(p₂ : HomObj N L)(p₃ : HomObj L O)
                  → HomEqR (cmp p₃ (cmp p₂ p₁))
                            (cmp (cmp p₃ p₂) p₁)
    cmp-ass p₁ p₂ emty = HomEqR-refl _ 
    cmp-ass p₁ p₂ (apnd p₃ g) = apnd-ext g (cmp-ass p₁ p₂ p₃)
  -- end cat-data
-- end free-monoidal-ecat-on


  
FMon free-monoidal-ecat-on-ecat-ecat : {ℓₒ ℓₐ ℓ~ : Level}(ℂ : ecategoryₗₑᵥ ℓₒ ℓₐ ℓ~)
                            → ecategoryₗₑᵥ (ecat.ℓₒ ℂ) (ecat.ℓₙₒ~ ℂ) (ecat.ℓₐₗₗ ℂ)
free-monoidal-ecat-on-ecat-ecat ℂ = record
  { Obj = Obj
  ; Hom = HomStd
  ; isecat = record
              { _∘_ = cmp
              ; idar = id
              ; ∘ext = λ p p' q q' → cmp-ext {p = p} {p'} {q} {q'}
              ; lidax = cmp-lid
              ; ridax = cmp-rid
              ; assoc = cmp-ass
              }
  }
  where open free-monoidal-ecat-on ℂ
        open cat-data
FMon = free-monoidal-ecat-on-ecat-ecat



module embedding-for-free-monoidal-ecat-on {ℓₒ ℓₐ ℓ~ : Level}(ℂ : ecategoryₗₑᵥ ℓₒ ℓₐ ℓ~) where
  open free-monoidal-ecat-on ℂ
  private
    module ℂ = ecategory-aux ℂ
    module Fℂ = ecategory-aux(FMon ℂ)
  
  iext : ∀ {A B} {f f' : || ℂ.Hom A B ||} → f ℂ.~ f' → HomEqR (iₐ f) (iₐ f')
  iext {A} {B} {f} {f'} eq = Fℂ.~proof
    iₐ f                     ~[ Fℂ.lidˢ ] Fℂ./
    Fℂ.idar (iₒ B) Fℂ.∘ iₐ f  ~[ Fℂ.∘e Fℂ.r (iid Fℂ.ˢ) ] Fℂ./
    iₐ (ℂ.idar B) Fℂ.∘ iₐ f   ~[ icmpext (ℂ.lid ℂ.⊙ eq) ]∎
    iₐ f' ∎

  icmp : ∀ {A B C} (f : || ℂ.Hom A B ||) (g : || ℂ.Hom B C ||)
           → HomEqR (cmp (iₐ g) (iₐ f)) (iₐ (g ℂ.∘ f))
  icmp f g = icmpext ℂ.r
-- end embedding-for-free-monoidal-ecat-on


free-monoidal-ecat-on-ecat-emb FMon-emb : {ℓₒ ℓₐ ℓ~ : Level}(ℂ : ecategoryₗₑᵥ ℓₒ ℓₐ ℓ~)
                                              → efunctorₗₑᵥ ℂ (FMon ℂ)
free-monoidal-ecat-on-ecat-emb ℂ = record
  { FObj = iₒ
  ; FHom = iₐ
  ; isF = record
        { ext = iext
        ; id = iid
        ; cmp = icmp
        }
  }
  where open free-monoidal-ecat-on ℂ
        open  embedding-for-free-monoidal-ecat-on ℂ
FMon-emb = free-monoidal-ecat-on-ecat-emb


module tensor-functor-for-free-monoidal-ecat-on {ℓₒ ℓₐ ℓ~ : Level}(ℂ : ecategoryₗₑᵥ ℓₒ ℓₐ ℓ~) where
  private
    module ℂ = ecat ℂ
    module Fℂ = ecategory-aux (FMon ℂ)
  open free-monoidal-ecat-on ℂ

  ⊗r-is-⊗ : ∀ (M : Fℂ.Obj) {X Y} (ff : || Fℂ.Hom X Y ||) → ff ⊗rₐ M Fℂ.~ ff ⊗ₐ Fℂ.idar M
  ⊗r-is-⊗ M emty = Fℂ.r
  ⊗r-is-⊗ M (apnd ff g) = apnd-ext (⊗rₐg _ g) (⊗r-is-⊗ M ff)

  ⊗r-is-⊗ˢ : ∀ (M : Fℂ.Obj) {X Y} (ff : || Fℂ.Hom X Y ||) → ff ⊗ₐ Fℂ.idar M Fℂ.~ ff ⊗rₐ M
  ⊗r-is-⊗ˢ M ff = ⊗r-is-⊗ M ff Fℂ.ˢ


  ⊗extˢ : ∀ {M₁ N₁ M₂ N₂} {ff ff' : || Fℂ.Hom M₁ N₁ ||} {gg gg' : || Fℂ.Hom M₂ N₂ ||}
                  → ff Fℂ.~ ff' → gg Fℂ.~ gg' → ff' ⊗ₐ gg' Fℂ.~ ff ⊗ₐ gg
  ⊗extˢ eq₁ eq₂ = ⊗ext eq₁ eq₂ Fℂ.ˢ


  ⊗ₐ-as-rl : ∀ {M₁ N₁ M₂ N₂} (ff₁ : HomObj M₁ N₁) (ff₂ : HomObj M₂ N₂)
            → ff₁ ⊗ₐ ff₂ Fℂ.~ (ff₁ ⊗rₐ N₂) Fℂ.∘ (M₁ l⊗ₐ ff₂)
  ⊗ₐ-as-rl emty ff₂ = Fℂ.r
  ⊗ₐ-as-rl (apnd ff₁ g₁) ff₂ = apnd-ext (⊗rₐg _ g₁) (⊗ₐ-as-rl ff₁ ff₂)

  ⊗ₐ-as-rlˢ : ∀ {M₁ N₁ M₂ N₂} (ff₁ : HomObj M₁ N₁) (ff₂ : HomObj M₂ N₂)
            → (ff₁ ⊗rₐ N₂) Fℂ.∘ (M₁ l⊗ₐ ff₂) Fℂ.~ ff₁ ⊗ₐ ff₂
  ⊗ₐ-as-rlˢ ff₁ ff₂ = ⊗ₐ-as-rl ff₁ ff₂ Fℂ.ˢ


  ⊗sqgl : ∀  {M₁ N₁ M₂ N₂} (g₁ : HomGen M₁ N₁) (ff₂ : HomObj M₂ N₂)
                  → apnd (M₁ l⊗ₐ ff₂) (⊗rₐg N₂ g₁) Fℂ.~ (N₁ l⊗ₐ ff₂) Fℂ.∘ (indv g₁ ⊗rₐ M₂)
  ⊗sqgl g₁ emty = Fℂ.rid
  ⊗sqgl g₁ (apnd ff₂ g₂) = ~proof
    (indv g₁ ⊗rₐ _) Fℂ.∘ (_ l⊗ₐ apnd ff₂ g₂)
      ~[ ass {f = _ l⊗ₐ ff₂} {_ l⊗ₐ indv g₂} {indv g₁ ⊗rₐ _}
         ⊙ ∘e r (⊗sqg g₁ g₂) ] /
    ((_ l⊗ₐ indv g₂) Fℂ.∘ (indv g₁ ⊗rₐ _)) Fℂ.∘ (_ l⊗ₐ ff₂)
      ~[ assˢ {f = _ l⊗ₐ ff₂} {indv g₁ ⊗rₐ _} {_ l⊗ₐ indv g₂}
         ⊙ ∘e (⊗sqgl g₁ ff₂) (r {f = _ l⊗ₐ indv g₂}) ] /
    (_ l⊗ₐ indv g₂) Fℂ.∘ (_ l⊗ₐ ff₂) Fℂ.∘ (indv g₁ ⊗rₐ _)
      ~[ ass {f = indv g₁ ⊗rₐ _} {_ l⊗ₐ ff₂} {_ l⊗ₐ indv g₂} ]∎
    (_ l⊗ₐ apnd ff₂ g₂) Fℂ.∘ (indv g₁ ⊗rₐ _) ∎
    where open ecategory-aux-only (FMon ℂ)


{-
  ⊗ₐ-as-lr : ∀ {M₁ N₁ M₂ N₂} (ff₁ : HomObj M₁ N₁) (ff₂ : HomObj M₂ N₂)
               → ff₁ ⊗ₐ ff₂ Fℂ.~ (N₁ l⊗ₐ ff₂) Fℂ.∘ (ff₁ ⊗rₐ M₂)
  ⊗ₐ-as-lr emty ff₂ = Fℂ.ridˢ
  ⊗ₐ-as-lr (apnd ff₁ g₁) ff₂ = ~proof
    apnd ff₁ g₁ ⊗ₐ ff₂
      ~[ ∘e (⊗ₐ-as-lr ff₁ ff₂) r
         ⊙ ass {f = ff₁ ⊗rₐ _} {_ l⊗ₐ ff₂} {indv g₁ ⊗rₐ _} ] /
    ((indv g₁ ⊗rₐ _) Fℂ.∘ (_ l⊗ₐ ff₂)) Fℂ.∘ (ff₁ ⊗rₐ _)
      ~[ ∘e r (⊗sqgl g₁ ff₂)
         ⊙ assˢ {f = ff₁ ⊗rₐ _} {indv g₁ ⊗rₐ _} {_ l⊗ₐ ff₂} ]∎
    (_ l⊗ₐ ff₂) Fℂ.∘ (apnd ff₁ g₁ ⊗rₐ _) ∎
    where open ecategory-aux-only (FMon ℂ)
-}


  ⊗ₐsq : {M₁ N₁ M₂ N₂ : Fℂ.Obj} (ff₁ : || Fℂ.Hom M₁ N₁ ||) (ff₂ : || Fℂ.Hom M₂ N₂ ||)
             → (ff₁ ⊗rₐ N₂) Fℂ.∘ (M₁ l⊗ₐ ff₂) Fℂ.~ (N₁ l⊗ₐ ff₂) Fℂ.∘ (ff₁ ⊗rₐ M₂)
  ⊗ₐsq emty ff₂ = Fℂ.ridˢ
  ⊗ₐsq (apnd ff₁ g₁) ff₂ = ~proof
    (apnd ff₁ g₁ ⊗rₐ _) Fℂ.∘ (_ l⊗ₐ ff₂)
      ~[ assˢ {f = _ l⊗ₐ ff₂} {ff₁ ⊗rₐ _} {indv g₁ ⊗rₐ _}
         ⊙ ∘e (⊗ₐsq ff₁ ff₂) (r {f = indv g₁ ⊗rₐ _}) ] /
    (indv g₁ ⊗rₐ _) Fℂ.∘ (_ l⊗ₐ ff₂) Fℂ.∘ (ff₁ ⊗rₐ _)
      ~[ ass {f = ff₁ ⊗rₐ _} {_ l⊗ₐ ff₂} {indv g₁ ⊗rₐ _}
         ⊙ ∘e r (⊗sqgl g₁ ff₂) ] /
    ((_ l⊗ₐ ff₂) Fℂ.∘ (indv g₁ ⊗rₐ _)) Fℂ.∘ (ff₁ ⊗rₐ _)
      ~[ assˢ {f = ff₁ ⊗rₐ _} {indv g₁ ⊗rₐ _} {_ l⊗ₐ ff₂} ]∎
    (_ l⊗ₐ ff₂) Fℂ.∘ (apnd ff₁ g₁ ⊗rₐ _) ∎
    where open ecategory-aux-only (FMon ℂ)

  ⊗ₐsqˢ : {M₁ N₁ M₂ N₂ : Fℂ.Obj} (ff₁ : || Fℂ.Hom M₁ N₁ ||) (ff₂ : || Fℂ.Hom M₂ N₂ ||)
             → (N₁ l⊗ₐ ff₂) Fℂ.∘ (ff₁ ⊗rₐ M₂) Fℂ.~ (ff₁ ⊗rₐ N₂) Fℂ.∘ (M₁ l⊗ₐ ff₂)
  ⊗ₐsqˢ ff₁ ff₂ = ⊗ₐsq ff₁ ff₂ Fℂ.ˢ


  ⊗ₐ-as-lr : ∀ {M₁ N₁ M₂ N₂} (ff₁ : HomObj M₁ N₁) (ff₂ : HomObj M₂ N₂)
               → ff₁ ⊗ₐ ff₂ Fℂ.~ (N₁ l⊗ₐ ff₂) Fℂ.∘ (ff₁ ⊗rₐ M₂)
  ⊗ₐ-as-lr ff₁ ff₂ = ~proof
    ff₁ ⊗ₐ ff₂                        ~[ ⊗ₐ-as-rl ff₁ ff₂ ] /
    (ff₁ ⊗rₐ _) Fℂ.∘ (_ l⊗ₐ ff₂)      ~[ ⊗ₐsq ff₁ ff₂ ]∎
    (_ l⊗ₐ ff₂) Fℂ.∘ (ff₁ ⊗rₐ _) ∎
    where open ecategory-aux-only (FMon ℂ)

  ⊗ₐ-as-lrˢ : ∀ {M₁ N₁ M₂ N₂} (ff₁ : HomObj M₁ N₁) (ff₂ : HomObj M₂ N₂)
               → (N₁ l⊗ₐ ff₂) Fℂ.∘ (ff₁ ⊗rₐ M₂) Fℂ.~ ff₁ ⊗ₐ ff₂
  ⊗ₐ-as-lrˢ ff₁ ff₂ = ⊗ₐ-as-lr ff₁ ff₂ Fℂ.ˢ
  

  l⊗cmp : ∀ M {X Y Z} (ff : || Fℂ.Hom X Y ||) (gg : || Fℂ.Hom Y Z ||)
                → (M l⊗ₐ gg) Fℂ.∘ (M l⊗ₐ ff) Fℂ.~ M l⊗ₐ (gg Fℂ.∘ ff)
  l⊗cmp M ff emty = Fℂ.r
  l⊗cmp M ff (apnd gg g) = apnd-ext (l⊗ₐg M g) (l⊗cmp M ff gg) 

  l⊗cmpˢ : ∀ M {X Y Z} (ff : || Fℂ.Hom X Y ||) (gg : || Fℂ.Hom Y Z ||)
                → M l⊗ₐ (gg Fℂ.∘ ff) Fℂ.~ (M l⊗ₐ gg) Fℂ.∘ (M l⊗ₐ ff)
  l⊗cmpˢ M ff gg = l⊗cmp M ff gg Fℂ.ˢ
  
  ⊗rcmp : ∀ M {X Y Z} (ff : || Fℂ.Hom X Y ||) (gg : || Fℂ.Hom Y Z ||)
                → (gg ⊗rₐ M) Fℂ.∘ (ff ⊗rₐ M) Fℂ.~ (gg Fℂ.∘ ff) ⊗rₐ M
  ⊗rcmp M ff emty = Fℂ.r
  ⊗rcmp M ff (apnd gg g) = apnd-ext (⊗rₐg M g) (⊗rcmp M ff gg)
  
  ⊗rcmpˢ : ∀ M {X Y Z} (ff : || Fℂ.Hom X Y ||) (gg : || Fℂ.Hom Y Z ||)
                → (gg Fℂ.∘ ff) ⊗rₐ M Fℂ.~ (gg ⊗rₐ M) Fℂ.∘ (ff ⊗rₐ M)
  ⊗rcmpˢ M ff gg = ⊗rcmp M ff gg Fℂ.ˢ


  ⊗cmp : ∀ {M₁ N₁ L₁ M₂ N₂ L₂} (ff₁ : || Fℂ.Hom M₁ N₁ ||) (gg₁ : || Fℂ.Hom N₁ L₁ ||)
              (ff₂ : || Fℂ.Hom M₂ N₂ ||) (gg₂ : || Fℂ.Hom N₂ L₂ ||)
                → (gg₁ ⊗ₐ gg₂) Fℂ.∘ (ff₁ ⊗ₐ ff₂) Fℂ.~ (gg₁ Fℂ.∘ ff₁) ⊗ₐ (gg₂ Fℂ.∘ ff₂)
  ⊗cmp ff₁ gg₁ ff₂ gg₂ = ~proof
    (gg₁ ⊗ₐ gg₂) Fℂ.∘ (ff₁ ⊗ₐ ff₂)
      ~[ ∘e (⊗ₐ-as-rl ff₁ ff₂) (⊗ₐ-as-rl gg₁ gg₂)
         ⊙ assˢ {f = (ff₁ ⊗rₐ _) Fℂ.∘ (_ l⊗ₐ ff₂)} {_ l⊗ₐ gg₂} {gg₁ ⊗rₐ _} ] /
    (gg₁ ⊗rₐ _) Fℂ.∘ (_ l⊗ₐ gg₂) Fℂ.∘ (ff₁ ⊗rₐ _) Fℂ.∘ (_ l⊗ₐ ff₂)
      ~[ ∘e (ass {f = _ l⊗ₐ ff₂} {ff₁ ⊗rₐ _} {_ l⊗ₐ gg₂}
            ⊙ ∘e r (⊗ₐsqˢ ff₁ gg₂)
            ⊙ assˢ {f = _ l⊗ₐ ff₂} {_ l⊗ₐ gg₂} {ff₁ ⊗rₐ _}) (r {f = gg₁ ⊗rₐ _}) ] /
    (gg₁ ⊗rₐ _) Fℂ.∘ (ff₁ ⊗rₐ _) Fℂ.∘ (_ l⊗ₐ gg₂) Fℂ.∘ (_ l⊗ₐ ff₂)
      ~[ ass {f = (_ l⊗ₐ gg₂) Fℂ.∘ (_ l⊗ₐ ff₂)} {ff₁ ⊗rₐ _} {gg₁ ⊗rₐ _}
         ⊙ ∘e (l⊗cmp _ ff₂ gg₂) (⊗rcmp _ ff₁ gg₁) ] /
    ((gg₁ Fℂ.∘ ff₁) ⊗rₐ _) Fℂ.∘ (_ l⊗ₐ (gg₂ Fℂ.∘ ff₂))
      ~[ ⊗ₐ-as-rlˢ (gg₁ Fℂ.∘ ff₁) (gg₂ Fℂ.∘ ff₂) ]∎
    (gg₁ Fℂ.∘ ff₁) ⊗ₐ (gg₂ Fℂ.∘ ff₂) ∎
    where open ecategory-aux-only (FMon ℂ)

  ⊗cmpˢ : ∀ {M₁ N₁ L₁ M₂ N₂ L₂} (ff₁ : || Fℂ.Hom M₁ N₁ ||) (gg₁ : || Fℂ.Hom N₁ L₁ ||)
              (ff₂ : || Fℂ.Hom M₂ N₂ ||) (gg₂ : || Fℂ.Hom N₂ L₂ ||)
                → (gg₁ Fℂ.∘ ff₁) ⊗ₐ (gg₂ Fℂ.∘ ff₂) Fℂ.~ (gg₁ ⊗ₐ gg₂) Fℂ.∘ (ff₁ ⊗ₐ ff₂)
  ⊗cmpˢ ff₁ gg₁ ff₂ gg₂ =
    ⊗cmp ff₁ gg₁ ff₂ gg₂ Fℂ.ˢ


  ⊗cmpext : ∀ {M₁ N₁ M₂ N₂ L₁ L₂} {ff₁ : || Fℂ.Hom M₁ N₁ ||} {ff₂ : || Fℂ.Hom M₂ N₂ ||}
               {gg₁ : || Fℂ.Hom N₁ L₁ ||} {gg₂ : || Fℂ.Hom N₂ L₂ ||}
               {hh₁ : || Fℂ.Hom M₁ L₁ ||} {hh₂ : || Fℂ.Hom M₂ L₂ ||}
                   → gg₁ Fℂ.∘ ff₁ Fℂ.~ hh₁ → gg₂ Fℂ.∘ ff₂ Fℂ.~ hh₂
                     → (gg₁ ⊗ₐ gg₂) Fℂ.∘ (ff₁ ⊗ₐ ff₂) Fℂ.~ hh₁ ⊗ₐ hh₂
  ⊗cmpext {ff₁ = ff₁} {ff₂} {gg₁} {gg₂} eq₁ eq₂ =
    ⊗cmp ff₁ gg₁ ff₂ gg₂ Fℂ.⊙ ⊗ext eq₁ eq₂ 

  ⊗cmpextˢ : ∀ {M₁ N₁ M₂ N₂ L₁ L₂} {ff₁ : || Fℂ.Hom M₁ N₁ ||} {ff₂ : || Fℂ.Hom M₂ N₂ ||}
               {gg₁ : || Fℂ.Hom N₁ L₁ ||} {gg₂ : || Fℂ.Hom N₂ L₂ ||}
               {hh₁ : || Fℂ.Hom M₁ L₁ ||} {hh₂ : || Fℂ.Hom M₂ L₂ ||}
                   → gg₁ Fℂ.∘ ff₁ Fℂ.~ hh₁ → gg₂ Fℂ.∘ ff₂ Fℂ.~ hh₂
                     → hh₁ ⊗ₐ hh₂ Fℂ.~ (gg₁ ⊗ₐ gg₂) Fℂ.∘ (ff₁ ⊗ₐ ff₂)
  ⊗cmpextˢ {ff₁ = ff₁} {ff₂} {gg₁} {gg₂} eq₁ eq₂ =
    ⊗ext eq₁ eq₂ Fℂ.ˢ Fℂ.⊙ ⊗cmp ff₁ gg₁ ff₂ gg₂ Fℂ.ˢ


  ⊗∘∘ : ∀ {M₁ N₁ N₁' L₁ M₂ N₂ N₂' L₂} {ff₁ : || Fℂ.Hom M₁ N₁ ||} {gg₁ : || Fℂ.Hom N₁ L₁ ||}
           {ff₂ : || Fℂ.Hom M₂ N₂ ||} {gg₂ : || Fℂ.Hom N₂ L₂ ||}
           {kk₁ : || Fℂ.Hom M₁ N₁' ||} {hh₁ : || Fℂ.Hom N₁' L₁ ||}
           {kk₂ : || Fℂ.Hom M₂ N₂' ||} {hh₂ : || Fℂ.Hom N₂' L₂ ||}
                → gg₁ Fℂ.∘ ff₁ Fℂ.~ hh₁ Fℂ.∘ kk₁ → gg₂ Fℂ.∘ ff₂ Fℂ.~ hh₂ Fℂ.∘ kk₂
                  → (gg₁ ⊗ₐ gg₂) Fℂ.∘ (ff₁ ⊗ₐ ff₂) Fℂ.~ (hh₁ ⊗ₐ hh₂) Fℂ.∘ (kk₁ ⊗ₐ kk₂)
  ⊗∘∘  {ff₁ = ff₁} {gg₁} {ff₂} {gg₂} {kk₁ = kk₁} {hh₁} {kk₂} {hh₂} eq₁ eq₂ =
    ⊗cmpext {ff₁ = ff₁} {ff₂} {gg₁} {gg₂} eq₁ eq₂ Fℂ.⊙ ⊗cmpˢ kk₁ hh₁ _ _


  module functor-data where
    l⊗ₒ : Fℂ.Obj → efunctor (FMon ℂ) (FMon ℂ)
    l⊗ₒ M = record
      { FObj = M ⊗ₒ_
      ; FHom = λ f → Fℂ.idar M ⊗ₐ f
      ; isF = record
            { ext = ⊗ext r
            ; id = r
            ; cmp = λ f g → ⊗cmp (Fℂ.idar _) (Fℂ.idar _) f g
            }
      }
      where open ecategory-aux-only (FMon ℂ) using (r; lid)
    module l⊗ₒ (M : Fℂ.Obj) = efctr (l⊗ₒ M)

    l⊗ₐ : {M N : Fℂ.Obj} → || Fℂ.Hom M N || → (l⊗ₒ M) ⇒ (l⊗ₒ N)
    l⊗ₐ {M} {N} ff = record
      { fnc = λ {X} → ff ⊗ₐ Fℂ.idar X
      ; nat = λ gg → ⊗∘∘ {ff₁ = Fℂ.idar _} {ff} {gg} {Fℂ.idar _} {ff} {Fℂ.idar _}
                      {Fℂ.idar _} {gg} rid ridˢ
      }
      where
        open ecategory-aux-only (FMon ℂ) using (rid; ridˢ)
  -- end functor-data
-- end tensor-functor-for-free-monoidal-ecat-on



free⊗ free-monoidal-ecat-on-ecat-tensor : {ℓₒ ℓₐ ℓ~ : Level}(ℂ : ecategoryₗₑᵥ ℓₒ ℓₐ ℓ~)
                                              → efunctorₗₑᵥ (FMon ℂ) [ FMon ℂ , FMon ℂ ]ᶜᵃᵗ
free-monoidal-ecat-on-ecat-tensor ℂ = record
  { FObj = l⊗ₒ
  ; FHom = l⊗ₐ
  ; isF = record
        { ext = λ eq _ → ⊗ext eq r
        ; id = λ _ → r
        ; cmp = λ ff gg X → ⊗cmp ff gg (Fℂ.idar X) (Fℂ.idar X)
        }
  }
  where
    open free-monoidal-ecat-on ℂ using (⊗ext)
    module Fℂ = ecat (FMon ℂ)
    open tensor-functor-for-free-monoidal-ecat-on ℂ using (⊗cmp)
    open tensor-functor-for-free-monoidal-ecat-on.functor-data ℂ
    open ecategory-aux-only (FMon ℂ) using (r; lid)
free⊗ = free-monoidal-ecat-on-ecat-tensor



module free-monoidal-ecat-on-ecat-is-monoidal {ℓₒ ℓₐ ℓ~ : Level}(ℂ : ecategoryₗₑᵥ ℓₒ ℓₐ ℓ~)
                                              where
  private
    module ℂ = ecat ℂ
    module Fℂ where
      open ecat (FMon ℂ) public
      open iso-d&p (FMon ℂ) public
  open monoidal-defs (FMon ℂ)
  open free-monoidal-ecat-on ℂ
  open tensor-efunctor-not (free⊗ ℂ) hiding (_⊗ₒ_; _⊗ₐ_)
                                  renaming (⊗ass-lfst to free⊗ass-l; ⊗ass-llst to free⊗ass-r)
  open tensor-functor-for-free-monoidal-ecat-on ℂ

  lun-nat : l⊗.ₒ I ⇒ IdF
  lun-nat = record
    { fnc = λ {M} → Iλ M
    ; nat = Iλnat
    }
  module lun-nat = natural-transformation lun-nat

  lun-iso : {M : Fℂ.Obj} → Fℂ.is-iso-pair (lun-nat.fnc {M}) (Iλ⁻¹ M)
  lun-iso {M} = record
    { iddom = Iλ₁ M
    ; idcod = Iλ₂ M
    }

  run-nat : ⊗rₒ I ⇒ IdF
  run-nat = record
    { fnc = λ {M} → ρI M
    ; nat = λ f → ∘e (⊗r-is-⊗ˢ I f) r ⊙ ρInat f
    }
    where open ecategory-aux-only (FMon ℂ) using (r; ∘e ; _⊙_)
  module run-nat = natural-transformation run-nat

  run-iso : {M : Fℂ.Obj} → Fℂ.is-iso-pair (run-nat.fnc {M}) (ρI⁻¹ M)
  run-iso {M} = record
    { iddom = ρI₁ M
    ; idcod = ρI₂ M
    }


  private
    module free⊗ass-l = efctr free⊗ass-l
    module free⊗ass-r = efctr free⊗ass-r

  ass-iso : (M N L : Fℂ.Obj) → Fℂ.is-iso-pair (α M N L) (α⁻¹ M N L)
  ass-iso M N L = record
    { iddom = α₁ M N L
    ; idcod = α₂ M N L
    }
  module ass-iso (M N L : Fℂ.Obj) = Fℂ.is-iso-pair (ass-iso M N L)

  ass-fst-nat : (M : Fℂ.Obj) → free⊗ass-l.ₒ M ⇒ free⊗ass-r.ₒ M
  ass-fst-nat M = record
    { fnc = λ {N} → record { fnc = λ {L} → α M N L
                            ; nat = λ f → αnat (Fℂ.idar M) (Fℂ.idar N) f }
    ; nat = λ f L → αnat (Fℂ.idar M) f (Fℂ.idar L)
    }
    where
      open ecategory-aux-only (FMon ℂ)
  module ass-fst-nat (M : Fℂ.Obj) where
    open natural-transformation (ass-fst-nat M) public
    module snd (N : Fℂ.Obj) = natural-transformation (fnc {N})

  ass-fst-nat⁻¹ : (M : Fℂ.Obj) → free⊗ass-r.ₒ M ⇒ free⊗ass-l.ₒ M
  ass-fst-nat⁻¹ M = record
    { fnc = λ {N} → record { fnc = λ {L} → α⁻¹ M N L
                            ; nat = λ f → Fℂ.iso-sq (ass-iso M N _) (ass-iso M N _)
                                                     (ass-fst-nat.snd.natˢ M N f) }
    ; nat = λ f L → Fℂ.iso-sq (ass-iso M _ L) (ass-iso M _ L)
                               (ass-fst-nat.natˢ M f L)
    }
    where
      open ecategory-aux-only (FMon ℂ)

  ass-nat : free⊗ass-l ⇒ free⊗ass-r
  ass-nat = record
    { fnc = λ {M} → ass-fst-nat M
    ; nat = λ f N L → αnat f (Fℂ.idar N) (Fℂ.idar L)
    }
     where
      open ecategory-aux-only (FMon ℂ)
  module ass where
    open natural-transformation ass-nat renaming (fnc to fncn₁; nat to nat₁; natˢ to nat₁ˢ) public
    private module fncn₁ (M : Fℂ.Obj) = natural-transformation (fncn₁ {M})
    open fncn₁ renaming (fnc to fncn₂; nat to nat₂; natˢ to nat₂ˢ) public
    private module fncn₂ (M N : Fℂ.Obj) = natural-transformation (fncn₂ M {N})
    open fncn₂ renaming (nat to nat₃; natˢ to nat₃ˢ) public
    

  free⊗-is-tensor : is-tensor-with-unit I (free⊗ ℂ)
  free⊗-is-tensor = record
    { lun = record
          { natt = lun-nat
          ; natt⁻¹ = record { fnc = λ {M} → Iλ⁻¹ M
                            ; nat = λ f → Fℂ.iso-sq lun-iso lun-iso (lun-nat.natˢ f) }
          ; isiso = lun-iso
          }
    ; run = record
          { natt = run-nat
          ; natt⁻¹ = record { fnc = λ {M} → ρI⁻¹ M
                            ; nat = λ f → Fℂ.iso-sq run-iso run-iso (run-nat.natˢ f) }
          ; isiso = run-iso
          }
    ; ass = record
          { natt = ass-nat
          ; natt⁻¹ = record { fnc = λ {M} → ass-fst-nat⁻¹ M
                            ; nat = λ f N L → Fℂ.iso-sq (ass-iso _ N L) (ass-iso _ N L)
                                                         (ass.nat₁ˢ f N L) }
          ; isiso = λ {M} → record { iddom = ass-iso.iddom M
                                   ; idcod = ass-iso.idcod M }
          }
    ; trng = IλαρI
    ; pntg = αpent
    }
-- end free-monoidal-ecat-on-ecat-is-monoidal


free-monoidal-ecat-on-ecat-is-monoidal FMon-mon : {ℓₒ ℓₐ ℓ~ : Level}(ℂ : ecategoryₗₑᵥ ℓₒ ℓₐ ℓ~)
                                             → is-monoidal-cat (FMon ℂ)
free-monoidal-ecat-on-ecat-is-monoidal ℂ = record
  { I = I
  ; tenf = free⊗ ℂ
  ; pf = free⊗-is-tensor
  }
  where
      open free-monoidal-ecat-on ℂ using (I)
      open free-monoidal-ecat-on-ecat-is-monoidal ℂ using (free⊗-is-tensor)
FMon-mon = free-monoidal-ecat-on-ecat-is-monoidal


module free-monoidal-ecat-on-ecat-is-free {ℓₒ₁ ℓₐ₁ ℓ~₁ : Level} (ℂ : ecategoryₗₑᵥ ℓₒ₁ ℓₐ₁ ℓ~₁)
                                          {ℓₒ' ℓₐ' ℓ~' : Level} {𝕎 : ecategoryₗₑᵥ ℓₒ' ℓₐ' ℓ~'}
                                          (𝕎mon : is-monoidal-cat 𝕎)
                                          (F : efunctorₗₑᵥ ℂ 𝕎)
                                          where
  open free-monoidal-on-cat-defs ℂ (FMon-mon ℂ) (FMon-emb ℂ)
  open free-monoidal-ecat-on ℂ
  private
    module ℂ = ecat ℂ
    module 𝕎 where
      open moncat 𝕎mon public
      open ecategory-aux-only 𝕎 public
      --open iso-d&p 𝕎 public
      --open is-monoidal 𝕎mon public renaming (ass to ⊗ass; lun to ⊗lun; run to ⊗run)
    module Fℂ where
      open moncat (FMon-mon ℂ) public
      module ⊗df = tensor-functor-for-free-monoidal-ecat-on ℂ
    module F = efunctor-aux F
  --open monoidal-defs (FMon ℂ)

  fctr-ob : Fℂ.Obj → 𝕎.Obj
  fctr-ob I = 𝕎.I
  fctr-ob (iₒ A) = F.ₒ A
  fctr-ob (M ⊗ₒ N) = (fctr-ob M) 𝕎.⊗ₒ (fctr-ob N)

  fctr-ar-gen : {M N : Fℂ.Obj} → HomGen M N → || 𝕎.Hom (fctr-ob M) (fctr-ob N) ||
  fctr-ar-gen (iₐg f) = F.ₐ f
  fctr-ar-gen (l⊗ₐg M g) = 𝕎.l⊗ₒ.ₐ (fctr-ob M) (fctr-ar-gen g)
  fctr-ar-gen (⊗rₐg N g) = 𝕎.⊗rₒ.ₐ (fctr-ob N) (fctr-ar-gen g) 
  fctr-ar-gen (αg M N L) = 𝕎.⊗ass.fnc (fctr-ob M) (fctr-ob N)
  fctr-ar-gen (α⁻¹g M N L) = 𝕎.⊗ass.⁻¹.fnc (fctr-ob M) (fctr-ob N)
  fctr-ar-gen (Iλg _) = 𝕎.⊗lun.fnc
  fctr-ar-gen (Iλ⁻¹g _) = 𝕎.⊗lun.fnc⁻¹
  fctr-ar-gen (ρIg _) = 𝕎.⊗run.fnc
  fctr-ar-gen (ρI⁻¹g _) = 𝕎.⊗run.fnc⁻¹


  fctr-ar : {M N : Fℂ.Obj} → || Fℂ.Hom M N || → || 𝕎.Hom (fctr-ob M) (fctr-ob N) ||
  fctr-ar {M} emty = 𝕎.idar (fctr-ob M)
  fctr-ar (apnd emty g) = fctr-ar-gen g
  fctr-ar (apnd (apnd ff g) g') = fctr-ar-gen g' 𝕎.∘ fctr-ar (apnd ff g)
  -- the additional case is to avoid `fctr-ar (indv g) = fctr-ar-gen g 𝕎.∘ 𝕎.idar _`


  fctr-apnd : {M N L : Fℂ.Obj} (ff : || Fℂ.Hom M N ||) (g : HomGen N L)
                → fctr-ar-gen g 𝕎.∘ fctr-ar ff 𝕎.~ fctr-ar (apnd ff g)
  fctr-apnd emty g = 𝕎.rid
  fctr-apnd (apnd ff g') g = 𝕎.r

  fctr-apndˢ : {M N L : Fℂ.Obj} (ff : || Fℂ.Hom M N ||) (g : HomGen N L)
                → fctr-ar (apnd ff g) 𝕎.~ fctr-ar-gen g 𝕎.∘ fctr-ar ff
  fctr-apndˢ ff g = fctr-apnd ff g 𝕎.ˢ


  fctr-cmp : {M N L : Fℂ.Obj} (ff : || Fℂ.Hom M N ||) (gg : || Fℂ.Hom N L ||)
                → fctr-ar gg 𝕎.∘ fctr-ar ff 𝕎.~ fctr-ar (gg Fℂ.∘ ff)
  fctr-cmp ff emty = 𝕎.lid
  fctr-cmp ff (apnd gg g) = ~proof
    fctr-ar (apnd gg g) 𝕎.∘ fctr-ar ff           ~[ ∘e r (fctr-apndˢ gg g) ⊙ assˢ ] /
    fctr-ar-gen g 𝕎.∘ fctr-ar gg 𝕎.∘ fctr-ar ff  ~[ ∘e (fctr-cmp ff gg) r ] /
    fctr-ar-gen g 𝕎.∘ fctr-ar (gg Fℂ.∘ ff)        ~[ fctr-apnd (gg Fℂ.∘ ff) g ]∎
    fctr-ar (apnd gg g Fℂ.∘ ff) ∎
    where open ecategory-aux-only 𝕎


  l⊗ₐeq : {M₁ M₂ N₂ : Fℂ.Obj} (gg : || Fℂ.Hom M₂ N₂ ||)
                 → 𝕎.l⊗ₒ.ₐ (fctr-ob M₁) (fctr-ar gg) 𝕎.~ fctr-ar (M₁ l⊗ₐ gg)
  l⊗ₐeq emty = 𝕎.l⊗ₒ.id _
  l⊗ₐeq {M} (apnd gg g) = ~proof
    𝕎.l⊗ₒ.ₐ _ (fctr-ar (apnd gg g))                  ~[ 𝕎.l⊗ₒ.∘axˢ _ (fctr-apnd gg g) ] /
    𝕎.l⊗ₒ.ₐ _ (fctr-ar-gen g) 𝕎.∘ 𝕎.l⊗ₒ.ₐ _ (fctr-ar gg)        ~[ ∘e (l⊗ₐeq gg) 𝕎.r ] /
    fctr-ar-gen (l⊗ₐg M g) 𝕎.∘ fctr-ar (M l⊗ₐ gg)   ~[ fctr-apnd (M l⊗ₐ gg) (l⊗ₐg M g) ]∎
    fctr-ar (M l⊗ₐ apnd gg g) ∎
    where open ecategory-aux-only 𝕎

  l⊗ₐeqˢ : {M₁ M₂ N₂ : Fℂ.Obj} (gg : || Fℂ.Hom M₂ N₂ ||)
                 → fctr-ar (M₁ l⊗ₐ gg) 𝕎.~ 𝕎.l⊗ₒ.ₐ (fctr-ob M₁) (fctr-ar gg)
  l⊗ₐeqˢ gg = l⊗ₐeq gg 𝕎.ˢ

  ⊗rₐeq : {M M₁ N₁ : Fℂ.Obj} (ff : || Fℂ.Hom M₁ N₁ ||)
                 → 𝕎.⊗rₒ.ₐ (fctr-ob M) (fctr-ar ff) 𝕎.~ fctr-ar (ff ⊗rₐ M)
  ⊗rₐeq emty = 𝕎.⊗rₒ.id _
  ⊗rₐeq {M} (apnd ff g) = ~proof
    𝕎.⊗rₒ.ₐ _ (fctr-ar (apnd ff g))                  ~[ 𝕎.⊗rₒ.∘axˢ _ (fctr-apnd ff g) ] /
    𝕎.⊗rₒ.ₐ _ (fctr-ar-gen g) 𝕎.∘ 𝕎.⊗rₒ.ₐ _ (fctr-ar ff)        ~[ ∘e (⊗rₐeq ff) 𝕎.r ] /
    fctr-ar-gen (⊗rₐg M g) 𝕎.∘ fctr-ar (ff ⊗rₐ M)   ~[ fctr-apnd (ff ⊗rₐ M) (⊗rₐg M g) ]∎
    fctr-ar (apnd ff g ⊗rₐ M) ∎
    where open ecategory-aux-only 𝕎

  ⊗rₐeqˢ : {M M₁ N₁ : Fℂ.Obj} (ff : || Fℂ.Hom M₁ N₁ ||)
                 → fctr-ar (ff ⊗rₐ M) 𝕎.~ 𝕎.⊗rₒ.ₐ (fctr-ob M) (fctr-ar ff)
  ⊗rₐeqˢ ff = ⊗rₐeq ff 𝕎.ˢ

  ⊗ₐeq : {M₁ N₁ M₂ N₂ : Fℂ.Obj} (ff : || Fℂ.Hom M₁ N₁ ||) (gg : || Fℂ.Hom M₂ N₂ ||)
                 → (fctr-ar ff) 𝕎.⊗ₐ (fctr-ar gg) 𝕎.~ fctr-ar (ff ⊗ₐ gg)
  ⊗ₐeq emty gg = 𝕎.lidgg (l⊗ₐeq gg) (𝕎.⊗rₒ.id _)
  ⊗ₐeq (apnd ff g) gg = ~proof
    (fctr-ar (apnd ff g) 𝕎.⊗ₐ fctr-ar gg)
                                        ~[ ∘e r (𝕎.⊗rₒ.∘axˢ _ (fctr-apnd ff g)) ⊙ assˢ ] /
    𝕎.⊗rₒ.ₐ _ (fctr-ar-gen g) 𝕎.∘ (fctr-ar ff 𝕎.⊗ₐ fctr-ar gg)
                                                                  ~[ ∘e (⊗ₐeq ff gg) r ] /
    𝕎.⊗rₒ.ₐ _ (fctr-ar-gen g) 𝕎.∘ fctr-ar (ff ⊗ₐ gg)
                                                     ~[ fctr-apnd (ff ⊗ₐ gg) (⊗rₐg _ g) ]∎
    fctr-ar (apnd ff g ⊗ₐ gg) ∎
    where open ecategory-aux-only 𝕎

  ⊗ₐeqˢ : {M₁ N₁ M₂ N₂ : Fℂ.Obj} (ff : || Fℂ.Hom M₁ N₁ ||) (gg : || Fℂ.Hom M₂ N₂ ||)
                 → fctr-ar (ff ⊗ₐ gg) 𝕎.~ (fctr-ar ff) 𝕎.⊗ₐ (fctr-ar gg)
  ⊗ₐeqˢ ff gg = ⊗ₐeq ff gg 𝕎.ˢ


  mon-⊗ar : {M N : Fℂ.Obj} → || 𝕎.Hom ((fctr-ob M) 𝕎.⊗ₒ (fctr-ob N)) (fctr-ob (M ⊗ₒ N)) ||
  mon-⊗ar = 𝕎.idar _

  mon-l⊗nat : {M M₂ N₂ : Fℂ.Obj} (gg : || Fℂ.Hom M₂ N₂ ||)
                 → mon-⊗ar {M} {N₂} 𝕎.∘ (𝕎.l⊗ₒ.ₐ (fctr-ob M) (fctr-ar gg))
                               𝕎.~ fctr-ar (M l⊗ₐ gg) 𝕎.∘ mon-⊗ar {M} {M₂}
  mon-l⊗nat gg = 𝕎.lidgen (𝕎.ridgenˢ (l⊗ₐeq gg))

  mon-l⊗natˢ : {M M₂ N₂ : Fℂ.Obj} (gg : || Fℂ.Hom M₂ N₂ ||)
                 → fctr-ar (M l⊗ₐ gg) 𝕎.∘ mon-⊗ar {M} {M₂}
                               𝕎.~ mon-⊗ar {M} {N₂} 𝕎.∘ (𝕎.l⊗ₒ.ₐ (fctr-ob M) (fctr-ar gg))
  mon-l⊗natˢ gg = 𝕎.ridgen (𝕎.lidgenˢ (l⊗ₐeqˢ gg))

  mon-⊗rnat : {M M₁ N₁ : Fℂ.Obj} (ff : || Fℂ.Hom M₁ N₁ ||)
                 → mon-⊗ar {N₁} {M} 𝕎.∘ (𝕎.⊗rₒ.ₐ (fctr-ob M) (fctr-ar ff))
                               𝕎.~ fctr-ar (ff ⊗rₐ M) 𝕎.∘ mon-⊗ar {M₁} {M}
  mon-⊗rnat ff = 𝕎.lidgen (𝕎.ridgenˢ (⊗rₐeq ff))

  mon-⊗nat : {M₁ N₁ M₂ N₂ : Fℂ.Obj} (ff : || Fℂ.Hom M₁ N₁ ||) (gg : || Fℂ.Hom M₂ N₂ ||)
                 → mon-⊗ar {N₁} {N₂} 𝕎.∘ ((fctr-ar ff) 𝕎.⊗ₐ (fctr-ar gg))
                               𝕎.~ fctr-ar (ff ⊗ₐ gg) 𝕎.∘ mon-⊗ar {M₁} {M₂}
  mon-⊗nat ff gg = 𝕎.lidgen (𝕎.ridgenˢ (⊗ₐeq ff gg))


  fctr-ext : {M N : Fℂ.Obj} {ff ff' : || Fℂ.Hom M N ||}
                → ff Fℂ.~ ff' → fctr-ar ff 𝕎.~ fctr-ar ff'

  fctr-ext {M} {N} (cmp-ext {p = ff} {ff'} {gg} {gg'} eq₁ eq₂) = ~proof
    fctr-ar (cmp gg ff)             ~[ fctr-cmp ff gg ˢ ] /
    fctr-ar gg 𝕎.∘ fctr-ar ff       ~[ ∘e (fctr-ext eq₁) (fctr-ext eq₂) ] /
    fctr-ar gg' 𝕎.∘ fctr-ar ff'     ~[ fctr-cmp ff' gg' ]∎
    fctr-ar (cmp gg' ff') ∎
     where open ecategory-aux-only 𝕎
  fctr-ext emty-rfl =
    𝕎.r
  fctr-ext indv-rfl =
    𝕎.r
  fctr-ext (HomEqR-tran eq₁ eq₂) =
    fctr-ext eq₁ 𝕎.⊙ fctr-ext eq₂
  fctr-ext (HomEqR-sym eq) =
    fctr-ext eq 𝕎.ˢ
  fctr-ext iid =
    F.id
  fctr-ext (icmpext eq) =
    F.∘ax eq
  fctr-ext (⊗ext {ff = ff} {ff'} {gg} {gg'} eq₁ eq₂) = ~proof
    fctr-ar (ff ⊗ₐ gg)                   ~[ ⊗ₐeqˢ ff gg ] /
    (fctr-ar ff) 𝕎.⊗ₐ (fctr-ar gg)       ~[ 𝕎.⊗ext (fctr-ext eq₁) (fctr-ext eq₂) ] /
    (fctr-ar ff') 𝕎.⊗ₐ (fctr-ar gg')     ~[ ⊗ₐeq ff' gg' ]∎
    fctr-ar (ff' ⊗ₐ gg') ∎
    where open ecategory-aux-only 𝕎
  fctr-ext {M} {N} {ff} {ff'} (⊗sqg g₁ g₂) =
    𝕎.⊗ₐsq (fctr-ar-gen g₁) (fctr-ar-gen g₂)

  fctr-ext (α₁ M N L) =
    𝕎.⊗ass.iddom (fctr-ob N) (fctr-ob L)
  fctr-ext (α₂ M N L) =
    𝕎.⊗ass.idcod (fctr-ob N) (fctr-ob L)
  fctr-ext (Iλ₁ N) =
    𝕎.⊗lun.iddom
  fctr-ext (Iλ₂ M) =
    𝕎.⊗lun.idcod
  fctr-ext (ρI₁ N) =
    𝕎.⊗run.iddom
  fctr-ext (ρI₂ M) =
    𝕎.⊗run.idcod
  fctr-ext (αnat {M} {N} {L} {M'} {N'} {L'} ff gg hh) = ~proof
    fctr-ar (apnd ((ff ⊗ₐ gg) ⊗ₐ hh) (αg M' N' L'))
            ~[ fctr-apndˢ ((ff ⊗ₐ gg) ⊗ₐ hh) (αg M' N' L') ] /
    fctr-ar (α M' N' L') 𝕎.∘ fctr-ar ((ff ⊗ₐ gg) ⊗ₐ hh)
            ~[ ∘e (⊗ₐeqˢ (ff ⊗ₐ gg) hh ⊙ 𝕎.⊗ext (⊗ₐeqˢ ff gg) r) r ] /
    𝕎.⊗ass.fnc (fctr-ob M') (fctr-ob N') {fctr-ob L'}
                              𝕎.∘ ((fctr-ar ff 𝕎.⊗ₐ fctr-ar gg) 𝕎.⊗ₐ fctr-ar hh)
                  ~[ 𝕎.⊗ass.nat (fctr-ar ff) (fctr-ar gg) (fctr-ar hh)   ] /
    (fctr-ar ff 𝕎.⊗ₐ (fctr-ar gg 𝕎.⊗ₐ fctr-ar hh))
                              𝕎.∘ 𝕎.⊗ass.fnc (fctr-ob M) (fctr-ob N) {fctr-ob L}
                  ~[ ∘e r (𝕎.⊗ext r (⊗ₐeq gg hh) ⊙ ⊗ₐeq ff (gg ⊗ₐ hh)) ] /
    fctr-ar (ff ⊗ₐ (gg ⊗ₐ hh)) 𝕎.∘ fctr-ar (α M N L)
                  ~[ fctr-cmp (α M N L) (ff ⊗ₐ (gg ⊗ₐ hh)) ]∎
    fctr-ar ((ff ⊗ₐ (gg ⊗ₐ hh)) Fℂ.∘ α M N L) ∎
     where open ecategory-aux-only 𝕎
  fctr-ext (Iλnat ff) = ~proof
    fctr-ar (Iλ _ Fℂ.∘ (I l⊗ₐ ff))
                              ~[ fctr-apndˢ (I l⊗ₐ ff) (Iλg _) ⊙ ∘e (l⊗ₐeqˢ ff) r ] /
    𝕎.⊗lun.fnc 𝕎.∘ 𝕎.l⊗ₒ.ₐ 𝕎.I (fctr-ar ff)                    ~[ 𝕎.⊗lun.nat _ ] /
    fctr-ar ff 𝕎.∘ 𝕎.⊗lun.fnc                              ~[ fctr-cmp (Iλ _) ff ]∎
    fctr-ar (ff Fℂ.∘ Iλ _) ∎
    where open ecategory-aux-only 𝕎
  fctr-ext (ρInat ff) = ~proof
    fctr-ar (ρI _ Fℂ.∘ (ff ⊗rₐ I))
                               ~[ fctr-apndˢ (ff ⊗rₐ I) (ρIg _) ⊙ ∘e (⊗rₐeqˢ ff) r ] /
    𝕎.⊗run.fnc 𝕎.∘ 𝕎.⊗rₒ.ₐ 𝕎.I (fctr-ar ff)                     ~[ 𝕎.⊗run.nat _ ] /
    fctr-ar ff 𝕎.∘ 𝕎.⊗run.fnc                               ~[ fctr-cmp (ρI _) ff ]∎
    fctr-ar (ff Fℂ.∘ ρI _) ∎
    where open ecategory-aux-only 𝕎
  fctr-ext IλαρI = 𝕎.trng
  fctr-ext αpent = 𝕎.pntg


  fctr : efunctorₗₑᵥ (FMon ℂ) 𝕎
  fctr = record
    { FObj = fctr-ob
    ; FHom = fctr-ar
    ; isF = record
          { ext = fctr-ext
          ; id = 𝕎.r
          ; cmp = fctr-cmp
          }
    }
  private module fctr where
    open efunctor-aux fctr public
    open monoidal-functor-defs.aux (FMon-mon ℂ) 𝕎mon fctr using (F⊗F; F⊗) public


  mon-⊗rnat' : {M M₁ N₁ : Fℂ.Obj} (ff : || Fℂ.Hom M₁ N₁ ||)
           → 𝕎.idar (fctr.ₒ N₁ 𝕎.⊗ₒ fctr.ₒ M) 𝕎.∘ 𝕎.⊗rₒ.ₐ (fctr.ₒ M) (fctr.ₐ ff)
                       𝕎.~ fctr.ₐ (Fℂ.⊗rₒ.ₐ M ff) 𝕎.∘ 𝕎.idar (fctr.ₒ (M₁ ⊗ₒ M))
  mon-⊗rnat' {M} ff = mon-⊗rnat {M} ff ⊙ ∘e r (fctr.ext (Fℂ.⊗df.⊗r-is-⊗ _ ff)) 
    where open ecategory-aux-only 𝕎 using (_⊙_; ∘e; r)

  mon-⊗rnat'ˢ : {M M₁ N₁ : Fℂ.Obj} (ff : || Fℂ.Hom M₁ N₁ ||)
           → fctr.ₐ (Fℂ.⊗rₒ.ₐ M ff) 𝕎.∘ 𝕎.idar (fctr.ₒ (M₁ ⊗ₒ M))
                  𝕎.~ 𝕎.idar (fctr.ₒ N₁ 𝕎.⊗ₒ fctr.ₒ M) 𝕎.∘ 𝕎.⊗rₒ.ₐ (fctr.ₒ M) (fctr.ₐ ff)
  mon-⊗rnat'ˢ {M} ff = mon-⊗rnat' {M} ff ˢ
    where open ecategory-aux-only 𝕎 using (_ˢ)

  F⊗F≅F⊗ : natural-iso fctr.F⊗F fctr.F⊗
  F⊗F≅F⊗ = record
    { natt = record
           { fnc = λ {M} → record
                 { fnc = λ {N} → mon-⊗ar {M} {N}
                 ; nat = mon-l⊗nat }
           ; nat = λ ff _ → mon-⊗rnat' ff
           }
    ; natt⁻¹ = record
             { fnc = λ {M} → record
                   { fnc = λ {N} → 𝕎.idar _
                   ; nat = λ ff → 𝕎.iso-sq (𝕎.idar-is-isopair _) (𝕎.idar-is-isopair _)
                                            (mon-l⊗natˢ ff)  }
             ; nat = λ ff _ → 𝕎.iso-sq (𝕎.idar-is-isopair _) (𝕎.idar-is-isopair _)
                                        (mon-⊗rnat'ˢ ff)
             }
    ; isiso = record { iddom = λ _ → 𝕎.lid ; idcod = λ _ → 𝕎.lid }
    }



  module fctr-uniqueness {G : efunctorₗₑᵥ (FMon ℂ) 𝕎}
                         (monG : is-monoidal-functor G (FMon-mon ℂ) 𝕎mon)
                         (trG : G ○ FMon-emb ℂ ≅ₐ F)
                         where
    private
      module G where
        open efunctor-aux G public
        open is-monoidal-functor monG public using (Iiso; ⊗iso) renaming (pf to ismon)
        module I≅ = 𝕎._≅ₒ_ Iiso renaming (a12 to ar; a21 to ar⁻¹)
        module ⊗≅ = uncurry-nat-iso-into-functor-cat ⊗iso
        module ⊗ = monoidal-functor-defs.is-monoidal-with-isos ismon
      module trG = natural-iso trG

    ar : (M : Fℂ.Obj) → || 𝕎.Hom (G.ₒ M) (fctr.ₒ M) ||
    ar I = G.I≅.ar⁻¹
    ar (iₒ A) = trG.fnc {A}
    ar (M ⊗ₒ N) = (ar M 𝕎.⊗ₐ ar N) 𝕎.∘ G.⊗≅.⁻¹.fnc M {N}

    ar⁻¹ : (M : Fℂ.Obj) → || 𝕎.Hom (fctr.ₒ M) (G.ₒ M) ||
    ar⁻¹ I = G.I≅.ar
    ar⁻¹ (iₒ A) = trG.fnc⁻¹ {A}
    ar⁻¹ (M ⊗ₒ N) = G.⊗≅.fnc M {N} 𝕎.∘ (ar⁻¹ M 𝕎.⊗ₐ ar⁻¹ N)

    isop : (M : Fℂ.Obj) → 𝕎.is-iso-pair (ar M) (ar⁻¹ M)
    isop I = 𝕎.inv-iso-pair G.I≅.isop
    isop (iₒ A) = trG.isiso {A}
    isop (M ⊗ₒ N) = 𝕎.isopair-cmp (𝕎.inv-iso-pair (G.⊗≅.isisopair {M} {N}))
                                   (𝕎.⊗pres-iso-pair (isop M) (isop N))


    natg : {M N : Fℂ.Obj} (g : HomGen M N)
              → ar N 𝕎.∘ G.ₐ (indv g) 𝕎.~ fctr.ₐ (indv g) 𝕎.∘ ar M

    natg (iₐg f) = trG.nat _

    natg (l⊗ₐg M g) = ~proof
      ((ar M 𝕎.⊗ₐ ar _) 𝕎.∘ G.⊗≅.⁻¹.fnc M) 𝕎.∘ G.ₐ (M l⊗ₐ (indv g))
           ~[ assˢ ⊙ ∘e (∘e (lidggˢ r G.id) r ⊙ (G.⊗≅.⁻¹.nat (Fℂ.idar M) (indv g)
                          ⊙ ∘e r (lidgg r (𝕎.l⊗.ext G.id _ ⊙ 𝕎.l⊗.id {G.ₒ M} _)))) r ] /
      ((𝕎.⊗rₒ.ₐ _ (ar M)) 𝕎.∘ (𝕎.l⊗ₒ.ₐ _ (ar _)))
          𝕎.∘ 𝕎.l⊗ₒ.ₐ (G.ₒ M) (G.ₐ (indv g)) 𝕎.∘ G.⊗≅.⁻¹.fnc M
           ~[ ass ⊙ ∘e r (assˢ ⊙ ∘e (𝕎.l⊗ₒ.∘∘ (G.ₒ M) (natg g)) r
                           ⊙ (ass ⊙ ∘e r (𝕎.⊗ₐsq _ _) ⊙ assˢ)) ⊙ assˢ ]∎
      fctr.ₐ (indv (l⊗ₐg M g)) 𝕎.∘ (ar M 𝕎.⊗ₐ ar _) 𝕎.∘ G.⊗≅.⁻¹.fnc M ∎
      where open ecategory-aux-only 𝕎

    natg (⊗rₐg N g) = ~proof
      ((ar _ 𝕎.⊗ₐ ar N) 𝕎.∘ G.⊗≅.⁻¹.fnc _) 𝕎.∘ G.ₐ ((indv g) ⊗rₐ N)
           ~[ assˢ ⊙ ∘e (∘e (ridggˢ r G.id) r ⊙ (G.⊗≅.⁻¹.nat (indv g) (Fℂ.idar N))
                         ⊙ ∘e r (ridgg r (𝕎.l⊗ₒ.ext _ G.id ⊙ 𝕎.l⊗ₒ.id _))) r ] /
      ((𝕎.⊗rₒ.ₐ _ (ar _)) 𝕎.∘ (𝕎.l⊗ₒ.ₐ _ (ar N)))
          𝕎.∘ 𝕎.⊗rₒ.ₐ (G.ₒ N) (G.ₐ (indv g)) 𝕎.∘ G.⊗≅.⁻¹.fnc _
           ~[ ass ⊙ ∘e r ( assˢ ⊙ ∘e (𝕎.⊗ₐsqˢ _ _) r
                            ⊙ ass ⊙ ∘e r (𝕎.⊗rₒ.∘∘ (fctr.ₒ N) (natg g)) ⊙ assˢ ) ⊙ assˢ ]∎
      fctr.ₐ (indv (⊗rₐg N g)) 𝕎.∘ (ar _ 𝕎.⊗ₐ ar N) 𝕎.∘ G.⊗≅.⁻¹.fnc _ ∎
      where open ecategory-aux-only 𝕎

    natg (αg M N L) = ~proof
      ((ar M 𝕎.⊗ₐ ((ar N 𝕎.⊗ₐ ar L) 𝕎.∘ G.⊗≅.⁻¹.fnc N)) 𝕎.∘ G.⊗≅.⁻¹.fnc M)
             𝕎.∘ G.ₐ (α M N L)
                 ~[ ∘e r (∘e r (∘e (𝕎.l⊗ₒ.∘ax-rfˢ (G.ₒ M)) r ⊙ ass) ⊙ assˢ) ⊙ assˢ ] /
      (𝕎.⊗rₒ.ₐ _ (ar M) 𝕎.∘ 𝕎.l⊗ₒ.ₐ _ (ar N 𝕎.⊗ₐ ar L))
         𝕎.∘ (𝕎.l⊗ₒ.ₐ _ (G.⊗≅.⁻¹.fnc N) 𝕎.∘ G.⊗≅.⁻¹.fnc M) 𝕎.∘ G.ₐ (α M N L)
                                        ~[ ∘e (G.⊗.ass-eq⁻¹ ⊙ ass) (∘e (𝕎.l⊗ₒ.∘ax-rfˢ _) r)
                                           ⊙ (ass ⊙ ∘e r (assˢ ⊙ ∘e assˢ r)) ] /
      (𝕎.⊗rₒ.ₐ _ (ar M) 𝕎.∘ 𝕎.l⊗ₒ.ₐ _ (𝕎.⊗rₒ.ₐ _ (ar N)) 𝕎.∘ 𝕎.l⊗ₒ.ₐ _ (𝕎.l⊗ₒ.ₐ _ (ar L))
         𝕎.∘ 𝕎.⊗ass.fnc (G.ₒ M) (G.ₒ N) {G.ₒ L} 𝕎.∘ 𝕎.⊗rₒ.ₐ _ (G.⊗≅.⁻¹.fnc _))
                        𝕎.∘ G.⊗≅.⁻¹.fnc _
           ~[ ∘e r (~proof
         𝕎.⊗rₒ.ₐ _ (ar M) 𝕎.∘ 𝕎.l⊗ₒ.ₐ _ (𝕎.⊗rₒ.ₐ _ (ar N))
           𝕎.∘ 𝕎.l⊗ₒ.ₐ _ (𝕎.l⊗ₒ.ₐ _ (ar L)) 𝕎.∘ 𝕎.⊗ass.fnc (G.ₒ M) (G.ₒ N) {G.ₒ L}
               𝕎.∘ 𝕎.⊗rₒ.ₐ _ (G.⊗≅.⁻¹.fnc _)
         ~[ ass ⊙ ∘e (ass ⊙ ∘e r (𝕎.⊗ass.rnatˢ (G.ₒ M) (G.ₒ N) (ar L)) ⊙ assˢ) r ⊙ assˢ ] /
         𝕎.⊗rₒ.ₐ _ (ar M) 𝕎.∘ 𝕎.l⊗ₒ.ₐ _ (𝕎.⊗rₒ.ₐ _ (ar N))
           𝕎.∘ 𝕎.⊗ass.fnc (G.ₒ M) (G.ₒ N) {fctr.ₒ L}
             𝕎.∘ 𝕎.l⊗ₒ.ₐ _ (ar L) 𝕎.∘ 𝕎.⊗rₒ.ₐ _ (G.⊗≅.⁻¹.fnc _)
                 ~[ ∘e (ass ⊙ ∘e ( 𝕎.⊗ₐsqˢ _ (ar L))
                                   (𝕎.⊗ass.cnatˢ (G.ₒ M) (ar N) (fctr.ₒ L) ) ⊙ assˢ) r ] /
         𝕎.⊗rₒ.ₐ _ (ar M) 𝕎.∘ 𝕎.⊗ass.fnc (G.ₒ M) (fctr.ₒ N)
           𝕎.∘ 𝕎.⊗rₒ.ₐ _ (𝕎.l⊗ₒ.ₐ _ (ar N))
             𝕎.∘ 𝕎.⊗rₒ.ₐ _ (G.⊗≅.⁻¹.fnc _) 𝕎.∘ 𝕎.l⊗ₒ.ₐ _ (ar L)
                 ~[ ass ⊙ ∘e r (𝕎.⊗ass.lnatˢ (ar M) (fctr.ₒ N) (fctr.ₒ L)) ⊙ assˢ ] /
         𝕎.⊗ass.fnc (fctr.ₒ M) (fctr.ₒ N)
            𝕎.∘ 𝕎.⊗rₒ.ₐ _ (𝕎.⊗rₒ.ₐ _ (ar M)) 𝕎.∘ 𝕎.⊗rₒ.ₐ _ (𝕎.l⊗ₒ.ₐ _ (ar N))
              𝕎.∘ 𝕎.⊗rₒ.ₐ _ (G.⊗≅.⁻¹.fnc _)𝕎.∘ 𝕎.l⊗ₒ.ₐ _ (ar L)
                  ~[ ∘e ( ass ⊙ ∘e r (𝕎.⊗rₒ.∘ax-rf (fctr.ₒ L))
                          ⊙ (ass ⊙ ∘e r (𝕎.⊗rₒ.∘ax-rf (fctr.ₒ L))) ) r ]∎
         𝕎.⊗ass.fnc (fctr.ₒ M) (fctr.ₒ N)
            𝕎.∘ (((ar M 𝕎.⊗ₐ ar N) 𝕎.∘ G.⊗≅.⁻¹.fnc M) 𝕎.⊗ₐ ar L) ∎) ] /
      (fctr.ₐ (indv (αg M N L)) 𝕎.∘ (((ar M 𝕎.⊗ₐ ar N) 𝕎.∘ G.⊗≅.⁻¹.fnc M) 𝕎.⊗ₐ ar L))
             𝕎.∘ G.⊗≅.⁻¹.fnc (M ⊗ₒ N)
                        ~[ assˢ ]∎
      fctr.ₐ (indv (αg M N L)) 𝕎.∘ (((ar M 𝕎.⊗ₐ ar N) 𝕎.∘ G.⊗≅.⁻¹.fnc M) 𝕎.⊗ₐ ar L)
             𝕎.∘ G.⊗≅.⁻¹.fnc (M ⊗ₒ N) ∎
      where open ecategory-aux-only 𝕎
    natg (α⁻¹g M N L) =
      𝕎.iso-sqˢ (G.ᵢₛₒ αisop) (fctr.ᵢₛₒ αisop) (natg (αg M N L) ˢ)
      where open ecategory-aux-only 𝕎 using (_ˢ)
            αisop : Fℂ.is-iso-pair (α M N L) (α⁻¹ M N L)
            αisop = record { iddom = α₁ M N L ; idcod = α₂ M N L }

    natg (Iλg M) = ~proof
      ar M 𝕎.∘ G.ₐ (Iλ M)                                   ~[ ∘e G.⊗.lun-eq⁻¹ˢ r ] /
      ar M 𝕎.∘ 𝕎.⊗lun.fnc 𝕎.∘ (𝕎.⊗rₒ.ₐ _ G.I≅.ar⁻¹) 𝕎.∘ G.⊗≅.⁻¹.fnc Fℂ.I
         ~[ ass ⊙ ∘e r (𝕎.⊗lun.natˢ (ar M)) ⊙ assˢ  ] /
      𝕎.⊗lun.fnc 𝕎.∘ 𝕎.l⊗ₒ.ₐ _ (ar M) 𝕎.∘ 𝕎.⊗rₒ.ₐ _ G.I≅.ar⁻¹ 𝕎.∘ G.⊗≅.⁻¹.fnc Fℂ.I
         ~[ ∘e (ass ⊙ ∘e r (𝕎.⊗ₐsqˢ G.I≅.ar⁻¹ (ar M))) r ]∎
      fctr.ₐ (Iλ M) 𝕎.∘ (G.I≅.ar⁻¹ 𝕎.⊗ₐ ar M) 𝕎.∘ G.⊗≅.⁻¹.fnc Fℂ.I ∎
      where open ecategory-aux-only 𝕎
    natg (Iλ⁻¹g M) = 𝕎.iso-sqˢ (G.ᵢₛₒ λisop) (fctr.ᵢₛₒ λisop) (natg (Iλg M) ˢ)
      where open ecategory-aux-only 𝕎 using (_ˢ)
            λisop : Fℂ.is-iso-pair (Iλ M) (Iλ⁻¹ M)
            λisop = record { iddom = Iλ₁ M ; idcod = Iλ₂ M }

    natg (ρIg N) = ~proof
      ar N 𝕎.∘ G.ₐ (ρI N)                                 ~[ ∘e G.⊗.run-eq⁻¹ˢ r ] /
      ar N 𝕎.∘ 𝕎.⊗run.fnc 𝕎.∘ (𝕎.l⊗ₒ.ₐ _ G.I≅.ar⁻¹) 𝕎.∘ G.⊗≅.⁻¹.fnc N
         ~[ ass ⊙ ∘e r (𝕎.⊗run.natˢ (ar N)) ⊙ assˢ  ] /
      𝕎.⊗run.fnc 𝕎.∘ 𝕎.⊗rₒ.ₐ _ (ar N) 𝕎.∘ 𝕎.l⊗ₒ.ₐ _ G.I≅.ar⁻¹ 𝕎.∘ G.⊗≅.⁻¹.fnc N
         ~[ ∘e ass r ]∎
      fctr.ₐ (ρI N) 𝕎.∘ (ar N 𝕎.⊗ₐ G.I≅.ar⁻¹) 𝕎.∘ G.⊗≅.⁻¹.fnc N ∎
      where open ecategory-aux-only 𝕎
    natg (ρI⁻¹g N) = 𝕎.iso-sqˢ (G.ᵢₛₒ ρisop) (fctr.ᵢₛₒ ρisop) (natg (ρIg N) ˢ)
      where open ecategory-aux-only 𝕎 using (_ˢ)
            ρisop : Fℂ.is-iso-pair (ρI N) (ρI⁻¹ N)
            ρisop = record { iddom = ρI₁ N ; idcod = ρI₂ N }


    nat : {M N : Fℂ.Obj} (ff : || Fℂ.Hom M N ||) → ar N 𝕎.∘ G.ₐ ff 𝕎.~ fctr.ₐ ff 𝕎.∘ ar M
    nat emty = 𝕎.ridgg 𝕎.lidˢ G.id
    -- when the definition has just one clause `nat (apnd ff g)`,
    -- then `nat emty` becomes a subterm of `nat (indv g)` together with `natg g`
    nat (apnd emty g) = natg g
    nat (apnd (apnd ff g) g') = ~proof
      ar _ 𝕎.∘ G.ₐ (apnd (apnd ff g) g')
                               ~[ ∘e G.∘ax-rfˢ r ⊙ ass ⊙ ∘e r (nat (indv g')) ⊙ assˢ ] /
      fctr.ₐ (indv g') 𝕎.∘ ar _ 𝕎.∘ G.ₐ (apnd ff g)   ~[ ∘e (~proof
        ar _ 𝕎.∘ G.ₐ (apnd ff g)
                                ~[ ∘e G.∘ax-rfˢ r ⊙ ass ⊙ ∘e r (nat (indv g)) ⊙ assˢ ] /
        fctr.ₐ (indv g) 𝕎.∘ ar _ 𝕎.∘ G.ₐ ff           ~[ ∘e (nat ff) r ]∎
        fctr.ₐ (indv g) 𝕎.∘ fctr.ₐ ff 𝕎.∘ ar _ ∎) r ] /
      fctr.ₐ (indv g') 𝕎.∘ fctr.ₐ (indv g) 𝕎.∘ fctr.ₐ ff 𝕎.∘ ar _
                               ~[ ∘e (ass ⊙ ∘e r (fctr.∘ax-rf {f = ff} {indv g})) r
                                  ⊙ ass ⊙ ∘e r (fctr.∘ax-rf {f = apnd ff g} {indv g'}) ]∎
      fctr.ₐ (apnd (apnd ff g) g') 𝕎.∘ ar _ ∎
      where open ecategory-aux-only 𝕎

    natˢ : {M N : Fℂ.Obj} (ff : || Fℂ.Hom M N ||) → fctr.ₐ ff 𝕎.∘ ar M 𝕎.~ ar N 𝕎.∘ G.ₐ ff
    natˢ ff = nat ff ˢ
      where open ecategory-aux-only 𝕎 using (_ˢ)

    nat⁻¹ : {M N : Fℂ.Obj} (ff : || Fℂ.Hom M N ||)
                   → ar⁻¹ N 𝕎.∘ fctr.ₐ ff 𝕎.~ G.ₐ ff 𝕎.∘ ar⁻¹ M
    nat⁻¹ ff = 𝕎.iso-sq (isop _) (isop _) (natˢ ff)

    nat⁻¹ˢ : {M N : Fℂ.Obj} (ff : || Fℂ.Hom M N ||)
                   → G.ₐ ff 𝕎.∘ ar⁻¹ M 𝕎.~ ar⁻¹ N 𝕎.∘ fctr.ₐ ff
    nat⁻¹ˢ ff = 𝕎.iso-sqˢ (isop _) (isop _) (nat ff)


    pf : G ≅ₐ fctr
    pf = record
      { natt = record { fnc = λ {M} → ar M
                      ; nat = nat
                      }
      ; natt⁻¹ = record { fnc = λ {M} → ar⁻¹ M
                        ; nat = nat⁻¹
                        }
      ; isiso = λ {M} → isop M
      }
  -- end fctr-uniqueness


  unvprop : is-free-monoidal-on-cat-univ-prop 𝕎mon F
  unvprop = record
    { fctr = fctr
    ; tr = record { natt = record
                         { fnc = λ {A} → 𝕎.idar (F.ₒ A)
                         ; nat = λ f → 𝕎.lidgen 𝕎.ridˢ
                         }
                  ; natt⁻¹ = record
                           { fnc = λ {A} → 𝕎.idar (F.ₒ A)
                           ; nat = λ f → 𝕎.lidgen 𝕎.ridˢ
                           }
                  ; isiso = λ {A} → 𝕎.idar-is-isopair (F.ₒ A)
                  }
    ; mon =  record
          { Iiso = 𝕎.≅ₒrefl _
          ; ⊗iso = F⊗F≅F⊗
          ; pf = record
               { run-eq = λ {X} → 𝕎.ridgg 𝕎.r (𝕎.lidgen (𝕎.l⊗ₒ.id _))
               ; lun-eq = λ {X} → 𝕎.ridgg 𝕎.r (𝕎.lidgen (𝕎.⊗rₒ.id _))
               ; ass-eq = λ {X} {Y} {Z} → 𝕎.ridgg (𝕎.lidggˢ 𝕎.r (𝕎.lidgen (𝕎.l⊗ₒ.id _)))
                                                   (𝕎.lidgen (𝕎.⊗rₒ.id _))
               }
          }
    ; uq = fctr-uniqueness.pf
    }
  
-- end free-monoidal-ecat-on-ecat-is-free



free-monoidal-ecat-on-ecat-is-free : {ℓₒ₁ ℓₐ₁ ℓ~₁ : Level} (ℂ : ecategoryₗₑᵥ ℓₒ₁ ℓₐ₁ ℓ~₁)
                                     (ℓₒ' ℓₐ' ℓ~' : Level)
                         → (FMon-mon ℂ) is-free-monoidal-on-cat ℂ via (FMon-emb ℂ)
                                                                  at-lev[ ℓₒ' , ℓₐ' , ℓ~' ]
free-monoidal-ecat-on-ecat-is-free ℂ ℓₒ' ℓₐ' ℓ~' = record
  { unvp = unvprop
  }
  where open free-monoidal-ecat-on-ecat-is-free ℂ
