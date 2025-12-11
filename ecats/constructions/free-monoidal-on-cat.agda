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
open import ecats.constructions.free-ecat-on-graph
--open import ecats.constructions.free-ecat-on-refl-graph


-- when 𝕍 is free monoidal over ℂ via some ℂ → 𝕍

module free-monoidal-on-cat-defs {ℓₒ₁ ℓₐ₁ ℓ~₁ : Level} (ℂ : ecategoryₗₑᵥ ℓₒ₁ ℓₐ₁ ℓ~₁)
                                 {ℓₒ₂ ℓₐ₂ ℓ~₂ : Level} {𝕍 : ecategoryₗₑᵥ ℓₒ₂ ℓₐ₂ ℓ~₂}
                                 (𝕍mon : is-monoidal 𝕍)
                                 (J : efunctorₗₑᵥ ℂ 𝕍)
                                 where
  private
    module ℂ = ecat ℂ
    module 𝕍 where
      open ecat 𝕍 public
      open is-monoidal 𝕍mon public
    module unvprop-aux {ℓ₁' ℓ₂' ℓ₃' : Level}(𝕏 : ecategoryₗₑᵥ ℓ₁' ℓ₂' ℓ₃') where
      open ecat 𝕏 public
      open iso-defs 𝕏 public
      open iso-props 𝕏 public

  record is-free-monoidal-on-cat-univ-prop {ℓₒ₃ ℓₐ₃ ℓ~₃ : Level}{𝕎 : ecategoryₗₑᵥ ℓₒ₃ ℓₐ₃ ℓ~₃}
                                           (𝕎mon : is-monoidal 𝕎) (F : efunctorₗₑᵥ ℂ 𝕎)
                                           : Set
                                           where
    private
      module 𝕎 = ecat 𝕎


module free-monoidal-ecat-on {ℓₒ ℓₐ ℓ~ : Level}(ℂ : ecategoryₗₑᵥ ℓₒ ℓₐ ℓ~) where
  private
    module ℂ = ecat ℂ


  infix 5 _⊗ₒ_ _l⊗ₐ_ _⊗rₐ_ _⊗ₐ_

  data Obj : Set ℓₒ where
    I : Obj
    iₒ : ℂ.Obj → Obj
    _⊗ₒ_ : Obj → Obj → Obj

-- with a two-variable generator for the tensor,
-- identities seem to be needed to contruct the two-variable tensor (see below).
-- otherwise it should be possible to use left and right generators instead.
-- in this case contructing the free category on the (non-reflexive)
-- graph of generators should be enough

  -- generators for the freen monoidal structure
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
                  → HomEqR (apnd (indv (l⊗ₐg M₁ g₂)) (⊗rₐg N₂ g₁))
                            (apnd (indv (⊗rₐg M₂ g₁)) (l⊗ₐg N₁ g₂))

    -- coherence isomorphisms
    α₁ : ∀ M N L → HomEqR (apnd (indv (αg M N L)) (α⁻¹g M N L)) (id ((M ⊗ₒ N) ⊗ₒ L))
    α₂ : ∀ M N L → HomEqR (apnd (indv (α⁻¹g M N L)) (αg M N L)) (id (M ⊗ₒ (N ⊗ₒ L)))
    Iλ₁ : ∀ M → HomEqR (apnd (indv (Iλg M)) (Iλ⁻¹g M)) (id (I ⊗ₒ M))
    Iλ₂ : ∀ M → HomEqR (apnd (indv (Iλ⁻¹g M)) (Iλg M)) (id M)
    ρI₁ : ∀ M → HomEqR (apnd (indv (ρIg M)) (ρI⁻¹g M)) (id (M ⊗ₒ I))
    ρI₂ : ∀ M → HomEqR (apnd (indv (ρI⁻¹g M)) (ρIg M)) (id M)

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


free-monoidal-ecat-on-ecat-emb : {ℓₒ ℓₐ ℓ~ : Level}(ℂ : ecategoryₗₑᵥ ℓₒ ℓₐ ℓ~)
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

{-
  ⊗ext : ∀ {M₁ N₁ M₂ N₂} {ff ff' : || Fℂ.Hom M₁ N₁ ||} {gg gg' : || Fℂ.Hom M₂ N₂ ||}
                  → ff Fℂ.~ ff' → gg Fℂ.~ gg' → (ff ⊗ₐ gg) Fℂ.~ (ff' ⊗ₐ gg')
  ⊗ext {ff = ff} {ff'} {gg} {gg'} eq₁ eq₂ =
    lidˢ --⊙ ∘e r (⊗id ˢ)
         ⊙ (⊗cmpext {p₁ = ff} {gg} {Fℂ.idar _} {Fℂ.idar _} (lidgen eq₁) (lidgen eq₂))
    where open ecategory-aux-only (FMon ℂ)
-}

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

{-
  ⊗cmp emty emty ff₂ gg₂ = l⊗cmp _ ff₂ gg₂
  ⊗cmp (apnd ff₁ g₁) emty ff₂ gg₂ = ~proof
    (_ l⊗ₐ gg₂) Fℂ.∘ apnd (ff₁ ⊗ₐ ff₂) (⊗rₐg _ g₁)
                    ~[ ass {f = ff₁ ⊗ₐ ff₂} {indv g₁ ⊗rₐ _} {_ l⊗ₐ gg₂}
                       ⊙ ∘e r (⊗sqgl g₁ gg₂ ˢ)
                       ⊙ assˢ {f = ff₁ ⊗ₐ ff₂} {_ l⊗ₐ gg₂} {indv g₁ ⊗rₐ _} ] /
    (indv g₁ ⊗rₐ _) Fℂ.∘ (emty ⊗ₐ gg₂) Fℂ.∘ (ff₁ ⊗ₐ ff₂)
                    ~[ ∘e (⊗cmp ff₁ emty ff₂ gg₂) r ]∎
    apnd (ff₁ ⊗ₐ (gg₂ Fℂ.∘ ff₂)) (⊗rₐg _ g₁) ∎
    where open ecategory-aux-only (FMon ℂ)
  ⊗cmp emty (apnd gg₁ g₁') ff₂ gg₂ = ~proof
    (apnd gg₁ g₁' ⊗ₐ gg₂) Fℂ.∘ (_ l⊗ₐ ff₂)
          ~[ assˢ {f = emty ⊗ₐ ff₂} {gg₁ ⊗ₐ gg₂} {indv g₁' ⊗rₐ _} ] /
    (indv g₁' ⊗rₐ _) Fℂ.∘ (gg₁ ⊗ₐ gg₂) Fℂ.∘ (_ l⊗ₐ ff₂)
          ~[ ∘e (⊗cmp emty gg₁ ff₂ gg₂) r ] /
    (indv g₁' ⊗rₐ _) Fℂ.∘ ((gg₁ Fℂ.∘ Fℂ.idar _) ⊗ₐ (gg₂ Fℂ.∘ ff₂))
          ~[ ⊗ext (ass {f = emty} {gg₁} {indv g₁'}) r ]∎
    (apnd gg₁ g₁' Fℂ.∘ Fℂ.idar _) ⊗ₐ (gg₂ Fℂ.∘ ff₂) ∎
    where open ecategory-aux-only (FMon ℂ)
  ⊗cmp (apnd ff₁ g₁) (apnd gg₁ g₁') ff₂ gg₂ =  ~proof
    (apnd gg₁ g₁' ⊗ₐ gg₂) Fℂ.∘ (apnd ff₁ g₁ ⊗ₐ ff₂)
      ~[ ∘e (~proof
      (gg₁ ⊗ₐ gg₂) Fℂ.∘ (apnd ff₁ g₁ ⊗ₐ ff₂)
           ~[ ∘e r (⊗ₐ-as-rl gg₁ gg₂)
              ⊙ assˢ {f = apnd ff₁ g₁ ⊗ₐ ff₂} {_ l⊗ₐ gg₂} {gg₁ ⊗rₐ _} ] /
      (gg₁ ⊗rₐ _) Fℂ.∘ (_ l⊗ₐ gg₂) Fℂ.∘ (indv g₁ ⊗rₐ _) Fℂ.∘ (ff₁ ⊗ₐ ff₂)
               ~[ ∘e (ass {f = ff₁ ⊗ₐ ff₂} {indv g₁ ⊗rₐ _} {_ l⊗ₐ gg₂}
                     ⊙ ∘e r (⊗ₐsqˢ (indv g₁) gg₂)
                     ⊙ assˢ {f = ff₁ ⊗ₐ ff₂} {_ l⊗ₐ gg₂} {indv g₁ ⊗rₐ _}) r ] /
      (gg₁ ⊗rₐ _) Fℂ.∘ (indv g₁ ⊗rₐ _) Fℂ.∘ (_ l⊗ₐ gg₂) Fℂ.∘ (ff₁ ⊗ₐ ff₂)
           ~[ ass {f = (_ l⊗ₐ gg₂) Fℂ.∘ (ff₁ ⊗ₐ ff₂)} {indv g₁ ⊗rₐ _} {gg₁ ⊗rₐ _}
              ⊙ ∘e (⊗cmp ff₁ emty ff₂ gg₂) (⊗rcmp _ (indv g₁) gg₁) ] /
      ((gg₁ Fℂ.∘ indv g₁) ⊗rₐ _) Fℂ.∘ (ff₁ ⊗ₐ (gg₂ Fℂ.∘ ff₂))
           ~[ ∘e r (⊗r-is-⊗ _ (gg₁ Fℂ.∘ indv g₁))
              ⊙ ⊗cmp ff₁ (gg₁ Fℂ.∘ indv g₁) (gg₂ Fℂ.∘ ff₂) emty ]∎
      ((gg₁ Fℂ.∘ indv g₁) Fℂ.∘ ff₁) ⊗ₐ (gg₂ Fℂ.∘ ff₂) ∎) r ] /
    (indv g₁' Fℂ.∘ (gg₁ Fℂ.∘ indv g₁)  Fℂ.∘ ff₁) ⊗ₐ (gg₂ Fℂ.∘ ff₂)
      ~[ ⊗ext (∘e (assˢ {f = ff₁} {indv g₁} {gg₁}) (r {f = indv g₁'})
                ⊙ ass {f = apnd ff₁ g₁} {gg₁} {indv g₁'})
               r ]∎
    (apnd gg₁ g₁' Fℂ.∘ apnd ff₁ g₁) ⊗ₐ (gg₂ Fℂ.∘ ff₂) ∎
-}

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



F⊗ free-monoidal-ecat-on-ecat-tensor : {ℓₒ ℓₐ ℓ~ : Level}(ℂ : ecategoryₗₑᵥ ℓₒ ℓₐ ℓ~)
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
F⊗ = free-monoidal-ecat-on-ecat-tensor



module free-monoidal-ecat-on-ecat-is-monoidal {ℓₒ ℓₐ ℓ~ : Level}(ℂ : ecategoryₗₑᵥ ℓₒ ℓₐ ℓ~)
                                              where
  private
    module ℂ = ecat ℂ
    module Fℂ where
      open ecat (FMon ℂ) public
      open iso-d&p (FMon ℂ) public
  open monoidal-defs (FMon ℂ)
  open free-monoidal-ecat-on ℂ
  open tensor-efunctor-not (F⊗ ℂ) hiding (_⊗ₒ_; _⊗ₐ_)
                                  renaming (⊗ass-lfst to F⊗ass-l; ⊗ass-llst to F⊗ass-r)
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
    module F⊗ass-l = efctr F⊗ass-l
    module F⊗ass-r = efctr F⊗ass-r

  ass-iso : (M N L : Fℂ.Obj) → Fℂ.is-iso-pair (α M N L) (α⁻¹ M N L)
  ass-iso M N L = record
    { iddom = α₁ M N L
    ; idcod = α₂ M N L
    }
  module ass-iso (M N L : Fℂ.Obj) = Fℂ.is-iso-pair (ass-iso M N L)

  ass-fst-nat : (M : Fℂ.Obj) → F⊗ass-l.ₒ M ⇒ F⊗ass-r.ₒ M
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

  ass-fst-nat⁻¹ : (M : Fℂ.Obj) → F⊗ass-r.ₒ M ⇒ F⊗ass-l.ₒ M
  ass-fst-nat⁻¹ M = record
    { fnc = λ {N} → record { fnc = λ {L} → α⁻¹ M N L
                            ; nat = λ f → Fℂ.iso-sq (ass-iso M N _) (ass-iso M N _)
                                                    (ass-fst-nat.snd.nat M N f) }
    ; nat = λ f L → Fℂ.iso-sq (ass-iso M _ L) (ass-iso M _ L)
                               (ass-fst-nat.nat M f L)
    }
    where
      open ecategory-aux-only (FMon ℂ)

  ass-nat : F⊗ass-l ⇒ F⊗ass-r
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
    

  F⊗-is-tensor : is-tensor-with-unit I (F⊗ ℂ)
  F⊗-is-tensor = record
    { lun = record
          { natt = lun-nat
          ; natt⁻¹ = record { fnc = λ {M} → Iλ⁻¹ M
                            ; nat = λ f → Fℂ.iso-sq lun-iso lun-iso (lun-nat.nat f) }
          ; isiso = lun-iso
          }
    ; run = record
          { natt = run-nat
          ; natt⁻¹ = record { fnc = λ {M} → ρI⁻¹ M
                            ; nat = λ f → Fℂ.iso-sq run-iso run-iso (run-nat.nat f) }
          ; isiso = run-iso
          }
    ; ass = record
          { natt = ass-nat
          ; natt⁻¹ = record { fnc = λ {M} → ass-fst-nat⁻¹ M
                            ; nat = λ f N L → Fℂ.iso-sq (ass-iso _ N L) (ass-iso _ N L)
                                                         (ass.nat₁ f N L) }
          ; isiso = λ {M} → record { iddom = ass-iso.iddom M
                                   ; idcod = ass-iso.idcod M }
          }
    ; trng = IλαρI
    ; pntg = αpent
    }
-- end free-monoidal-ecat-on-ecat-is-monoidal



free-monoidal-ecat-on-ecat-is-monoidal : {ℓₒ ℓₐ ℓ~ : Level}(ℂ : ecategoryₗₑᵥ ℓₒ ℓₐ ℓ~)
                                             → is-monoidal (FMon ℂ)
free-monoidal-ecat-on-ecat-is-monoidal ℂ = record
  { I = I
  ; tenf = F⊗ ℂ
  ; pf = F⊗-is-tensor
  }
  where
      open free-monoidal-ecat-on ℂ using (I)
      open free-monoidal-ecat-on-ecat-is-monoidal ℂ using (F⊗-is-tensor)
