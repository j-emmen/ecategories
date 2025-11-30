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
open import ecats.constructions.free-ecat-on-refl-graph



module free-monoidal-ecat-on {ℓₒ ℓₐ ℓ~ : Level}(ℂ : ecategoryₗₑᵥ ℓₒ ℓₐ ℓ~) where
  private
    module ℂ = ecat ℂ


  infix 5 _⊗ₒ_ _⊗ₐg_ _⊗ₐ_

  data Obj : Set ℓₒ where
    I : Obj
    iₒ : ℂ.Obj → Obj
    _⊗ₒ_ : Obj → Obj → Obj

-- with a two-variable generator for the tensor,
-- identities seem to be needed to contruct the two-variable tensor (see below).
-- otherwise it should be possible to use left and right generators instead.
-- in this case contructing the free category on the (non-reflexive)
-- graph of generators should be enough
  data HomGen : Obj → Obj → Set (ℓₒ ⊔ ℓₐ) where
    idg : ∀ {M} → HomGen M M
    iₐg : ∀ {A B} → || ℂ.Hom A B || → HomGen (iₒ A) (iₒ B)
    _⊗ₐg_ : ∀ {M₁ N₁ M₂ N₂} → HomGen M₁ N₁ → HomGen M₂ N₂
             → HomGen (M₁ ⊗ₒ M₂) (N₁ ⊗ₒ N₂)
    αg : ∀ M N L → HomGen ((M ⊗ₒ N) ⊗ₒ L) (M ⊗ₒ (N ⊗ₒ L))
    α⁻¹g : ∀ M N L → HomGen (M ⊗ₒ (N ⊗ₒ L)) ((M ⊗ₒ N) ⊗ₒ L)
    Iλg : ∀ M → HomGen (I ⊗ₒ M) M
    Iλ⁻¹g : ∀ M → HomGen M (I ⊗ₒ M)
    ρIg : ∀ M → HomGen (M ⊗ₒ I) M
    ρI⁻¹g : ∀ M → HomGen M (M ⊗ₒ I)

  HomGen-freestd : Obj → Obj → setoid {ℓₒ ⊔ ℓₐ} {ℓₒ ⊔ ℓₐ}
  HomGen-freestd M N = Freestd (HomGen M N)

  open free-ecat-on-refl-graph-via-inductive-paths HomGen-freestd idg public
       using (indv; apnd) renaming (fin-path₀ to HomObj; path₀-cmp to cmp) 


  iₐ : ∀ {A B} → || ℂ.Hom A B || → HomObj (iₒ A) (iₒ B)
  iₐ f = indv (iₐg f)
  id : ∀ M → HomObj M M
  id M = indv (idg {M})
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
  _⊗ₐ_ : ∀ {M₁ N₁ M₂ N₂} → HomObj M₁ N₁ → HomObj M₂ N₂ → HomObj (M₁ ⊗ₒ M₂) (N₁ ⊗ₒ N₂)
  indv g ⊗ₐ indv g' = indv (g ⊗ₐg g')
  indv g ⊗ₐ apnd q g' = apnd (indv g ⊗ₐ q) (idg ⊗ₐg g')
  -- in this way ⊗ₐ further reduces as soon as p or q are canonical
  apnd p g ⊗ₐ indv g' = apnd (p ⊗ₐ indv g') (g ⊗ₐg idg) 
  apnd p g ⊗ₐ apnd q g' = apnd (p ⊗ₐ q) (g ⊗ₐg g')


  data HomEqR : {M N : Obj} → HomObj M N → HomObj M N → Set ℂ.ℓₐₗₗ where
    -- category with the generator idg as unit of concatenation
    cmp-ext : {M N L : Obj} {p p' : HomObj M L}{q q' : HomObj L N}
                  → HomEqR p p' → HomEqR q q' → HomEqR (cmp q p) (cmp q' p')
    apnd-lun : {M N : Obj} {p : HomObj M N}
                   → HomEqR (apnd p (idg {N})) p
    apnd-run : {M N : Obj} {g : HomGen M N}
                     → HomEqR (apnd (id M) g) (indv g)

    -- equivalence relation
    indv-rfl : ∀ {M N} (g : HomGen M N) → HomEqR (indv g) (indv g)
    HomEqR-tran : {M N : Obj} {p₁ p₂ p₃ : HomObj M N}
                    → HomEqR p₁ p₂ → HomEqR p₂ p₃ → HomEqR p₁ p₃
    HomEqR-sym :{M N : Obj} {p₁ p₂ : HomObj M N}
                  → HomEqR p₁ p₂ → HomEqR p₂ p₁

    -- functoriality of i
    iid : ∀ {A} → HomEqR (iₐ (ℂ.idar A)) (id (iₒ A))
    icmpext : ∀ {A B C} {f : || ℂ.Hom A B ||} {g : || ℂ.Hom B C ||} {h : || ℂ.Hom A C ||}
                → g ℂ.∘ f ℂ.~ h → HomEqR (cmp (iₐ g) (iₐ f)) (iₐ h)

    -- functoriality of ⊗
    ⊗id : ∀ {M N} → HomEqR (id M ⊗ₐ id N) (id (M ⊗ₒ N))
    ⊗cmpext : ∀ {M₁ N₁ M₂ N₂ L₁ L₂} {p₁ : HomObj M₁ N₁} {p₂ : HomObj M₂ N₂} {q₁ : HomObj N₁ L₁}
                 {q₂ : HomObj N₂ L₂} {r₁ : HomObj M₁ L₁} {r₂ : HomObj M₂ L₂}
                   → HomEqR (cmp q₁ p₁) r₁ → HomEqR (cmp q₂ p₂) r₂
                     → HomEqR (cmp (q₁ ⊗ₐ q₂) (p₁ ⊗ₐ p₂)) (r₁ ⊗ₐ r₂)

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
    Iλnat : ∀ {M M'}
              (ff : HomObj M M')
                → HomEqR (cmp (Iλ M') (id I ⊗ₐ ff))
                         (cmp ff (Iλ M))
    ρInat : ∀ {M M'}
              (ff : HomObj M M')
                  → HomEqR (cmp (ρI M') (ff ⊗ₐ id I))
                           (cmp ff (ρI M))

    -- the triangle
    IλαρI : ∀ {M N} → HomEqR (cmp (id M ⊗ₐ Iλ N) (α M I N)) (ρI M ⊗ₐ id N)
    -- the penthagon
    αpent : ∀ {M N L O} → HomEqR (cmp (id M ⊗ₐ α N L O)
                                         (cmp (α M (N ⊗ₒ L) O) (α M N L ⊗ₐ id O)))
                                  (cmp (α M N (L ⊗ₒ O)) (α (M ⊗ₒ N) L O))
  -- end HomEqR


  apnd-eq : {M N L : Obj} {p₁ p₂ : HomObj M N}
                  → HomEqR p₁ p₂ → (g : HomGen N L) → HomEqR (apnd p₁ g) (apnd p₂ g)
  apnd-eq eq g = cmp-ext eq (indv-rfl g)


  module cat-data where
    HomEqR-refl : {M N : Obj}(p : HomObj M N) → HomEqR p p
    HomEqR-refl (indv g) = indv-rfl g
    HomEqR-refl (apnd p g) = apnd-eq (HomEqR-refl p) g

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
    cmp-rid (indv g) = apnd-run
    cmp-rid (apnd p g) = apnd-eq (cmp-rid p) g

    cmp-lid : {M N : Obj} (p : HomObj M N) → HomEqR (cmp (id N) p) p
    cmp-lid p = apnd-lun

    cmp-ass : {M N L O : Obj}(p₁ : HomObj M N)(p₂ : HomObj N L)(p₃ : HomObj L O)
                  → HomEqR (cmp p₃ (cmp p₂ p₁))
                            (cmp (cmp p₃ p₂) p₁)
    cmp-ass p₁ p₂ (indv g) = HomEqR-refl _
    cmp-ass p₁ p₂ (apnd p₃ g) = apnd-eq (cmp-ass p₁ p₂ p₃) g
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
    module Fℂ = ecat (FMon ℂ)
  open free-monoidal-ecat-on ℂ

  ⊗cmp : ∀ {M₁ N₁ L₁ M₂ N₂ L₂} (ff₁ : || Fℂ.Hom M₁ N₁ ||) (gg₁ : || Fℂ.Hom N₁ L₁ ||)
              (ff₂ : || Fℂ.Hom M₂ N₂ ||) (gg₂ : || Fℂ.Hom N₂ L₂ ||)
                → (gg₁ ⊗ₐ gg₂) Fℂ.∘ (ff₁ ⊗ₐ ff₂) Fℂ.~ (gg₁ Fℂ.∘ ff₁) ⊗ₐ (gg₂ Fℂ.∘ ff₂)
  ⊗cmp ff₁ gg₁ ff₂ gg₂ = ⊗cmpext r r
    where open ecategory-aux-only (FMon ℂ) using (r)

  ⊗cmpˢ : ∀ {M₁ N₁ L₁ M₂ N₂ L₂} (ff₁ : || Fℂ.Hom M₁ N₁ ||) (gg₁ : || Fℂ.Hom N₁ L₁ ||)
              (ff₂ : || Fℂ.Hom M₂ N₂ ||) (gg₂ : || Fℂ.Hom N₂ L₂ ||)
                → (gg₁ Fℂ.∘ ff₁) ⊗ₐ (gg₂ Fℂ.∘ ff₂) Fℂ.~ (gg₁ ⊗ₐ gg₂) Fℂ.∘ (ff₁ ⊗ₐ ff₂)
  ⊗cmpˢ ff₁ gg₁ ff₂ gg₂ = ⊗cmp ff₁ gg₁ ff₂ gg₂ ˢ
    where open ecategory-aux-only (FMon ℂ) using (_ˢ)

  ⊗ext : ∀ {M₁ N₁ M₂ N₂} {p p' : || Fℂ.Hom M₁ N₁ ||} {q q' : || Fℂ.Hom M₂ N₂ ||}
                  → p Fℂ.~ p' → q Fℂ.~ q' → (p ⊗ₐ q) Fℂ.~ (p' ⊗ₐ q')
  ⊗ext {p = p} {p'} {q} {q'} eq₁ eq₂ =
    lidˢ ⊙ ∘e r (⊗id ˢ)
         ⊙ (⊗cmpext {p₁ = p} {q} {Fℂ.idar _} {Fℂ.idar _} (lidgen eq₁) (lidgen eq₂))
    where open ecategory-aux-only (FMon ℂ)

  ⊗extˢ : ∀ {M₁ N₁ M₂ N₂} {p p' : || Fℂ.Hom M₁ N₁ ||} {q q' : || Fℂ.Hom M₂ N₂ ||}
                  → p Fℂ.~ p' → q Fℂ.~ q' → p' ⊗ₐ q' Fℂ.~ p ⊗ₐ q
  ⊗extˢ eq₁ eq₂ = ⊗ext eq₁ eq₂ ˢ
    where open ecategory-aux-only (FMon ℂ) using (_ˢ)

  ⊗∘∘ : ∀ {M₁ N₁ N₁' L₁ M₂ N₂ N₂' L₂} {ff₁ : || Fℂ.Hom M₁ N₁ ||} {gg₁ : || Fℂ.Hom N₁ L₁ ||}
           {ff₂ : || Fℂ.Hom M₂ N₂ ||} {gg₂ : || Fℂ.Hom N₂ L₂ ||}
           {kk₁ : || Fℂ.Hom M₁ N₁' ||} {hh₁ : || Fℂ.Hom N₁' L₁ ||}
           {kk₂ : || Fℂ.Hom M₂ N₂' ||} {hh₂ : || Fℂ.Hom N₂' L₂ ||}
                → gg₁ Fℂ.∘ ff₁ Fℂ.~ hh₁ Fℂ.∘ kk₁ → gg₂ Fℂ.∘ ff₂ Fℂ.~ hh₂ Fℂ.∘ kk₂
                  → (gg₁ ⊗ₐ gg₂) Fℂ.∘ (ff₁ ⊗ₐ ff₂) Fℂ.~ (hh₁ ⊗ₐ hh₂) Fℂ.∘ (kk₁ ⊗ₐ kk₂)
  ⊗∘∘ eq₁ eq₂ = ⊗cmpext eq₁ eq₂ ⊙ ⊗cmpˢ _ _ _ _
    where open ecategory-aux-only (FMon ℂ) using (_⊙_)

  module functor-data where
    l⊗ₒ : Fℂ.Obj → efunctor (FMon ℂ) (FMon ℂ)
    l⊗ₒ M = record
      { FObj = M ⊗ₒ_
      ; FHom = λ f → Fℂ.idar M ⊗ₐ f
      ; isF = record
            { ext = ⊗ext r
            ; id = ⊗id
            ; cmp = λ _ _ → ⊗cmpext lid r
            }
      }
      where open ecategory-aux-only (FMon ℂ) using (r; lid)
    module l⊗ₒ (M : Fℂ.Obj) = efctr (l⊗ₒ M)

    l⊗ₐ : {M N : Fℂ.Obj} → || Fℂ.Hom M N || → (l⊗ₒ M) ⇒ (l⊗ₒ N)
    l⊗ₐ {M} {N} ff = record
      { fnc = λ {X} → ff ⊗ₐ Fℂ.idar X
      ; nat = λ _ → ⊗∘∘ (rid ⊙ lidˢ) (lid ⊙ ridˢ)
      }
      where
        open ecategory-aux-only (FMon ℂ)
  -- end functor-data
-- end tensor-functor-for-free-monoidal-ecat-on



F⊗ free-monoidal-ecat-on-ecat-tensor : {ℓₒ ℓₐ ℓ~ : Level}(ℂ : ecategoryₗₑᵥ ℓₒ ℓₐ ℓ~)
                                              → efunctorₗₑᵥ (FMon ℂ) [ FMon ℂ , FMon ℂ ]ᶜᵃᵗ
free-monoidal-ecat-on-ecat-tensor ℂ = record
  { FObj = l⊗ₒ
  ; FHom = l⊗ₐ
  ; isF = record
        { ext = λ eq _ → ⊗ext eq r
        ; id = λ _ → ⊗id
        ; cmp = λ _ _ _ → ⊗cmpext r lid
        }
  }
  where
    open free-monoidal-ecat-on ℂ using (⊗id; ⊗cmpext)
    open tensor-functor-for-free-monoidal-ecat-on ℂ using (⊗ext)
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
  --module F⊗ = fst
  open tensor-functor-for-free-monoidal-ecat-on ℂ

  lun-nat : l⊗ I ⇒ IdF
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

  run-nat : ⊗r I ⇒ IdF
  run-nat = record
    { fnc = λ {M} → ρI M
    ; nat = ρInat
    }
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
                            ; nat = λ f → ∘e (⊗ext (⊗id ˢ) (r {f = f})) (r {f = α M N _})
                                          ⊙ αnat (Fℂ.idar M) (Fℂ.idar N) f }
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
                      ⊙ ∘e (r {f = α _ N L}) (⊗ext (r {f = f}) ⊗id)
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
