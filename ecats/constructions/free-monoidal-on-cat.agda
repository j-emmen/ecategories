{-# OPTIONS --without-K #-}

module ecats.constructions.free-monoidal-on-cat where 

open import tt-basics.setoids hiding (||_||)
open import ecats.basic-defs.ecat-def&not
open import ecats.functors.defs.efunctor-d&n
open import ecats.functors.defs.natural-transformation
open import ecats.functors.defs.natural-iso
open import ecats.concr-ecats.ecat-ecats
open import ecats.constructions.functor-ecat
open import ecats.basic-defs.monoidal
open import ecats.constructions.free-ecat-on-graph



module free-monoidal-on {ℓₒ ℓₐ ℓ~ : Level}(ℂ : ecategoryₗₑᵥ ℓₒ ℓₐ ℓ~) where
  private
    module ℂ = ecat ℂ


  infix 10 _⊗ₒ_ _⊗ₐ_

  data Obj : Set ℓₒ where
    I : Obj
    iₒ : ℂ.Obj → Obj
    _⊗ₒ_ : Obj → Obj → Obj

  data HomGen : Obj → Obj → Set (ℓₒ ⊔ ℓₐ) where
    id : ∀ {M} → HomGen M M
    iₐg : ∀ {A B} → || ℂ.Hom A B || → HomGen (iₒ A) (iₒ B)
    _⊗ₐg_ : ∀ {M₁ N₁ M₂ N₂} → HomGen M₁ N₁ → HomGen M₂ N₂
             → HomGen (M₁ ⊗ₒ M₂) (N₁ ⊗ₒ M₂)
    αg : ∀ M N L → HomGen ((M ⊗ₒ N) ⊗ₒ L) (M ⊗ₒ (N ⊗ₒ L))
    α⁻¹g : ∀ M N L → HomGen (M ⊗ₒ (N ⊗ₒ L)) ((M ⊗ₒ N) ⊗ₒ L)
    Iλg : ∀ M → HomGen (I ⊗ₒ M) M
    Iλ⁻¹g : ∀ M → HomGen M (I ⊗ₒ M)
    ρIg : ∀ M → HomGen (M ⊗ₒ I) M
    ρI⁻¹g : ∀ M → HomGen M (M ⊗ₒ I)

  HomGen-freestd : Obj → Obj → setoid {ℓₒ ⊔ ℓₐ} {ℓₒ ⊔ ℓₐ}
  HomGen-freestd M N = Freestd (HomGen M N)
  module fc = free-ecat-on-graph-via-inductive-paths HomGen-freestd
       --using (fin-path; path-cmp; path-cmp-ext; path-rid; path-ass)

  iₐ : ∀ {A B} → || ℂ.Hom A B || → fc.fin-path (iₒ A) (iₒ B)
  iₐ f = fc.indv (iₐg f)
  --id : ∀ {M} → fc.fin-path M M
  --id = fc.emty
  α : ∀ M N L → fc.fin-path ((M ⊗ₒ N) ⊗ₒ L) (M ⊗ₒ (N ⊗ₒ L))
  α M N L = fc.indv (αg M N L)
  α⁻¹ : ∀ M N L → fc.fin-path (M ⊗ₒ (N ⊗ₒ L)) ((M ⊗ₒ N) ⊗ₒ L)
  α⁻¹ M N L = fc.indv (α⁻¹g M N L)
  Iλ : ∀ M → fc.fin-path (I ⊗ₒ M) M
  Iλ M = fc.indv (Iλg M)
  Iλ⁻¹ : ∀ M → fc.fin-path M (I ⊗ₒ M)
  Iλ⁻¹ M = fc.indv (Iλ⁻¹g M)
  ρI : ∀ M → fc.fin-path (M ⊗ₒ I) M
  ρI M = fc.indv (ρIg M)
  ρI⁻¹ : ∀ M → fc.fin-path M (M ⊗ₒ I)
  ρI⁻¹ M = fc.indv (ρI⁻¹g M)

{-
  _⊗ₐlg_ : ∀ {M₁ N₁ M₂ N₂} → HomGen M₁ N₁ → fc.fin-path M₂ N₂ → fc.fin-path (M₁ ⊗ₒ M₂) (N₁ ⊗ₒ N₂)
  iₐg x ⊗ₐlg fc.emty = {!!}
  (g ⊗ₐg g₁) ⊗ₐlg fc.emty = {!!}
  αg M N L ⊗ₐlg fc.emty = {!!}
  α⁻¹g M N L ⊗ₐlg fc.emty = {!!}
  Iλg _ ⊗ₐlg fc.emty = {!!}
  Iλ⁻¹g _ ⊗ₐlg fc.emty = {!!}
  ρIg _ ⊗ₐlg fc.emty = {!!}
  ρI⁻¹g _ ⊗ₐlg fc.emty = {!!}
  g ⊗ₐlg fc.apnd ff x = {!!}
-}

  _⊗ₐ_ : ∀ {M₁ N₁ M₂ N₂} → fc.fin-path M₁ N₁ → fc.fin-path M₂ N₂ → fc.fin-path (M₁ ⊗ₒ M₂) (N₁ ⊗ₒ N₂)
  fc.emty ⊗ₐ fc.emty = fc.emty
  fc.apnd ff e ⊗ₐ fc.emty = fc.path-cmp (fc.indv e ⊗ₐ id) (ff ⊗ₐ id)
  fc.emty ⊗ₐ fc.apnd gg e = {!fc.path-cmp (fc.emty ⊗ₐ fc.indv e) (fc.emty ⊗ₐ )!}
  fc.apnd ff x ⊗ₐ fc.apnd gg e = {!!}

  data HomEqR : {M N : Obj} → fc.fin-path M N → fc.fin-path M N → Set (ℓₒ ⊔ ℓₐ) where
    -- coherence isomorphisms
    α₁ : ∀ M N L → HomEqR (fc.twocmp (αg M N L) (α⁻¹g M N L)) id
    α₂ : ∀ M N L → HomEqR (fc.twocmp (α⁻¹g M N L) (αg M N L)) id
    Iλ₁ : ∀ M → HomEqR (fc.twocmp (Iλg M) (Iλ⁻¹g M)) id
    Iλ₂ : ∀ M → HomEqR (fc.twocmp (Iλ⁻¹g M) (Iλg M)) id
    Iρ₁ : ∀ M → HomEqR (fc.twocmp (ρIg M) (ρI⁻¹g M)) id
    Iρ₂ : ∀ M → HomEqR (fc.twocmp (ρI⁻¹g M) (ρIg M)) id
    -- their naturality
    αnat : ∀ {M N L M' N' L'}
             (ff : fc.fin-path M M') (gg : fc.fin-path N N') (hh : fc.fin-path L L')
                → HomEqR (fc.path-cmp (α M' N' L') ((ff ⊗ₐ gg) ⊗ₐ hh))
                         (fc.path-cmp (ff ⊗ₐ (gg ⊗ₐ hh)) (α M N L))
    Iλnat : ∀ {M M'}
              (ff : fc.fin-path M M')
                → HomEqR (fc.path-cmp (Iλ M') (id ⊗ₐ ff))
                         (fc.path-cmp ff (Iλ M))
    ρInat : ∀ {M M'}
              (ff : fc.fin-path M M')
                  → HomEqR (fc.path-cmp (ρI M') (ff ⊗ₐ id))
                           (fc.path-cmp ff (ρI M))
    -- the triangle
    IλαρI : ∀ {M N} → HomEqR (fc.path-cmp (id ⊗ₐ Iλ N) (α M I N)) (ρI M ⊗ₐ id)
    -- the penthagon
    αpent : ∀ {M N L O} → HomEqR (fc.path-cmp (id ⊗ₐ α N L O)
                                           (fc.path-cmp (α M (N ⊗ₒ L) O) (α M N L ⊗ₐ id)))
                                  (fc.path-cmp (α M N (L ⊗ₒ O)) (α (M ⊗ₒ N) L O))
    -- functoriality of i
    iid : ∀ {A} → HomEqR (iₐ (ℂ.idar A)) (id {iₒ A})


  fMonHStd : {M N : Obj} → fc.fin-path M N → fc.fin-path M N → Set
  fMonHStd {M} {N} ff fc.emty = {!!}
  fMonHStd {M} {N} ff (fc.apnd ff' x) = {!!}

  fMonHom : Obj → Obj → setoid {ℓₒ ⊔ ℓₐ} {ℓₒ ⊔ ℓₐ}
  fMonHom M I = {!!}
  fMonHom M (iₒ x) = {!!}
  fMonHom M (N ⊗ₒ N₁) = {!!}

  
