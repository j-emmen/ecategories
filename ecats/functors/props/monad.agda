{-# OPTIONS --without-K #-}

module ecats.functors.props.monad where

open import ecats.basic-defs.ecat-def&not
open import ecats.functors.defs.efunctor-d&n
open import ecats.functors.defs.natural-transformation
open import ecats.functors.defs.natural-iso
open import ecats.functors.defs.monad
open import ecats.functors.defs.adjunction

module monad-from-adjunction {ℓₒ₁ ℓₐ₁ ℓ~₁}{ℂ : ecategoryₗₑᵥ ℓₒ₁ ℓₐ₁ ℓ~₁}{ℓₒ₂ ℓₐ₂ ℓ~₂}
                             {𝔻 : ecategoryₗₑᵥ ℓₒ₂ ℓₐ₂ ℓ~₂}{L : efunctorₗₑᵥ ℂ 𝔻}{R : efunctorₗₑᵥ 𝔻 ℂ}
                             (L⊣R : adjunction-εη L R)
                             where
  private
    module ℂ = ecat ℂ
    module 𝔻 = ecat 𝔻
    module L = efunctor-aux L
    module R = efunctor-aux R
    module L⊣R = adjunction-εη L⊣R
    RL RL² : efunctorₗₑᵥ ℂ ℂ
    RL = R ○ L
    RL² = RL ○ RL
    module RL = efunctorₗₑᵥ (R ○ L)

  η : IdF ⇒ RL
  η = L⊣R.ηnt
  module η = natural-transformation η
  ε : L ○ R ⇒ IdF
  ε = L⊣R.εnt
  module ε = natural-transformation ε

  private
    module μaux where
      -- R○Id ≅ R
      module RId = natural-iso (○rid {F = R})
      -- R○L○R≅RL○R
      module RLR = natural-iso (○ass {F = R} {L} {R})
      -- RL○RL ≅ (RL○R)○L
      module RLRL = natural-iso (○ass {F = L} {R} {RL})
      Rε : R ○ L ○ R ⇒ R ○ IdF
      Rε = R ·ₙₜ ε
      module Rε = natural-transformation Rε
  μ : RL² ⇒ RL
  μ = (μaux.RId.natt ○ᵥ μaux.Rε ○ᵥ μaux.RLR.natt⁻¹) ₙₜ· L ○ᵥ μaux.RLRL.natt
  module μ-aux where
    open μaux public
    open natural-transformation μ public
    ~RεL : {X : ℂ.Obj} → fnc {X} ℂ.~ R.ₐ (ε.fnc {L.ₒ X})
    ~RεL {X} = ridgen (lidgen rid)
             where open ecategory-aux-only ℂ
    RεL~ : {X : ℂ.Obj} → R.ₐ (ε.fnc {L.ₒ X}) ℂ.~ fnc {X}
    RεL~ {X} = ridgenˢ (lidgenˢ ridˢ)
             where open ecategory-aux-only ℂ
  private module μ = μ-aux
  mnd-struct : is-monad-struct RL η μ
  mnd-struct = record
    { ax-Tη = λ X → ~proof
                   μ.fnc ∘ RL.ₐ η.fnc                         ~[ ∘e r μ.~RεL ] /
                   R.ₐ (ε.fnc {L.ₒ X}) ∘ RL.ₐ η.fnc           ~[ R.∘ax L⊣R.trid₁ ⊙ R.id ]∎
                   idar (RL.ₒ X) ∎
    ; ax-ηT = λ X → ~proof
            μ.fnc ∘ η.fnc {RL.ₒ X}                           ~[ ∘e r (μ.~RεL {X}) ] /
            R.ₐ (ε.fnc {L.ₒ X}) ∘ η.fnc {RL.ₒ X}             ~[ L⊣R.trid₂ ]∎
            idar (RL.ₒ X) ∎
    ; ax-μ = λ X → ~proof
           μ.fnc ∘ μ.fnc                                     ~[ ∘e μ.~RεL μ.~RεL ] /
           R.ₐ (ε.fnc {L.ₒ X}) ∘ R.ₐ (ε.fnc {L.ₒ (RL.ₒ X)})   ~[ R.∘∘ (ε.natˢ ε.fnc) ] /
           R.ₐ (ε.fnc {L.ₒ X}) ∘ RL.ₐ (R.ₐ (ε.fnc {L.ₒ X}))   ~[ ∘e (ridgenˢ (RL.ext μ.RεL~)) μ.RεL~ ]∎
           μ.fnc ∘ RL.ₐ μ.fnc ∘ RLRLRL.fnc⁻¹ ∎
    }
    where open ecategory-aux ℂ
          module RLRLRL = natural-iso (○ass {F = RL} {RL} {RL})
-- end monad-from-adjunction



adjunction2monad-on-cmp : {ℓₒ₁ ℓₐ₁ ℓ~₁ : Level}{ℂ : ecategoryₗₑᵥ ℓₒ₁ ℓₐ₁ ℓ~₁}{ℓₒ₂ ℓₐ₂ ℓ~₂ : Level}
                          {𝔻 : ecategoryₗₑᵥ ℓₒ₂ ℓₐ₂ ℓ~₂}{L : efunctorₗₑᵥ ℂ 𝔻}{R : efunctorₗₑᵥ 𝔻 ℂ}
                            → adjunction-εη L R → monad-struct-on (R ○ L)
adjunction2monad-on-cmp L⊣R = record
  { ηnt = η
  ; μnt = μ
  ; ismndstr = mnd-struct
  }
  where open monad-from-adjunction L⊣R


adjunction2monad-on-cat : {ℓₒ₁ ℓₐ₁ ℓ~₁ : Level}{ℂ : ecategoryₗₑᵥ ℓₒ₁ ℓₐ₁ ℓ~₁}{ℓₒ₂ ℓₐ₂ ℓ~₂ : Level}
                          {𝔻 : ecategoryₗₑᵥ ℓₒ₂ ℓₐ₂ ℓ~₂}{L : efunctorₗₑᵥ ℂ 𝔻}{R : efunctorₗₑᵥ 𝔻 ℂ}
                            → adjunction-εη L R → monad-on ℂ
adjunction2monad-on-cat {L = L} {R} L⊣R = record
  { fc = R ○ L
  ; ηnt = η
  ; μnt = μ
  ; ismndstr = mnd-struct
  }
  where open monad-from-adjunction L⊣R
