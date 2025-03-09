{-# OPTIONS --without-K #-}

module ecats.constructions.adjunctions where

open import tt-basics.setoids using (setoid)
open import tt-basics.basics
open import ecats.basic-defs.ecat-def&not
open import ecats.functors.defs.efunctor-d&n
open import ecats.functors.defs.basic-defs
open import ecats.functors.defs.natural-transformation
open import ecats.functors.defs.natural-iso
open import ecats.basic-defs.isomorphism
open import ecats.basic-props.isomorphism
open import ecats.functors.defs.adjunction
--open import ecats.functors.defs.monad
--open import ecats.functors.props.monad



record right-morphism-adjnct {ℓₒ₁ ℓₐ₁ ℓ~₁}{ℂ : ecategoryₗₑᵥ ℓₒ₁ ℓₐ₁ ℓ~₁}
                             {ℓₒ₂ ℓₐ₂ ℓ~₂}{𝔻 : ecategoryₗₑᵥ ℓₒ₂ ℓₐ₂ ℓ~₂}
                             (RL : adjunction-εη-btw ℂ 𝔻)
                             {ℓₒ₁' ℓₐ₁' ℓ~₁'}{ℂ' : ecategoryₗₑᵥ ℓₒ₁' ℓₐ₁' ℓ~₁'}
                             {ℓₒ₂' ℓₐ₂' ℓ~₂'}{𝔻' : ecategoryₗₑᵥ ℓₒ₂' ℓₐ₂' ℓ~₂'}
                             (RL' : adjunction-εη-btw ℂ' 𝔻')
                             : Set (ecat.ℓₐₗₗ ℂ ⊔ ecat.ℓₐₗₗ 𝔻 ⊔ ecat.ℓₐₗₗ ℂ' ⊔ ecat.ℓₐₗₗ 𝔻')
                             where
  private
    module ℂ = ecat ℂ
    module 𝔻 = ecat 𝔻
    module ℂ' = ecat ℂ'
    module 𝔻' = ecat 𝔻'
    module RL = adjunction-εη-btw RL
    module RL' = adjunction-εη-btw RL'
  field
    fc₁ : efunctorₗₑᵥ ℂ ℂ'
    fc₂ : efunctorₗₑᵥ 𝔻 𝔻'
    niso : fc₁ ○ RL.right ≅ₐ RL'.right ○ fc₂
  module fc₁ = efunctor-aux fc₁
  module fc₂ = efunctor-aux fc₂
  module ni = natural-iso niso
  ζ♯ : RL'.left ○ fc₁ ⇒ fc₂ ○ RL.left
  ζ♯ = record
    { fnc = λ {X} → RL'.εnt.ar
                          𝔻'.∘ RL'.left.ₐ (ni.ar {RL.left.ₒ _})
                               𝔻'.∘ RL'.left.ₐ (fc₁.ₐ RL.ηnt.ar)
    ; nat = λ f → ~proof
    (RL'.εnt.ar ∘ RL'.left.ₐ ni.ar ∘ RL'.left.ₐ (fc₁.ₐ RL.ηnt.ar)) ∘ RL'.left.ₐ (fc₁.ₐ f)
                               ~[ assˢ ⊙ ∘e (assˢ ⊙ ∘e (RL'.left.∘∘ (fc₁.∘∘ (RL.ηnt.nat f))) r) r ] /
    RL'.εnt.ar ∘ RL'.left.ₐ ni.ar
      ∘ RL'.left.ₐ (fc₁.ₐ (RL.right.ₐ (RL.left.ₐ f))) ∘ RL'.left.ₐ (fc₁.ₐ RL.ηnt.ar)
                                ~[ ∘e (ass ⊙ ∘e r (RL'.left.∘∘ (ni.nat (RL.left.ₐ f))) ⊙ assˢ) r ] /
    RL'.εnt.ar ∘ RL'.left.ₐ (RL'.right.ₐ (fc₂.ₐ (RL.left.ₐ f))) ∘ RL'.left.ₐ ni.ar
      ∘ RL'.left.ₐ (fc₁.ₐ RL.ηnt.ar)
                                        ~[ ass ⊙ ∘e r (RL'.εnt.nat (fc₂.ₐ (RL.left.ₐ f))) ⊙ assˢ ]∎
    fc₂.ₐ (RL.left.ₐ f) ∘ RL'.εnt.ar ∘ RL'.left.ₐ ni.ar ∘ RL'.left.ₐ (fc₁.ₐ RL.ηnt.ar) ∎
    }
    where open ecategory-aux 𝔻'


id-right-morph-adj : {ℓₒ₁ ℓₐ₁ ℓ~₁ : Level}{ℂ : ecategoryₗₑᵥ ℓₒ₁ ℓₐ₁ ℓ~₁}
                     {ℓₒ₂ ℓₐ₂ ℓ~₂ : Level}{𝔻 : ecategoryₗₑᵥ ℓₒ₂ ℓₐ₂ ℓ~₂}
                         → (RL : adjunction-εη-btw ℂ 𝔻)
                           → right-morphism-adjnct RL RL
id-right-morph-adj RL = record
  { fc₁ = IdF
  ; fc₂ = IdF
  ; niso = natiso-vcmp (≅ₐsym ○rid) (○lid)
  }


record ct&adj (ℓₒ₁ ℓₐ₁ ℓ~₁ ℓₒ₂ ℓₐ₂ ℓ~₂ : Level)
               : Set (sucₗₑᵥ (ℓₒ₁ ⊔ ℓₐ₁ ⊔ ℓ~₁ ⊔ ℓₒ₂ ⊔ ℓₐ₂ ⊔ ℓ~₂)) where
    field
      ct₁ : ecategoryₗₑᵥ ℓₒ₁ ℓₐ₁ ℓ~₁
      ct₂ : ecategoryₗₑᵥ ℓₒ₂ ℓₐ₂ ℓ~₂
      adj : adjunction-εη-btw ct₁ ct₂
    module ct₁ = ecat ct₁
    module ct₂ = ecat ct₂
    open adjunction-εη-btw adj public


module cat-adjR-def (ℓₒ₁ ℓₐ₁ ℓ~₁ ℓₒ₂ ℓₐ₂ ℓ~₂ ℓₒ₁' ℓₐ₁' ℓ~₁' ℓₒ₂' ℓₐ₂' ℓ~₂' : Level) where

  record right-morph-eq {RL : ct&adj ℓₒ₁ ℓₐ₁ ℓ~₁ ℓₒ₂ ℓₐ₂ ℓ~₂}{RL' : ct&adj ℓₒ₁' ℓₐ₁' ℓ~₁' ℓₒ₂' ℓₐ₂' ℓ~₂'}
                        (h k : right-morphism-adjnct (ct&adj.adj RL) (ct&adj.adj RL'))
                        : Set (natt-level (ct&adj.ct₁ RL) (ct&adj.ct₁ RL') ⊔ natt-level (ct&adj.ct₂ RL) (ct&adj.ct₂ RL'))
                        where
    private
      module RL = ct&adj RL
      module RL' = ct&adj RL'
      module h = right-morphism-adjnct h
      module k = right-morphism-adjnct k
    field
      ₁ : h.fc₁ ≅ₐ k.fc₁
      ₂ : h.fc₂ ≅ₐ k.fc₂
    module ₁ = natural-iso ₁
    module ₂ = natural-iso ₂
    private
      module ct₁' = ecat RL'.ct₁
    field
      sq : {X : RL.ct₂.Obj}
              → k.ni.ar {X} ct₁'.∘ ₁.ar {RL.right.ₒ X}
                        ct₁'.~ RL'.right.ₐ ₂.ar ct₁'.∘ h.ni.ar {X}
      -- h.niso : h.fc₁ ○ RL.right ≅ₐ RL'.right ○ h.fc₂
      -- k.niso : k.fc₁ ○ RL.right ≅ₐ RL'.right ○ k.fc₂

  RMorAdj : (RL : ct&adj ℓₒ₁ ℓₐ₁ ℓ~₁ ℓₒ₂ ℓₐ₂ ℓ~₂)(RL' : ct&adj ℓₒ₁' ℓₐ₁' ℓ~₁' ℓₒ₂' ℓₐ₂' ℓ~₂')
                → setoid {ct&adj.ct₁.ℓₐₗₗ RL ⊔ ct&adj.ct₁.ℓₐₗₗ RL' ⊔ ct&adj.ct₂.ℓₐₗₗ RL ⊔ ct&adj.ct₂.ℓₐₗₗ RL'}
                          {natt-level (ct&adj.ct₁ RL) (ct&adj.ct₁ RL') ⊔ natt-level (ct&adj.ct₂ RL) (ct&adj.ct₂ RL')}
  RMorAdj RL RL' = record
    { object = right-morphism-adjnct RL.adj RL'.adj
    ; _∼_ = right-morph-eq {RL} {RL'}
    ; istteqrel = record
                { refl = rfl
                ; sym = sym
                ; tra = tra
                }
    }
    where module RL = ct&adj RL
          module RL' = ct&adj RL'
          rfl : (h : right-morphism-adjnct RL.adj RL'.adj) → right-morph-eq h h
          rfl h = record
            { ₁ = ≅ₐrefl {F = h.fc₁}
            ; ₂ = ≅ₐrefl {F = h.fc₂}
            ; sq = λ {X} → lidggˢ rid RL'.right.id
            }
            where module h = right-morphism-adjnct h
                  open ecategory-aux RL'.ct₁
          sym : {h k : right-morphism-adjnct RL.adj RL'.adj}
                   → right-morph-eq h k → right-morph-eq k h
          sym {h} {k} eq = record
            { ₁ = ≅ₐsym eq.₁
            ; ₂ = ≅ₐsym eq.₂
            ; sq = λ {X} → ct₁'.iso-sqˢ eq.₁.isiso (RL'.right.ᵢₛₒ eq.₂.isiso) (eq.sq {X} ˢ)
            }
            where module h = right-morphism-adjnct h
                  module k = right-morphism-adjnct k
                  module eq = right-morph-eq eq
                  module ct₁' where
                    open ecat RL'.ct₁ public
                    open iso-defs RL'.ct₁ public
                    open iso-props RL'.ct₁ public
                  open ecategory-aux RL'.ct₁ using (_ˢ)
          tra : {h k l : right-morphism-adjnct RL.adj RL'.adj}
                → right-morph-eq h k → right-morph-eq k l → right-morph-eq h l
          tra {h} {k} {l} h~k k~l = record
            { ₁ = natiso-vcmp k~l.₁ h~k.₁
            ; ₂ = natiso-vcmp k~l.₂ h~k.₂
            ; sq = λ {X} → ~proof
            l.ni.ar ∘ k~l.₁.ar ∘ h~k.₁.ar              ~[ ass ⊙ ∘e r k~l.sq ⊙ assˢ ] /
            RL'.right.ₐ k~l.₂.ar ∘ k.ni.ar ∘ h~k.₁.ar
                                                      ~[ ∘e h~k.sq r ⊙ ass ⊙ ∘e r RL'.right.∘ax-rf ]∎
            RL'.right.ₐ (k~l.₂.ar RL'.ct₂.∘ h~k.₂.ar) ∘ h.ni.ar ∎
            }
            where module h = right-morphism-adjnct h
                  module k = right-morphism-adjnct k
                  module l = right-morphism-adjnct l
                  module h~k = right-morph-eq h~k
                  module k~l = right-morph-eq k~l
                  open ecategory-aux RL'.ct₁
-- end cat-adjR-def

AdjRₗₑᵥ : (ℓₒ₁ ℓₐ₁ ℓ~₁ ℓₒ₂ ℓₐ₂ ℓ~₂ : Level) → ecategoryₗₑᵥ (sucₗₑᵥ (ℓₒ₁ ⊔ ℓₐ₁ ⊔ ℓ~₁ ⊔ ℓₒ₂ ⊔ ℓₐ₂ ⊔ ℓ~₂))
                                                         (ℓₒ₁ ⊔ ℓₐ₁ ⊔ ℓ~₁ ⊔ ℓₒ₂ ⊔ ℓₐ₂ ⊔ ℓ~₂)
                                                         (ℓₒ₁ ⊔ ℓₐ₁ ⊔ ℓ~₁ ⊔ ℓₒ₂ ⊔ ℓₐ₂ ⊔ ℓ~₂)
AdjRₗₑᵥ ℓₒ₁ ℓₐ₁ ℓ~₁ ℓₒ₂ ℓₐ₂ ℓ~₂ = record
  { Obj = ct&adj ℓₒ₁ ℓₐ₁ ℓ~₁ ℓₒ₂ ℓₐ₂ ℓ~₂
  ; Hom = RMorAdj
  ; isecat = record
               { _∘_ = {!!}
               ; idar = λ RL → id-right-morph-adj (ct&adj.adj RL)
               ; ∘ext = {!!}
               ; lidax = {!!}
               ; ridax = {!!}
               ; assoc = {!!}
               }
  }
  where open cat-adjR-def ℓₒ₁ ℓₐ₁ ℓ~₁ ℓₒ₂ ℓₐ₂ ℓ~₂ ℓₒ₁ ℓₐ₁ ℓ~₁ ℓₒ₂ ℓₐ₂ ℓ~₂
