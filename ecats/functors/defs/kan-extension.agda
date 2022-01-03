{-# OPTIONS --without-K #-}

module ecats.functors.defs.kan-extension where

open import tt-basics.basics using (prod; pair)
open import tt-basics.setoids hiding (||_||;_⇒_)
open import ecats.basic-defs.ecat-def&not
open import ecats.basic-defs.isomorphism
open import ecats.basic-props.isomorphism
open import ecats.functors.defs.efunctor-d&n
open import ecats.functors.defs.natural-transformation
open import ecats.functors.defs.natural-iso
open import ecats.functors.defs.adjunction
open import ecats.constructions.functor-ecat

module local-kan-extension-defs {ℓₒ₁ ℓₐ₁ ℓ~₁}{𝔸 : ecategoryₗₑᵥ ℓₒ₁ ℓₐ₁ ℓ~₁}
                                {ℓₒ₂ ℓₐ₂ ℓ~₂}{𝔹 : ecategoryₗₑᵥ ℓₒ₂ ℓₐ₂ ℓ~₂}(K : efunctorₗₑᵥ 𝔸 𝔹)
                                {ℓₒ ℓₐ ℓ~}{𝕏 : ecategoryₗₑᵥ ℓₒ ℓₐ ℓ~}(F : efunctorₗₑᵥ 𝔸 𝕏)
                                where
  private
    module 𝔸 = ecat 𝔸
    module 𝔹 = ecat 𝔹
    module 𝕏 = ecat 𝕏
    module K = efctr K
    module F = efctr F
    module NT = NatTr

  record is-loc-left-kan-extension (Lan : efunctorₗₑᵥ 𝔹 𝕏)(η : F ⇒ Lan ○ K)
                                   : Set (𝔸.ℓₙₒ~ ⊔ 𝔹.ℓₐₗₗ ⊔ 𝕏.ℓₐₗₗ)
                                   where
    infix 90 _+η
    _+η : {G : efunctorₗₑᵥ 𝔹 𝕏} → Lan ⇒ G → F ⇒ G ○ K
    α +η = natt-vcmp (natt-hcmp α natt-id) η
    field
      nt : {G : efunctorₗₑᵥ 𝔹 𝕏} → F ⇒ G ○ K → Lan ⇒ G
      tr : {G : efunctorₗₑᵥ 𝔹 𝕏}(α : F ⇒ G ○ K) → nt {G} α +η NT.~ α
      +η-je : {G : efunctorₗₑᵥ 𝔹 𝕏}(α α' : Lan ⇒ G)
                  → α +η NT.~ α' +η → α NT.~ α'
    uq :  {G : efunctorₗₑᵥ 𝔹 𝕏}(α : F ⇒ G ○ K)(β : Lan ⇒ G) → β +η NT.~ α → β NT.~ nt α
    uq {G} α β eq = +η-je β (nt α) ( _⊙_ {β +η} {α} {(nt {G} α) +η}
                                         eq
                                         (_ˢ {nt {G} α +η} {α} (tr α)) )
                                --(eq ⊙ tr α ˢ)
                  where open setoid-aux (NatTr F (G ○ K))


  record is-loc-right-kan-extension (Ran : efunctorₗₑᵥ 𝔹 𝕏)(ε : Ran ○ K ⇒ F)
                                    : Set (𝔸.ℓₙₒ~ ⊔ 𝔹.ℓₐₗₗ ⊔ 𝕏.ℓₐₗₗ)
                                    where
    ε+ : {G : efunctorₗₑᵥ 𝔹 𝕏} → G ⇒ Ran → G ○ K ⇒ F
    ε+ α = natt-vcmp ε (natt-hcmp α natt-id)
    field
      nt : {G : efunctorₗₑᵥ 𝔹 𝕏} → G ○ K ⇒ F → G ⇒ Ran
      tr : {G : efunctorₗₑᵥ 𝔹 𝕏}(α : G ○ K ⇒ F) → ε+ (nt {G} α) NT.~ α
      ε+-je : {G : efunctorₗₑᵥ 𝔹 𝕏}(α α' : G ⇒ Ran)
                  → ε+ α NT.~ ε+ α' → α NT.~ α'
    uq :  {G : efunctorₗₑᵥ 𝔹 𝕏}(α : G ○ K ⇒ F)(β : G ⇒ Ran) → ε+ β NT.~ α → β NT.~ nt α
    uq {G} α β eq = ε+-je β (nt α) (_⊙_ {ε+ β} {α} {ε+ (nt {G} α)}
                                         eq
                                         (_ˢ {ε+ (nt {G} α)} {α} (tr α)))
                  where open setoid-aux (NatTr (G ○ K) F)
-- end local-kan-extension-defs



record has-loc-left-kan-extensions {ℓₒ₁ ℓₐ₁ ℓ~₁}{𝔸 : ecategoryₗₑᵥ ℓₒ₁ ℓₐ₁ ℓ~₁}
                                   {ℓₒ₂ ℓₐ₂ ℓ~₂}{𝔹 : ecategoryₗₑᵥ ℓₒ₂ ℓₐ₂ ℓ~₂}(K : efunctorₗₑᵥ 𝔸 𝔹)
                                   {ℓₒ ℓₐ ℓ~}{𝕏 : ecategoryₗₑᵥ ℓₒ ℓₐ ℓ~}(F : efunctorₗₑᵥ 𝔸 𝕏)
                                   : Set (ecat.ℓₙₒ~ 𝔸 ⊔ ecat.ℓₐₗₗ 𝔹 ⊔ ecat.ℓₐₗₗ 𝕏)
                                   where
  open local-kan-extension-defs K F
  field
    Lan : efunctorₗₑᵥ 𝔹 𝕏
    η : F ⇒ Lan ○ K
    isllke : is-loc-left-kan-extension Lan η
  module unv = is-loc-left-kan-extension isllke


record has-loc-right-kan-extensions {ℓₒ₁ ℓₐ₁ ℓ~₁}{𝔸 : ecategoryₗₑᵥ ℓₒ₁ ℓₐ₁ ℓ~₁}
                                    {ℓₒ₂ ℓₐ₂ ℓ~₂}{𝔹 : ecategoryₗₑᵥ ℓₒ₂ ℓₐ₂ ℓ~₂}(K : efunctorₗₑᵥ 𝔸 𝔹)
                                    {ℓₒ ℓₐ ℓ~}{𝕏 : ecategoryₗₑᵥ ℓₒ ℓₐ ℓ~}(F : efunctorₗₑᵥ 𝔸 𝕏)
                                    : Set (ecat.ℓₙₒ~ 𝔸 ⊔ ecat.ℓₐₗₗ 𝔹 ⊔ ecat.ℓₐₗₗ 𝕏)
                                    where
  open local-kan-extension-defs K F
  field
    Ran : efunctorₗₑᵥ 𝔹 𝕏
    ε : Ran ○ K ⇒ F
    islrke : is-loc-right-kan-extension Ran ε
  module unv = is-loc-right-kan-extension islrke


record has-glob-left-kan-extensions {ℓₒ₁ ℓₐ₁ ℓ~₁}{𝔸 : ecategoryₗₑᵥ ℓₒ₁ ℓₐ₁ ℓ~₁}
                                    {ℓₒ₂ ℓₐ₂ ℓ~₂}{𝔹 : ecategoryₗₑᵥ ℓₒ₂ ℓₐ₂ ℓ~₂}
                                    (K : efunctorₗₑᵥ 𝔸 𝔹){ℓₒ ℓₐ ℓ~}(𝕏 : ecategoryₗₑᵥ ℓₒ ℓₐ ℓ~)
                                    : Set (ecat.ℓₐₗₗ 𝔸 ⊔ ecat.ℓₐₗₗ 𝔹 ⊔ ecat.ℓₐₗₗ 𝕏)
                                    where
  field
    Lan : efunctorₗₑᵥ [ 𝔸 , 𝕏 ]ᶜᵃᵗ [ 𝔹 , 𝕏 ]ᶜᵃᵗ
    isadj : Lan ⊣ fctr-precmp K 𝕏
  open adjunction-εη isadj public


record has-glob-right-kan-extensions {ℓₒ₁ ℓₐ₁ ℓ~₁}{𝔸 : ecategoryₗₑᵥ ℓₒ₁ ℓₐ₁ ℓ~₁}
                                     {ℓₒ₂ ℓₐ₂ ℓ~₂}{𝔹 : ecategoryₗₑᵥ ℓₒ₂ ℓₐ₂ ℓ~₂}
                                     (K : efunctorₗₑᵥ 𝔸 𝔹){ℓₒ ℓₐ ℓ~}(𝕏 : ecategoryₗₑᵥ ℓₒ ℓₐ ℓ~)
                                     : Set (ecat.ℓₐₗₗ 𝔸 ⊔ ecat.ℓₐₗₗ 𝔹 ⊔ ecat.ℓₐₗₗ 𝕏)
                                     where
  field
    Ran : efunctorₗₑᵥ [ 𝔸 , 𝕏 ]ᶜᵃᵗ [ 𝔹 , 𝕏 ]ᶜᵃᵗ
    isadj : fctr-precmp K 𝕏 ⊣ Ran
  open adjunction-εη isadj public
