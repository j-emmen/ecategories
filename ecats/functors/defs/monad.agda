{-# OPTIONS --without-K #-}

module ecats.functors.defs.monad where

open import ecats.basic-defs.ecat-def&not
open import ecats.functors.defs.efunctor-d&n
open import ecats.functors.defs.natural-transformation
open import ecats.functors.defs.natural-iso



-- Preliminary definitions. To be renamend and moved in a more appropriate place.
infix 90 _ₙₜ·'_ _·ₙₜ'_ ₙₜ·'' ·ₙₜ''
_ₙₜ·'_ : {ℓ₁ ℓ₂ ℓ₃ : Level}{ℂ : ecategoryₗₑᵥ ℓ₁ ℓ₂ ℓ₃}{ℓ₄ ℓ₅ ℓ₆ : Level}{𝔻 : ecategoryₗₑᵥ ℓ₄ ℓ₅ ℓ₆}
         {K : efunctorₗₑᵥ 𝔻 𝔻}
           → IdF ⇒ K → (F : efunctorₗₑᵥ ℂ 𝔻) → F ⇒ K ○ F
α ₙₜ·' F = α ₙₜ· F ○ᵥ Id○F≅F.natt⁻¹
         where module Id○F≅F = natural-iso (○lid {F = F})

_·ₙₜ'_ : {ℓ₁ ℓ₂ ℓ₃ : Level}{ℂ : ecategoryₗₑᵥ ℓ₁ ℓ₂ ℓ₃}{ℓ₄ ℓ₅ ℓ₆ : Level}{𝔻 : ecategoryₗₑᵥ ℓ₄ ℓ₅ ℓ₆}
         (K : efunctorₗₑᵥ ℂ 𝔻){F : efunctorₗₑᵥ ℂ ℂ}(α : IdF ⇒ F)
           → K ⇒ K ○ F
K ·ₙₜ' α = K ·ₙₜ α ○ᵥ K○Id≅K.natt⁻¹
         where module K○Id≅K = natural-iso (○rid {F = K})

ₙₜ·'' : {ℓ₁ ℓ₂ ℓ₃ : Level}{ℂ : ecategoryₗₑᵥ ℓ₁ ℓ₂ ℓ₃}{ℓ₄ ℓ₅ ℓ₆ : Level}{𝔻 : ecategoryₗₑᵥ ℓ₄ ℓ₅ ℓ₆}
        {ℓ₇' ℓ₈' ℓ₉' : Level}{𝔼' : ecategoryₗₑᵥ ℓ₇' ℓ₈' ℓ₉'}{ℓ₇ ℓ₈ ℓ₉ : Level}
        {𝔼 : ecategoryₗₑᵥ ℓ₇ ℓ₈ ℓ₉}(G : efunctorₗₑᵥ 𝔻 𝔼)(K : efunctorₗₑᵥ 𝔻 𝔼')(H : efunctorₗₑᵥ 𝔼' 𝔼)
          → G ⇒ H ○ K → (F : efunctorₗₑᵥ ℂ 𝔻) → G ○ F ⇒ H ○ K ○ F
ₙₜ·'' G K H α F = [H○K]○F≅H○K○F.natt⁻¹ ○ᵥ α ₙₜ· F
                where module [H○K]○F≅H○K○F = natural-iso (○ass {F = F}{G = K}{H = H})
syntax ₙₜ·'' G K H α F = α ₙₜ·'' F [ G , K , H ]

·ₙₜ'' : {ℓ₁ ℓ₂ ℓ₃ : Level}{ℂ : ecategoryₗₑᵥ ℓ₁ ℓ₂ ℓ₃}{ℓ₄ ℓ₅ ℓ₆ : Level}{𝔻 : ecategoryₗₑᵥ ℓ₄ ℓ₅ ℓ₆}
        {ℓ₇' ℓ₈' ℓ₉' : Level}{𝔼' : ecategoryₗₑᵥ ℓ₇' ℓ₈' ℓ₉'}{ℓ₇ ℓ₈ ℓ₉ : Level}
        {𝔼 : ecategoryₗₑᵥ ℓ₇ ℓ₈ ℓ₉}(F : efunctorₗₑᵥ 𝔼 ℂ)
        (G : efunctorₗₑᵥ 𝔻 𝔼)(K : efunctorₗₑᵥ 𝔻 𝔼')(H : efunctorₗₑᵥ 𝔼' 𝔼)
          → G ⇒ H ○ K → F ○ G ⇒ (F ○ H) ○ K
·ₙₜ''  F G K H α = [H○K]○F≅H○K○F.natt ○ᵥ F ·ₙₜ α
                 where module [H○K]○F≅H○K○F = natural-iso (○ass {F = K}{G = H}{H = F})
syntax ·ₙₜ'' F G K H α = F ·ₙₜ'' α [ G , K , H ]




----------
-- Monads
----------

record is-monad {ℓₒ ℓₐ ℓ~}{ℂ : ecategoryₗₑᵥ ℓₒ ℓₐ ℓ~}
                (T : efunctorₗₑᵥ ℂ ℂ)
                : Set (ecat.ℓₐₗₗ ℂ)
                where
  T² : efunctorₗₑᵥ ℂ ℂ
  T² = T ○ T
  field
    ηnt : natural-transformation IdF T
    μnt : natural-transformation T² T
  module ηnt = natural-transformation ηnt
  module μnt = natural-transformation μnt

record monad-on {ℓₒ ℓₐ ℓ~}(ℂ : ecategoryₗₑᵥ ℓₒ ℓₐ ℓ~)
                : Set (ecat.ℓₐₗₗ ℂ)
                where
  field
    fctr : efunctorₗₑᵥ ℂ ℂ
    is-mnd : is-monad fctr
  open is-monad is-mnd renaming (T² to ²) public

private
  module mnd {ℓₒ ℓₐ ℓ~}{ℂ : ecategoryₗₑᵥ ℓₒ ℓₐ ℓ~}(T : monad-on ℂ) where
    open monad-on T public
    open efunctorₗₑᵥ fctr public
    module ² = efunctorₗₑᵥ ²


-- Moprhisms of monads

record is-monad-lax-morphism {ℓₒ₁ ℓₐ₁ ℓ~₁}{ℂ : ecategoryₗₑᵥ ℓₒ₁ ℓₐ₁ ℓ~₁}{ℓₒ₂ ℓₐ₂ ℓ~₂}{𝔻 : ecategoryₗₑᵥ ℓₒ₂ ℓₐ₂ ℓ~₂}
                             (T : monad-on ℂ)(S : monad-on 𝔻)(F : efunctorₗₑᵥ ℂ 𝔻)
                             (ϕ : natural-transformation (mnd.fctr S ○ F) (F ○ mnd.fctr T))
                : Set (ecat.ℓₐₗₗ ℂ ⊔ ecat.ℓₐₗₗ 𝔻)
                where
  private
    module T = mnd T
    module S = mnd S
    module [F,F○T] = NatTr F (F ○ T.fctr)
    module [S²○F,F○T] = NatTr (S.² ○ F) (F ○ T.fctr)
    module S○S○F≅S²○F = natural-iso (○ass {F = F}{G = S.fctr}{H = S.fctr})
  field
    ηeq : ϕ ○ᵥ S.ηnt ₙₜ·' F [F,F○T].~ F ·ₙₜ' T.ηnt 
    μeq : ϕ ○ᵥ S.μnt ₙₜ· F [S²○F,F○T].~ F ·ₙₜ T.μnt ○ᵥ ϕ ₙₜ·'' T.fctr [ S.fctr ○ F , T.fctr , F ]
                                                    ○ᵥ S.fctr ·ₙₜ'' ϕ [ S.fctr ○ F , T.fctr , F ]
                                                     ○ᵥ S○S○F≅S²○F.natt⁻¹


record monad-lax-morphism {ℓₒ₁ ℓₐ₁ ℓ~₁}{ℂ : ecategoryₗₑᵥ ℓₒ₁ ℓₐ₁ ℓ~₁}{ℓₒ₂ ℓₐ₂ ℓ~₂}{𝔻 : ecategoryₗₑᵥ ℓₒ₂ ℓₐ₂ ℓ~₂}
                             (T : monad-on ℂ)(S : monad-on 𝔻)
                : Set (ecat.ℓₐₗₗ ℂ ⊔ ecat.ℓₐₗₗ 𝔻)
                where
  private
    module T = mnd T
    module S = mnd S
  field
    fctr : efunctorₗₑᵥ ℂ 𝔻
    natt : natural-transformation (S.fctr ○ fctr) (fctr ○ T.fctr)
    is-laxm : is-monad-lax-morphism T S fctr natt
  module laxm = is-monad-lax-morphism is-laxm
