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

record is-monad-struct {ℓₒ ℓₐ ℓ~}{ℂ : ecategoryₗₑᵥ ℓₒ ℓₐ ℓ~}
                       (T : efunctorₗₑᵥ ℂ ℂ)
                       (η : natural-transformation IdF T)
                       (μ : natural-transformation (T ○ T) T)
                       : Set (ecat.ℓₐₗₗ ℂ)
                       where
  private
    T² : efunctorₗₑᵥ ℂ ℂ
    T² = T ○ T
    module [T,T] = NatTr T T
    module [T²○T,T] = NatTr (T² ○ T) T
    module T○T²≅T²○T = natural-iso (○ass {F = T} {T} {T})
  field
    ax-Tη : μ ○ᵥ T ·ₙₜ' η [T,T].~ natt-id
    ax-ηT : μ ○ᵥ η ₙₜ·' T [T,T].~ natt-id
    ax-μ : μ ○ᵥ μ ₙₜ· T [T²○T,T].~ μ ○ᵥ T ·ₙₜ μ ○ᵥ T○T²≅T²○T.natt⁻¹


record monad-struct-on {ℓₒ ℓₐ ℓ~}{ℂ : ecategoryₗₑᵥ ℓₒ ℓₐ ℓ~}
                       (T : efunctorₗₑᵥ ℂ ℂ)
                       : Set (ecat.ℓₐₗₗ ℂ)
                       where
  T² : efunctorₗₑᵥ ℂ ℂ
  T² = T ○ T
  field
    ηnt : natural-transformation IdF T
    μnt : natural-transformation T² T
    ismndstr : is-monad-struct T ηnt μnt
  module η = natural-transformation ηnt
  module μ = natural-transformation μnt
  open is-monad-struct ismndstr public

record monad-on {ℓₒ ℓₐ ℓ~}(ℂ : ecategoryₗₑᵥ ℓₒ ℓₐ ℓ~)
                : Set (ecat.ℓₐₗₗ ℂ)
                where
  
  field
    fc : efunctorₗₑᵥ ℂ ℂ
    ηnt : natural-transformation IdF fc
    μnt : natural-transformation (fc ○ fc) fc
    ismndstr : is-monad-struct fc ηnt μnt
  ² : efunctorₗₑᵥ ℂ ℂ
  ² = fc ○ fc
  module fc = efunctor-aux fc
  module ² = efunctor-aux ²
  module η = natural-transformation ηnt
  module μ = natural-transformation μnt
  open is-monad-struct ismndstr public


private
  module mnd {ℓₒ ℓₐ ℓ~}{ℂ : ecategoryₗₑᵥ ℓₒ ℓₐ ℓ~}(T : monad-on ℂ) where
    open monad-on T public


-- Moprhisms of monads

record is-monad-lax-morphism {ℓₒ₁ ℓₐ₁ ℓ~₁}{ℂ : ecategoryₗₑᵥ ℓₒ₁ ℓₐ₁ ℓ~₁}{ℓₒ₂ ℓₐ₂ ℓ~₂}{𝔻 : ecategoryₗₑᵥ ℓₒ₂ ℓₐ₂ ℓ~₂}
                             (T : monad-on ℂ)(S : monad-on 𝔻)(F : efunctorₗₑᵥ ℂ 𝔻)
                             (ϕ : natural-transformation (mnd.fc S ○ F) (F ○ mnd.fc T))
                : Set (ecat.ℓₐₗₗ ℂ ⊔ ecat.ℓₐₗₗ 𝔻)
                where
  private
    module T = mnd T
    module S = mnd S
    module [F,F○T] = NatTr F (F ○ T.fc)
    module [S²○F,F○T] = NatTr (S.² ○ F) (F ○ T.fc)
    module S○S○F≅S²○F = natural-iso (○ass {F = F}{G = S.fc}{H = S.fc})
  field
    ηeq : ϕ ○ᵥ S.ηnt ₙₜ·' F [F,F○T].~ F ·ₙₜ' T.ηnt 
    μeq : ϕ ○ᵥ S.μnt ₙₜ· F [S²○F,F○T].~ F ·ₙₜ T.μnt ○ᵥ ϕ ₙₜ·'' T.fc [ S.fc ○ F , T.fc , F ]
                                                    ○ᵥ S.fc ·ₙₜ'' ϕ [ S.fc ○ F , T.fc , F ]
                                                     ○ᵥ S○S○F≅S²○F.natt⁻¹


record monad-lax-morphism {ℓₒ₁ ℓₐ₁ ℓ~₁}{ℂ : ecategoryₗₑᵥ ℓₒ₁ ℓₐ₁ ℓ~₁}{ℓₒ₂ ℓₐ₂ ℓ~₂}{𝔻 : ecategoryₗₑᵥ ℓₒ₂ ℓₐ₂ ℓ~₂}
                             (T : monad-on ℂ)(S : monad-on 𝔻)
                : Set (ecat.ℓₐₗₗ ℂ ⊔ ecat.ℓₐₗₗ 𝔻)
                where
  private
    module T = mnd T
    module S = mnd S
  field
    fc : efunctorₗₑᵥ ℂ 𝔻
    natt : natural-transformation (S.fc ○ fc) (fc ○ T.fc)
    is-laxm : is-monad-lax-morphism T S fc natt
  module fc = efunctor-aux fc
  module natt = natural-transformation natt
  module laxm = is-monad-lax-morphism is-laxm
