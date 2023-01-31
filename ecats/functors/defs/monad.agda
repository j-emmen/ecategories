{-# OPTIONS --without-K #-}

module ecats.functors.defs.monad where

open import ecats.basic-defs.ecat-def&not
open import ecats.functors.defs.efunctor-d&n
open import ecats.functors.defs.natural-transformation
open import ecats.functors.defs.natural-iso



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
    module ℂ = ecat ℂ
    module T = efctr T
    module η = natural-transformation η
    module μ = natural-transformation μ
    module [T,T] = NatTr T T
    module [T²○T,T] = NatTr (T² ○ T) T
    module [T○T²,T] = NatTr (T ○ T²) T
    module T○T²≅T²○T = natural-iso (○ass {F = T} {T} {T})
           -- the components at A are the identities on T³A
  field
    ax-Tη : (X : ℂ.Obj) → μ.ar {X} ℂ.∘ T.ₐ (η.ar {X}) ℂ.~ ℂ.idar (T.ₒ X)
    --μ ○ᵥ T ·ₙₜ' η [T,T].~ natt-id
    ax-ηT : (X : ℂ.Obj) → μ.ar {X} ℂ.∘ η.ar {T.ₒ X} ℂ.~ ℂ.idar (T.ₒ X)
    -- μ ○ᵥ η ₙₜ·' T [T,T].~ natt-id
    ax-μ : (X : ℂ.Obj) → μ.ar {X} ℂ.∘ μ.ar {T.ₒ X} ℂ.~ μ.ar {X} ℂ.∘ T.ₐ (μ.ar {X})
    --μ ○ᵥ μ ₙₜ· T [T²○T,T].~ μ ○ᵥ T ·ₙₜ μ ○ᵥ T○T²≅T²○T.natt⁻¹
  ax-Tηˢ : (X : ℂ.Obj) → ℂ.idar (T.ₒ X) ℂ.~ μ.ar {X} ℂ.∘ T.ₐ (η.ar {X})
  --natt-id [T,T].~ μ ○ᵥ T ·ₙₜ' η
  ax-Tηˢ X = ax-Tη X ˢ
          where open ecategory-aux ℂ using (_ˢ)
  ax-ηTˢ : (X : ℂ.Obj) → ℂ.idar (T.ₒ X) ℂ.~ μ.ar {X} ℂ.∘ η.ar {T.ₒ X}
  --natt-id [T,T].~ μ ○ᵥ η ₙₜ·' T
  ax-ηTˢ X = ax-ηT X ˢ
           where open ecategory-aux ℂ using (_ˢ)
  ax-μˢ : (X : ℂ.Obj) → μ.ar {X} ℂ.∘ T.ₐ (μ.ar {X}) ℂ.~ μ.ar {X} ℂ.∘ μ.ar {T.ₒ X}
  --μ ○ᵥ T ·ₙₜ μ [T○T²,T].~ μ ○ᵥ μ ₙₜ· T ○ᵥ T○T²≅T²○T.natt
  ax-μˢ X = ax-μ X ˢ
  {-~proof μ.ar ∘ T.ₐ μ.ar                      ~[ ridgenˢ (ridˢ ⊙ assˢ) ] /
                   (μ.ar ∘ T.ₐ μ.ar ∘ idar _) ∘ idar _  ~[ ∘e r (ax-μ X ˢ) ⊙ assˢ ]∎
                   μ.ar ∘ μ.ar ∘ idar _ ∎-}
          where open ecategory-aux ℂ using (_ˢ)


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
