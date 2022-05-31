
{-# OPTIONS --without-K #-}

module ecats.concr-ecats.ecat-ecats where

open import tt-basics.setoids using (setoid)
open import ecats.basic-defs.ecat-def&not
open import ecats.isomorphism
open import ecats.functors.defs.efunctor-d&n
open import ecats.functors.defs.natural-transformation
open import ecats.functors.defs.natural-iso



-----------------------------------------------
-- Setoid of efunctors between two ecategories
-----------------------------------------------

FctrStdₗₑᵥ : {ℓ₁ ℓ₂ ℓ₃ : Level}(ℂ : ecategoryₗₑᵥ ℓ₁ ℓ₂ ℓ₃){ℓ₄ ℓ₅ ℓ₆ : Level}(𝔻 : ecategoryₗₑᵥ ℓ₄ ℓ₅ ℓ₆)
                 → setoid {ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄ ⊔ ℓ₅ ⊔ ℓ₆} {ℓ₁ ⊔ ℓ₂ ⊔ ℓ₅ ⊔ ℓ₆}
FctrStdₗₑᵥ ℂ 𝔻 = record
  { object =  efunctorₗₑᵥ ℂ 𝔻
  ; _∼_ = λ F G → F ≅ₐ G
  ; istteqrel = record
              { refl = λ F → ≅ₐrefl {ℂ = ℂ} {𝔻 = 𝔻} {F}
              ; sym = ≅ₐsym {ℂ = ℂ} {𝔻 = 𝔻}
              ; tra = λ m n → natiso-vcmp {ℂ = ℂ} {𝔻 = 𝔻} n m
              }
  }

module ○-is-monoidal-up-to-nat-iso where
  ○lid : {ℓ₁ₒ ℓ₁ₕ ℓ₁~ : Level}{ℂ : ecategoryₗₑᵥ ℓ₁ₒ ℓ₁ₕ ℓ₁~}
         {ℓ₂ₒ ℓ₂ₕ ℓ₂~ : Level}{𝔻 : ecategoryₗₑᵥ ℓ₂ₒ ℓ₂ₕ ℓ₂~}
         {F : efunctorₗₑᵥ ℂ 𝔻} → IdF ○ F ≅ₐ F
  ○lid {ℂ = ℂ} {𝔻 = 𝔻} {F} = record
    { natt = natt
    ; natt⁻¹ = natt⁻¹
    ; isiso = idiso.isisopair
    }
    where module ℂ = ecat ℂ
          module 𝔻 where
            open ecat 𝔻 public
            open iso-d&p 𝔻 public
          module F = efunctor-aux F
          natt : natural-transformation (IdF ○ F) F
          natt = record
               { fnc = λ {A} → 𝔻.idar (F.ₒ A)
               ; nat = λ f → lidgen ridˢ
               }
               where open ecategory-aux-only 𝔻
          natt⁻¹ : natural-transformation F (IdF ○ F)
          natt⁻¹ = record
               { fnc = λ {A} → 𝔻.idar (F.ₒ A)
               ; nat = λ f → lidgen ridˢ
               }
               where open ecategory-aux-only 𝔻
          idiso : {A : ℂ.Obj} → 𝔻.is-iso (𝔻.idar (F.ₒ A))
          idiso {A} = 𝔻.idar-is-iso (F.ₒ A)
          module idiso {A : ℂ.Obj} = 𝔻.is-iso (idiso {A})

  ○rid : {ℓ₁ₒ ℓ₁ₕ ℓ₁~ : Level}{ℂ : ecategoryₗₑᵥ ℓ₁ₒ ℓ₁ₕ ℓ₁~}
         {ℓ₂ₒ ℓ₂ₕ ℓ₂~ : Level}{𝔻 : ecategoryₗₑᵥ ℓ₂ₒ ℓ₂ₕ ℓ₂~}
         {F : efunctorₗₑᵥ ℂ 𝔻} → F ○ IdF ≅ₐ F
  ○rid {ℂ = ℂ} {𝔻 = 𝔻} {F} = record
    { natt = natt
    ; natt⁻¹ = natt⁻¹
    ; isiso = idiso.isisopair
    }
    where module ℂ = ecat ℂ
          module 𝔻 where
            open ecat 𝔻 public
            open iso-d&p 𝔻 public
          module F = efunctor-aux F
          natt : natural-transformation (F ○ IdF) F
          natt = record
               { fnc = λ {A} → 𝔻.idar (F.ₒ A)
               ; nat = λ f → lidgen ridˢ
               }
               where open ecategory-aux-only 𝔻
          natt⁻¹ : natural-transformation F (F ○ IdF)
          natt⁻¹ = record
               { fnc = λ {A} → 𝔻.idar (F.ₒ A)
               ; nat = λ f → lidgen ridˢ
               }
               where open ecategory-aux-only 𝔻
          idiso : {A : ℂ.Obj} → 𝔻.is-iso (𝔻.idar (F.ₒ A))
          idiso {A} = 𝔻.idar-is-iso (F.ₒ A)
          module idiso {A : ℂ.Obj} = 𝔻.is-iso (idiso {A})

  ○ass : {ℓ₁ₒ ℓ₁ₕ ℓ₁~ : Level}{ℂ : ecategoryₗₑᵥ ℓ₁ₒ ℓ₁ₕ ℓ₁~}
         {ℓ₂ₒ ℓ₂ₕ ℓ₂~ : Level}{𝔻 : ecategoryₗₑᵥ ℓ₂ₒ ℓ₂ₕ ℓ₂~}
         {ℓ₃ₒ ℓ₃ₕ ℓ₃~ : Level}{𝔼 : ecategoryₗₑᵥ ℓ₃ₒ ℓ₃ₕ ℓ₃~}
         {ℓ₄ₒ ℓ₄ₕ ℓ₄~ : Level}{𝔽 : ecategoryₗₑᵥ ℓ₄ₒ ℓ₄ₕ ℓ₄~}
         {F : efunctorₗₑᵥ ℂ 𝔻}{G : efunctorₗₑᵥ 𝔻 𝔼}{H : efunctorₗₑᵥ 𝔼 𝔽}
            → H ○ G ○ F ≅ₐ (H ○ G) ○ F
  ○ass {ℂ = ℂ} {𝔻 = 𝔻} {𝔼 = 𝔼} {𝔽 = 𝔽} {F} {G} {H} = record
    { natt = natt
    ; natt⁻¹ = natt⁻¹
    ; isiso = idiso.isisopair
    }
    where module ℂ = ecat ℂ
          module 𝔽 where
            open ecat 𝔽 public
            --open epis&monos-defs 𝔽 public
            --open epis&monos-props 𝔽 public
            open iso-d&p 𝔽 public
          module F = efunctor-aux F
          module G = efunctor-aux G
          module H = efunctor-aux H
          natt : natural-transformation (H ○ G ○ F) ((H ○ G) ○ F)
          natt = record
               { fnc = λ {A} → 𝔽.idar (H.ₒ (G.ₒ (F.ₒ A)))
               ; nat = λ f → lidgen ridˢ
               }
               where open ecategory-aux-only 𝔽
          natt⁻¹ : natural-transformation ((H ○ G) ○ F) (H ○ G ○ F)
          natt⁻¹ = record
               { fnc = λ {A} → 𝔽.idar (H.ₒ (G.ₒ (F.ₒ A)))
               ; nat = λ f → lidgen ridˢ
               }
               where open ecategory-aux-only 𝔽
          idiso : {A : ℂ.Obj} → 𝔽.is-iso (𝔽.idar (H.ₒ (G.ₒ (F.ₒ A))))
          idiso {A} = 𝔽.idar-is-iso (H.ₒ (G.ₒ (F.ₒ A)))
          module idiso {A : ℂ.Obj} = 𝔽.is-iso (idiso {A})
-- end ○-is-monoidal-up-to-nat-iso


○-is-ecat : (ℓₒ ℓₕ ℓ~ : Level) → is-ecategory (ecategoryₗₑᵥ ℓₒ ℓₕ ℓ~) (λ ℂ 𝔻 → FctrStdₗₑᵥ ℂ 𝔻)
○-is-ecat ℓₒ ℓₕ ℓ~ = record
  { _∘_ = _○_
  ; idar = λ ℂ → IdF {ℂ = ℂ}
  ; ∘ext = λ {ℂ} {𝔻} {𝔼} F F' G G' eqF eqG → natiso-hcmp {ℂ = ℂ} {𝔻 = 𝔻} {𝔼 = 𝔼} eqG eqF
  ; lidax = λ {ℂ} {𝔻} F → ○lid {ℂ = ℂ} {𝔻 = 𝔻} {F}
  ; ridax = λ {ℂ} {𝔻} F → ○rid {ℂ = ℂ} {𝔻 = 𝔻} {F}
  ; assoc = λ {ℂ} {𝔻} {𝔼} {𝔽} F G H → ○ass {ℂ = ℂ} {𝔻 = 𝔻} {𝔼 = 𝔼} {𝔽 = 𝔽} {F} {G} {H}
  }
  where open ○-is-monoidal-up-to-nat-iso


-------------------------------------------------------------
-- Setoid of efunctors between two small ecategories
-------------------------------------------------------------

FctrStd₀ : (ℂ 𝔻 : small-ecategory) → setoid {0ₗₑᵥ} {0ₗₑᵥ}
FctrStd₀ ℂ 𝔻 = FctrStdₗₑᵥ ℂ 𝔻

-------------------------------------------------------------
-- Setoid of efunctors between two locally small ecategories
-------------------------------------------------------------

FctrStd₁ : (ℂ 𝔻 : ecategory) → setoid {1ₗₑᵥ} {1ₗₑᵥ}
FctrStd₁ ℂ 𝔻 = FctrStdₗₑᵥ ℂ 𝔻


----------------------------------------------------------
-- Category of ecategories and efunctors at a given level
----------------------------------------------------------

CATₗₑᵥ : (ℓₒ ℓₐ ℓ~ : Level) → ecategoryₗₑᵥ (sucₗₑᵥ (ℓₒ ⊔ ℓₐ ⊔ ℓ~)) (ℓₒ ⊔ ℓₐ ⊔ ℓ~) (ℓₒ ⊔ ℓₐ ⊔ ℓ~)
CATₗₑᵥ ℓₒ ℓₐ ℓ~ = record
  { Obj = ecategoryₗₑᵥ ℓₒ ℓₐ ℓ~
  ; Hom = λ ℂ 𝔻 → FctrStdₗₑᵥ ℂ 𝔻
  ; isecat = ○-is-ecat ℓₒ ℓₐ ℓ~
  }
module CATₗₑᵥ (ℓₒ ℓₐ ℓ~ : Level) = ecat (CATₗₑᵥ ℓₒ ℓₐ ℓ~)

-------------------------------------------------------------
-- Locally small category of small ecategories and efunctors
-------------------------------------------------------------

Cat : ecategory
Cat = CATₗₑᵥ 0ₗₑᵥ 0ₗₑᵥ 0ₗₑᵥ

------------------------------------------------------------------
-- Very large category of locally small ecategories and efunctors
------------------------------------------------------------------

CAT : Large-ecategory
CAT = CATₗₑᵥ 1ₗₑᵥ 0ₗₑᵥ 0ₗₑᵥ
