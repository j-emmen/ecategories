
{-# OPTIONS --without-K #-}

module ecats.constructions.ecat-ecats where

open import Agda.Primitive
open import tt-basics.basics using (is-tt-eqrel)
open import tt-basics.setoids using (setoid) --hiding (||_||)
open import ecats.basic-defs.ecat-def&not
open import ecats.isomorphism
open import ecats.functors.defs.efunctor-d&n
open import ecats.functors.defs.natural-transformation
open import ecats.functors.defs.natural-iso


-------------------------------------------------
-- Category of efunctors between two ecategories
-------------------------------------------------

Fctrₗₑᵥ : {ℓ₁ ℓ₂ ℓ₃ : Level}(ℂ : ecategoryₗₑᵥ ℓ₁ ℓ₂ ℓ₃){ℓ₄ ℓ₅ ℓ₆ : Level}(𝔻 : ecategoryₗₑᵥ ℓ₄ ℓ₅ ℓ₆)
            → ecategoryₗₑᵥ (ecat.ℓₐₗₗ ℂ ⊔ ecat.ℓₐₗₗ 𝔻)
                           (ecat.ℓₙₒ~ ℂ ⊔ ecat.ℓₕₒₘ 𝔻)
                           (ecat.ℓₒ ℂ ⊔ ecat.ℓ~ 𝔻)
Fctrₗₑᵥ ℂ 𝔻 = record
  { Obj = efunctorₗₑᵥ ℂ 𝔻
  ; Hom = NatTr {ℂ = ℂ} {𝔻 = 𝔻}
  ; isecat = record
           { _∘_ = natt-vcmp {ℂ = ℂ} {𝔻 = 𝔻}
           ; idar = λ F → natt-id {ℂ = ℂ} {𝔻 = 𝔻} {F}
           ; ∘ext = λ _ _ _ _ pff pfg X → 𝔻.∘ext _ _ _ _ (pff X) (pfg X)
           ; lidax = λ f X → 𝔻.lidax (fnc f {X})
           ; ridax = λ f X → 𝔻.ridax (fnc f {X})
           ; assoc = λ f g h X → 𝔻.assoc (fnc f {X}) (fnc g) (fnc h)
           }
  }
  where module 𝔻 = ecat 𝔻
        open natural-transformation

-------------------------------------------------------------
-- Small category of efunctors between two small ecategories
-------------------------------------------------------------

smallFctr : (ℂ 𝔻 : small-ecategory) → small-ecategory
smallFctr ℂ 𝔻 = Fctrₗₑᵥ ℂ 𝔻

-------------------------------------------------------------
-- Locally small category of small ecategories and efunctors
-------------------------------------------------------------


Cat : ecategory
Cat = record
  { Obj = small-ecategory
  ; Hom = {!!}
  ; isecat = {!!}
  }



---------------------------------------------------------------------
-- Large category of efunctors between two locally small ecategories
---------------------------------------------------------------------

Fctr : (ℂ 𝔻 : ecategory) → large-ecategory
Fctr ℂ 𝔻 = Fctrₗₑᵥ ℂ 𝔻

-------------------------------------------------------------
-- Setoid of efunctors between two locally small ecategories
-------------------------------------------------------------

FctrStd : (ℂ 𝔻 : ecategory) → setoid
FctrStd ℂ 𝔻 = record
  { object =  efunctor ℂ 𝔻
  ; _∼_ = λ F G → F ≅ₐ G
  ; istteqrel = record
              { refl = λ F → ≅ₐrefl {ℂ = ℂ} {𝔻 = 𝔻} {F}
              ; sym = ≅ₐsym {ℂ = ℂ} {𝔻 = 𝔻}
              ; tra = λ m n → natiso-vcmp {ℂ = ℂ} {𝔻 = 𝔻} n m
              }
  }

○lid : {ℂ 𝔻 : ecategory} {F : efunctor ℂ 𝔻} → IdF ○ F ≅ₐ F
○lid {ℂ} {𝔻} {F} = record
  { natt = natt
  ; natt⁻¹ = natt⁻¹
  ; isiso = idiso.isisopair
  }
  where module ℂ = ecategory ℂ
        module 𝔻 where
          open ecategory 𝔻 public
          --open epi&mono-defs 𝔻 public
          --open epi&mono-props 𝔻 public
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

○rid : {ℂ 𝔻 : ecategory} {F : efunctor ℂ 𝔻} → F ○ IdF ≅ₐ F
○rid {ℂ} {𝔻} {F} = record
  { natt = natt
  ; natt⁻¹ = natt⁻¹
  ; isiso = idiso.isisopair
  }
  where module ℂ = ecategory ℂ
        module 𝔻 where
          open ecategory 𝔻 public
          --open epis&monos-defs 𝔻 public
          --open epis&monos-props 𝔻 public
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

○ass : {ℂ 𝔻 𝔼 𝔽 : ecategory} {F : efunctor ℂ 𝔻} {G : efunctor 𝔻 𝔼} {H : efunctor 𝔼 𝔽}
          → H ○ G ○ F ≅ₐ (H ○ G) ○ F
○ass {ℂ} {𝔻} {𝔼} {𝔽} {F} {G} {H} = record
  { natt = natt
  ; natt⁻¹ = natt⁻¹
  ; isiso = idiso.isisopair
  }
  where module ℂ = ecategory ℂ
        module 𝔽 where
          open ecategory 𝔽 public
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


------------------------------------------------------------------
-- Very large category of locally small ecategories and efunctors
------------------------------------------------------------------

CAT : Large-ecategory
CAT = record
  { Obj = ecategory
  ; Hom = FctrStd
  ; isecat = record
           { _∘_ = _○_
           ; idar = λ ℂ → IdF {ℂ = ℂ}
           ; ∘ext = λ F F' G G' eqF eqG → natiso-hcmp eqG eqF
           ; lidax = λ F → ○lid {F = F}
           ; ridax = λ F → ○rid {F = F}
           ; assoc = λ F G H → ○ass {F = F} {G} {H}
           }
  }

-- There is no discrete-forget adjunction between Cat and Set₁ since
-- discrete cats have type ecategoryₗₑᵥ ℓ ℓ 0ₗₑᵥ




-- -- Large E-category of locally small E-ecategories

-- natiso-is-tt-eqrel : (ℂ 𝔻 : ecategory) → is-tt-eqrel (_≅ₐ_ {ℂ} {𝔻})
-- natiso-is-tt-eqrel ℂ 𝔻 = record
--   { refl = λ F → natiso-id {F = F}
--   ; sym = natiso-sym
--   ; tra = λ α β → natiso-vcmp β α
--   }

-- efunct-std : (ℂ 𝔻 : ecategory) → setoid
-- efunct-std ℂ 𝔻 = record
--            { object = efunctor ℂ 𝔻
--            ; _∼_ = _≅ₐ_ {ℂ} {𝔻}
--            ; istteqrel = natiso-is-tt-eqrel ℂ 𝔻
--            }


-- ECat : Large-ecategory
-- ECat = record
--      { Obj = ecategory
--      ; Hom = efunct-std
--      ; isecat = record
--                   { _∘_ = _○_
--                   ; idar = λ ℂ → IdF {ℂ}
--                   ; ∘ext = λ _ _ _ _ α β → natiso-hcmp β α
--                   ; lidax = λ F → ○lid {F = F}
--                   ; ridax = λ F → ○rid {F = F}
--                   ; assoc = λ F G H → ○ass {F = F} {G} {H}
--                   }
--      }
