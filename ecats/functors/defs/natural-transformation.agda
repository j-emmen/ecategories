 
-- disable the K axiom:

{-# OPTIONS --without-K #-}

-- Agda version 2.5.4.1

module ecats.functors.defs.natural-transformation where

open import ecats.basic-defs.ecat-def&not
open import ecats.basic-defs.isomorphism
open import ecats.basic-defs.epi&mono
open import ecats.basic-props.epi&mono
open import ecats.functors.defs.efunctor-d&n


-- Natural transformations

record natural-transformation {ℂ 𝔻 : ecategory} (F G : efunctor ℂ 𝔻) : Set₁ where
  private
    module ℂ = ecategory ℂ
    module 𝔻 = ecategory 𝔻
    module F = efunctor F
    module G = efunctor G
  field
    fnc : {A : ℂ.Obj} → || 𝔻.Hom (F.ₒ A) (G.ₒ A) ||
    nat : {A B : ℂ.Obj} → (f : || ℂ.Hom A B ||)
             → fnc 𝔻.∘ (F.ₐ f) 𝔻.~ (G.ₐ f) 𝔻.∘ fnc

infixr 8 _⇒_
_⇒_ :  {ℂ 𝔻 : ecategory} (F G : efunctor ℂ 𝔻) → Set₁
F ⇒ G = natural-transformation F G


natt-vcmp : {ℂ 𝔻 : ecategory} {F G H : efunctor ℂ 𝔻}
               → G ⇒ H → F ⇒ G → F ⇒ H
natt-vcmp {ℂ} {𝔻} {F} {G} {H} β α = record
  { fnc = λ {A} → β.fnc 𝔻.∘ α.fnc
  ; nat = λ f → assˢ ⊙ ∘e (α.nat f) r ⊙ ass ⊙ ∘e r (β.nat f) ⊙ assˢ
  }
  where module 𝔻 = ecategory 𝔻
        module α = natural-transformation α
        module β = natural-transformation β
        open ecategory-aux-only 𝔻


natt-hcmp : {ℂ 𝔻 𝔼 : ecategory} {F G : efunctor ℂ 𝔻} {H K : efunctor 𝔻 𝔼}
               → H ⇒ K → F ⇒ G → H ○ F ⇒ K ○ G
natt-hcmp {𝔼 = 𝔼} {F} {G} {H} {K} β α = record
  { fnc = λ {A} → β.fnc {G.ₒ A} 𝔼.∘ H.ₐ (α.fnc {A})
  ; nat = λ f → ~proof
        (β.fnc 𝔼.∘ H.ₐ α.fnc) 𝔼.∘ H.ₐ (F.ₐ f)   ~[ assˢ ⊙ ∘e (H.∘∘ (α.nat f)) r ] /
        β.fnc 𝔼.∘ H.ₐ (G.ₐ f) 𝔼.∘ H.ₐ α.fnc     ~[ ass ⊙ ∘e r (β.nat (G.ₐ f)) ⊙ assˢ ]∎
        K.ₐ (G.ₐ f) 𝔼.∘ β.fnc 𝔼.∘ H.ₐ α.fnc ∎
  }
  where module 𝔼 = ecategory 𝔼
        module F = efunctor F
        module G = efunctor G
        module H = efunctor-aux H
        module K = efunctor K
        module α = natural-transformation α
        module β = natural-transformation β
        open ecategory-aux-only 𝔼


natt-id : {ℂ 𝔻 : ecategory} {F : efunctor ℂ 𝔻} → F ⇒ F
natt-id {ℂ} {𝔻} {F} = record
                { fnc = λ {A} → 𝔻.idar (F.ₒ A)
                ; nat = λ f → lidgen ridˢ
                }
                where module 𝔻 = ecategory 𝔻
                      module F = efunctor F
                      open ecategory-aux-only 𝔻


record natural-iso {ℂ 𝔻 : ecategory} (F G : efunctor ℂ 𝔻) : Set₁ where
  private
    module ℂ = ecategory ℂ
    module 𝔻 = ecategory 𝔻
    module F = efunctor F
    module G = efunctor G
  field
    natt : natural-transformation F G
    natt⁻¹ : natural-transformation G F
  open natural-transformation natt public --renaming (fnc; nat to nat)
  open natural-transformation natt⁻¹ renaming (fnc to fnc⁻¹; nat to nat⁻¹) public
  {-private
    module natt = natural-transformation natt
    module natt⁻¹ = natural-transformation natt⁻¹-}
  open iso-defs 𝔻
  field
    isiso : {A : ℂ.Obj} → is-iso-pair (fnc {A}) (fnc⁻¹ {A})
  module isop {A : ℂ.Obj} = is-iso-pair (isiso {A})
  open isop public


infixr 9 _≅ₐ_
_≅ₐ_ :  {ℂ 𝔻 : ecategory} (F G : efunctor ℂ 𝔻) → Set₁
F ≅ₐ G = natural-iso F G


natiso-vcmp : {ℂ 𝔻 : ecategory} {F G H : efunctor ℂ 𝔻}
                  → G ≅ₐ H → F ≅ₐ G → F ≅ₐ H
natiso-vcmp {ℂ} {𝔻} {F} {G} {H} β α = record
  { natt = natt-vcmp β.natt α.natt
  ; natt⁻¹ = natt-vcmp α.natt⁻¹ β.natt⁻¹
  ; isiso = λ {A} → record
          { iddom = ass ⊙ ∘e r (assˢ ⊙ ridgg r β.iddom) ⊙ α.iddom
          ; idcod = ass ⊙ ∘e r (assˢ ⊙ ridgg r α.idcod) ⊙ β.idcod
          }
  }
  where open ecategory-aux-only 𝔻
        module α = natural-iso α
        module β = natural-iso β


natiso-hcmp : {ℂ 𝔻 𝔼 : ecategory} {F G : efunctor ℂ 𝔻} {H K : efunctor 𝔻 𝔼}
                  → H ≅ₐ K → F ≅ₐ G → H ○ F ≅ₐ K ○ G
natiso-hcmp {ℂ} {𝔻} {𝔼} {F} {G} {H} {K} β α = record
  { natt = natt-hcmp β.natt α.natt
  ; natt⁻¹ = natt-hcmp β.natt⁻¹ α.natt⁻¹
  ; isiso = λ {A} → record
          { iddom = ∘e r (β.nat⁻¹ α.fnc⁻¹) ⊙ assˢ ⊙ ∘e (ass ⊙ lidgg r β.iddom) r ⊙ H.∘ax α.iddom ⊙ H.id
          ; idcod = ∘e r (β.nat α.fnc) ⊙ assˢ ⊙ ∘e (ass ⊙ lidgg r β.idcod) r ⊙ K.∘ax α.idcod ⊙ K.id
          }
  }
  where open ecategory-aux-only 𝔼
        module H = efunctor-aux H
        module K = efunctor-aux K
        module α = natural-iso α
        module β = natural-iso β


natiso-id : {ℂ 𝔻 : ecategory} {F : efunctor ℂ 𝔻} → F ≅ₐ F
natiso-id {ℂ} {𝔻} {F} = record
  { natt = natt-id
  ; natt⁻¹ = natt-id
  ; isiso = λ {A} → record
          { iddom = lid
          ; idcod = lid
          }
  }
  where open ecategory-aux-only 𝔻

natiso-sym : {ℂ 𝔻 : ecategory} {F G : efunctor ℂ 𝔻} → F ≅ₐ G → G ≅ₐ F
natiso-sym α = record
  { natt = natt⁻¹
  ; natt⁻¹ = natt
  ; isiso = λ {A} → record
          { iddom = idcod
          ; idcod = iddom
          }
  }
  where open natural-iso α

○lid : {ℂ 𝔻 : ecategory} {F : efunctor ℂ 𝔻} → IdF ○ F ≅ₐ F
○lid {ℂ} {𝔻} {F} = record
  { natt = natt
  ; natt⁻¹ = natt⁻¹
  ; isiso = idiso.isisopair
  }
  where module ℂ = ecategory ℂ
        module 𝔻 where
          open ecategory 𝔻 public
          open epis&monos-defs 𝔻 public
          open epis&monos-props 𝔻 public
          open iso-defs 𝔻 public
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
          open epis&monos-defs 𝔻 public
          open epis&monos-props 𝔻 public
          open iso-defs 𝔻 public
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
          open epis&monos-defs 𝔽 public
          open epis&monos-props 𝔽 public
          open iso-defs 𝔽 public
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
        
