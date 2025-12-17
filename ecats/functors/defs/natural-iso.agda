
{-# OPTIONS --without-K #-}

module ecats.functors.defs.natural-iso where

open import Agda.Primitive
open import tt-basics.setoids using (setoid) --hiding (||_||; _⇒_)
open import ecats.basic-defs.ecat-def&not
open import ecats.basic-defs.isomorphism
open import ecats.basic-props.isomorphism
open import ecats.isomorphism
open import ecats.functors.defs.efunctor-d&n
open import ecats.functors.defs.natural-transformation


------------------------
-- Natural isomorphisms
------------------------

record natural-iso {ℓ₁ ℓ₂ ℓ₃}{ℂ : ecategoryₗₑᵥ ℓ₁ ℓ₂ ℓ₃}{ℓ₄ ℓ₅ ℓ₆}{𝔻 : ecategoryₗₑᵥ ℓ₄ ℓ₅ ℓ₆}
                   (F G : efunctorₗₑᵥ ℂ 𝔻) : Set (ecat.ℓₙₒ~ ℂ ⊔ ecat.ℓₕₒₘ 𝔻)
                   where
  private
    module ℂ = ecat ℂ
    module 𝔻 = ecat 𝔻
    module F = efunctorₗₑᵥ F
    module G = efunctorₗₑᵥ G
  field
    natt : natural-transformation F G
    natt⁻¹ : natural-transformation G F
  open natural-transformation natt public
  open natural-transformation natt⁻¹ renaming (fnc to fnc⁻¹; nat to nat⁻¹; natˢ to nat⁻¹ˢ) public
  open iso-defs 𝔻
  field
    isiso : {A : ℂ.Obj} → is-iso-pair (fnc {A}) (fnc⁻¹ {A})
  open module isop {A : ℂ.Obj} = is-iso-pair (isiso {A}) public
  open ecategory-aux-only 𝔻
  D2Cᵣ : {A B : ℂ.Obj}{f : || ℂ.Hom A B ||} → F.ₐ f 𝔻.~ fnc⁻¹ 𝔻.∘ G.ₐ f 𝔻.∘ fnc
  D2Cᵣ {f = f} = lidggˢ r iddom ⊙ assˢ ⊙ ∘e (nat f) r 
  D2Cᵣˢ : {A B : ℂ.Obj}{f : || ℂ.Hom A B ||} → fnc⁻¹ 𝔻.∘ G.ₐ f 𝔻.∘ fnc 𝔻.~ F.ₐ f
  D2Cᵣˢ {f = f} = ∘e (nat f ˢ) r ⊙ ass ⊙ lidgg r iddom 
  D2Cₗ : {A B : ℂ.Obj}{f : || ℂ.Hom A B ||} → F.ₐ f 𝔻.~ (fnc⁻¹ 𝔻.∘ G.ₐ f) 𝔻.∘ fnc
  D2Cₗ {f = f} = ridggˢ r iddom ⊙ ass ⊙ ∘e r (nat⁻¹ f ˢ)
  D2Cₗˢ : {A B : ℂ.Obj}{f : || ℂ.Hom A B ||} → (fnc⁻¹ 𝔻.∘ G.ₐ f) 𝔻.∘ fnc 𝔻.~ F.ₐ f
  D2Cₗˢ {f = f} = ∘e r (nat⁻¹ f) ⊙ assˢ ⊙ ridgg r iddom 
  C2Dᵣ : {A B : ℂ.Obj}{f : || ℂ.Hom A B ||} → G.ₐ f 𝔻.~ fnc 𝔻.∘ F.ₐ f 𝔻.∘ fnc⁻¹
  C2Dᵣ {f = f} = lidggˢ r idcod ⊙ assˢ ⊙ ∘e (nat⁻¹ f) r 
  C2Dᵣˢ : {A B : ℂ.Obj}{f : || ℂ.Hom A B ||} → fnc 𝔻.∘ F.ₐ f 𝔻.∘ fnc⁻¹ 𝔻.~ G.ₐ f
  C2Dᵣˢ {f = f} = ∘e (nat⁻¹ f ˢ) r ⊙ ass ⊙ lidgg r idcod 
  C2Dₗ : {A B : ℂ.Obj}{f : || ℂ.Hom A B ||} → G.ₐ f 𝔻.~ (fnc 𝔻.∘ F.ₐ f) 𝔻.∘ fnc⁻¹
  C2Dₗ {f = f} = ridggˢ r idcod ⊙ ass ⊙ ∘e r (nat f ˢ)
  C2Dₗˢ : {A B : ℂ.Obj}{f : || ℂ.Hom A B ||} → (fnc 𝔻.∘ F.ₐ f) 𝔻.∘ fnc⁻¹ 𝔻.~ G.ₐ f
  C2Dₗˢ {f = f} = ∘e r (nat f) ⊙ assˢ ⊙ ridgg r idcod 

infixr 9 _≅ₐ_
_≅ₐ_ :  {ℓ₁ ℓ₂ ℓ₃ : Level}{ℂ : ecategoryₗₑᵥ ℓ₁ ℓ₂ ℓ₃}{ℓ₄ ℓ₅ ℓ₆ : Level}{𝔻 : ecategoryₗₑᵥ ℓ₄ ℓ₅ ℓ₆}
        (F G : efunctorₗₑᵥ ℂ 𝔻) → Set (ecat.ℓₙₒ~ ℂ ⊔ ecat.ℓₕₒₘ 𝔻)
F ≅ₐ G = natural-iso F G


module natural-iso-defs {ℓ₁ ℓ₂ ℓ₃}{ℂ : ecategoryₗₑᵥ ℓ₁ ℓ₂ ℓ₃}{ℓ₄ ℓ₅ ℓ₆}{𝔻 : ecategoryₗₑᵥ ℓ₄ ℓ₅ ℓ₆}
                        (F G : efunctorₗₑᵥ ℂ 𝔻)
                        where
  private
    module ℂ = ecat ℂ
    module 𝔻 where
      open ecat 𝔻 public
      open iso-defs 𝔻 public
      open iso-props 𝔻 public
    module F = efctr F
    module G = efctr G
  open natural-trans-defs F G
  mk-natiso : {a : {X : ℂ.Obj} → || 𝔻.Hom (F.ₒ X) (G.ₒ X) ||}{a⁻¹ : {X : ℂ.Obj} → || 𝔻.Hom (G.ₒ X) (F.ₒ X) ||}(aiso : {X : ℂ.Obj} → 𝔻.is-iso-pair (a {X}) (a⁻¹ {X})) → is-natural a
                   → F ≅ₐ G
  mk-natiso {a} {a⁻¹} aiso anat = record
    { natt = record
           { fnc = a
           ; nat = anat
           }
    ; natt⁻¹ = record
             { fnc = a⁻¹
             ; nat = λ {X} {Y} f → 𝔻.iso-sq-alt (aiso {X}) (aiso {Y}) (anat f)
             }
    ; isiso = aiso
    }
-- end natural-iso-defs                   

≅ₐrefl : {ℓ₁ ℓ₂ ℓ₃ : Level}{ℂ : ecategoryₗₑᵥ ℓ₁ ℓ₂ ℓ₃}{ℓ₄ ℓ₅ ℓ₆ : Level}{𝔻 : ecategoryₗₑᵥ ℓ₄ ℓ₅ ℓ₆}
         {F : efunctorₗₑᵥ ℂ 𝔻} → F ≅ₐ F
≅ₐrefl {𝔻 = 𝔻} {F} = record
  { natt = natt-id
  ; natt⁻¹ = natt-id
  ; isiso = λ {A} → record
          { iddom = lid
          ; idcod = lid
          }
  }
  where open ecategory-aux-only 𝔻

≅ₐsym : {ℓ₁ ℓ₂ ℓ₃ : Level}{ℂ : ecategoryₗₑᵥ ℓ₁ ℓ₂ ℓ₃}{ℓ₄ ℓ₅ ℓ₆ : Level}{𝔻 : ecategoryₗₑᵥ ℓ₄ ℓ₅ ℓ₆}
       {F G : efunctorₗₑᵥ ℂ 𝔻} → F ≅ₐ G → G ≅ₐ F
≅ₐsym α = record
  { natt = natt⁻¹
  ; natt⁻¹ = natt
  ; isiso = λ {A} → record
          { iddom = idcod
          ; idcod = iddom
          }
  }
  where open natural-iso α

natiso-vcmp : {ℓ₁ ℓ₂ ℓ₃ : Level}{ℂ : ecategoryₗₑᵥ ℓ₁ ℓ₂ ℓ₃}{ℓ₄ ℓ₅ ℓ₆ : Level}{𝔻 : ecategoryₗₑᵥ ℓ₄ ℓ₅ ℓ₆}
              {F G H : efunctorₗₑᵥ ℂ 𝔻}
                  → G ≅ₐ H → F ≅ₐ G → F ≅ₐ H
natiso-vcmp {𝔻 = 𝔻} {F} {G} {H} β α = record
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


natiso-hcmp : {ℓ₁ ℓ₂ ℓ₃ : Level}{ℂ : ecategoryₗₑᵥ ℓ₁ ℓ₂ ℓ₃}{ℓ₄ ℓ₅ ℓ₆ : Level}{𝔻 : ecategoryₗₑᵥ ℓ₄ ℓ₅ ℓ₆}
              {ℓ₇ ℓ₈ ℓ₉ : Level}{𝔼 : ecategoryₗₑᵥ ℓ₇ ℓ₈ ℓ₉}{F G : efunctorₗₑᵥ ℂ 𝔻}
              {H K : efunctorₗₑᵥ 𝔻 𝔼}
                  → H ≅ₐ K → F ≅ₐ G → H ○ F ≅ₐ K ○ G
natiso-hcmp {𝔼 = 𝔼} {F} {G} {H} {K} β α = record
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


-- composition of functors is monoidal up to natural iso

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

○assˢ : {ℓ₁ₒ ℓ₁ₕ ℓ₁~ : Level}{ℂ : ecategoryₗₑᵥ ℓ₁ₒ ℓ₁ₕ ℓ₁~}
        {ℓ₂ₒ ℓ₂ₕ ℓ₂~ : Level}{𝔻 : ecategoryₗₑᵥ ℓ₂ₒ ℓ₂ₕ ℓ₂~}
        {ℓ₃ₒ ℓ₃ₕ ℓ₃~ : Level}{𝔼 : ecategoryₗₑᵥ ℓ₃ₒ ℓ₃ₕ ℓ₃~}
        {ℓ₄ₒ ℓ₄ₕ ℓ₄~ : Level}{𝔽 : ecategoryₗₑᵥ ℓ₄ₒ ℓ₄ₕ ℓ₄~}
        {F : efunctorₗₑᵥ ℂ 𝔻}{G : efunctorₗₑᵥ 𝔻 𝔼}{H : efunctorₗₑᵥ 𝔼 𝔽}
           → (H ○ G) ○ F ≅ₐ H ○ G ○ F
○assˢ {F = F} {G} {H} = ≅ₐsym (○ass {F = F} {G} {H})
