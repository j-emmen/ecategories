
{-# OPTIONS --without-K #-}

module ecats.functors.defs.basic-defs where

open import ecats.basic-defs.ecat-def&not
open import ecats.basic-defs.isomorphism
open import ecats.basic-props.isomorphism
open import ecats.functors.defs.efunctor-d&n
open import ecats.functors.defs.natural-transformation
open import ecats.functors.defs.natural-iso


-- Equivalences

record is-equivalence-pair {ℓₒ₁ ℓₐ₁ ℓ~₁ : Level}{ℂ : ecategoryₗₑᵥ ℓₒ₁ ℓₐ₁ ℓ~₁}
                           {ℓₒ₂ ℓₐ₂ ℓ~₂ : Level}{𝔻 : ecategoryₗₑᵥ ℓₒ₂ ℓₐ₂ ℓ~₂}
                           (F : efunctorₗₑᵥ ℂ 𝔻) (G : efunctorₗₑᵥ 𝔻 ℂ)
                           : Set (ecat.ℓₐₗₗ ℂ ⊔ ecat.ℓₐₗₗ 𝔻)
                           where
  field
    ι1 : natural-iso (F ○ G) IdF
    ι2 : natural-iso (G ○ F) IdF
  module ι1 = natural-iso ι1
  module ι2 = natural-iso ι2
  ι1⁻¹ : IdF ≅ₐ F ○ G
  ι1⁻¹ = ≅ₐsym ι1
  ι2⁻¹ :  IdF ≅ₐ G ○ F
  ι2⁻¹ = ≅ₐsym ι2

inv-is-eqv : {ℓₒ₁ ℓₐ₁ ℓ~₁ : Level}{ℂ : ecategoryₗₑᵥ ℓₒ₁ ℓₐ₁ ℓ~₁}
             {ℓₒ₂ ℓₐ₂ ℓ~₂ : Level}{𝔻 : ecategoryₗₑᵥ ℓₒ₂ ℓₐ₂ ℓ~₂}
             {F : efunctorₗₑᵥ ℂ 𝔻}{G : efunctorₗₑᵥ 𝔻 ℂ}
                  → is-equivalence-pair F G → is-equivalence-pair G F
inv-is-eqv eqv = record
  { ι1 = ι2
  ; ι2 = ι1
  }
  where open is-equivalence-pair eqv


record is-adj-equivalence-pair {ℓₒ₁ ℓₐ₁ ℓ~₁ : Level}{ℂ : ecategoryₗₑᵥ ℓₒ₁ ℓₐ₁ ℓ~₁}
                               {ℓₒ₂ ℓₐ₂ ℓ~₂ : Level}{𝔻 : ecategoryₗₑᵥ ℓₒ₂ ℓₐ₂ ℓ~₂}
                               (F : efunctorₗₑᵥ ℂ 𝔻) (G : efunctorₗₑᵥ 𝔻 ℂ)
                               : Set (ecat.ℓₐₗₗ ℂ ⊔ ecat.ℓₐₗₗ 𝔻) where
  private
    module ℂ = ecat ℂ
    module 𝔻 = ecat 𝔻
    module F = efunctor-aux F
    module G = efunctor-aux G
  field
    ι1 : natural-iso (F ○ G) IdF
    ι2 : natural-iso (G ○ F) IdF
  module ι1 = natural-iso ι1
  module ι2 = natural-iso ι2
  ι1⁻¹ : IdF ≅ₐ F ○ G
  ι1⁻¹ = ≅ₐsym ι1
  ι2⁻¹ :  IdF ≅ₐ G ○ F
  ι2⁻¹ = ≅ₐsym ι2
  field
    trid₁ : {X : ℂ.Obj} → ι1.fnc {F.ₒ X} 𝔻.∘ F.ₐ ι2.fnc⁻¹ 𝔻.~ 𝔻.idar (F.ₒ X)
    trid₂ : {Y : 𝔻.Obj} → G.ₐ ι1.fnc ℂ.∘ ι2.fnc⁻¹ {G.ₒ Y} ℂ.~ ℂ.idar (G.ₒ Y)

  -- in this case the triangular identities say that
  -- F ι2 ~ ι1 F and G ι1 ~ ι2 G, respectively.
  eq₁ : {X : ℂ.Obj} → F.ₐ (ι2.fnc {X}) 𝔻.~ ι1.fnc {F.ₒ X}
  eq₁ {X} = lidggˢ r trid₁ ⊙ assˢ ⊙ ridgg r (F.∘ax ι2.iddom ⊙ F.id)
          where open ecategory-aux-only 𝔻
  eq₂ : {Y : 𝔻.Obj} → G.ₐ (ι1.fnc {Y}) ℂ.~ ι2.fnc {G.ₒ Y}
  eq₂ {X} = ridggˢ r ι2.iddom ⊙ ass ⊙ lidgg r trid₂
          where open ecategory-aux-only ℂ
  eq⁻¹₁ : {X : ℂ.Obj} → F.ₐ (ι2.fnc⁻¹ {X}) 𝔻.~ ι1.fnc⁻¹ {F.ₒ X}
  eq⁻¹₁ {X} = inv-uq (F.ᵢₛₒ ι2.isiso) ι1.isiso eq₁
            where open iso-props 𝔻
  eq⁻¹₂ : {Y : 𝔻.Obj} → G.ₐ (ι1.fnc⁻¹ {Y}) ℂ.~ ι2.fnc⁻¹ {G.ₒ Y}
  eq⁻¹₂ {X} = inv-uq (G.ᵢₛₒ ι1.isiso) ι2.isiso eq₂
            where open iso-props ℂ
  {-isop₁ : {X : ℂ.Obj} → iso-defs.is-iso-pair 𝔻 (ι1.fnc {F.ₒ X}) (F.ₐ (ι2.fnc⁻¹ {X}))
  isop₁ {X} = record
            { iddom = ∘e eq₁ r ⊙ (F.∘ax ι2.iddom ⊙ F.id)
            ; idcod = trid₁
            }
            where open ecategory-aux-only 𝔻
  isop₂ : {Y : 𝔻.Obj} → iso-defs.is-iso-pair ℂ (G.ₐ (ι1.fnc {Y})) (ι2.fnc⁻¹ {G.ₒ Y})
  isop₂ {Y} = ?
            where open ecategory-aux-only ℂ-}
  
  -- triangle identities for the inverses  
  trid⁻¹₁ : {X : ℂ.Obj} → F.ₐ ι2.fnc 𝔻.∘ ι1.fnc⁻¹ {F.ₒ X} 𝔻.~ 𝔻.idar (F.ₒ X)
  trid⁻¹₁ {X} = ∘e r eq₁ ⊙ ι1.idcod
              where open ecategory-aux-only 𝔻
  trid⁻¹₂ : {Y : 𝔻.Obj} → ι2.fnc {G.ₒ Y} ℂ.∘ G.ₐ ι1.fnc⁻¹ ℂ.~ ℂ.idar (G.ₒ Y)
  trid⁻¹₂ {Y} = ∘e r (eq₂ ˢ) ⊙ (G.∘ax ι1.idcod ⊙ G.id)
              where open ecategory-aux-only ℂ
-- end is-adj-equivalence-pair


inv-is-adjeqv : {ℓₒ₁ ℓₐ₁ ℓ~₁ : Level}{ℂ : ecategoryₗₑᵥ ℓₒ₁ ℓₐ₁ ℓ~₁}
                {ℓₒ₂ ℓₐ₂ ℓ~₂ : Level}{𝔻 : ecategoryₗₑᵥ ℓₒ₂ ℓₐ₂ ℓ~₂}
                {F : efunctorₗₑᵥ ℂ 𝔻}{G : efunctorₗₑᵥ 𝔻 ℂ}
                   → is-adj-equivalence-pair F G → is-adj-equivalence-pair G F
inv-is-adjeqv adjeqv = record
  { ι1 = ι2
  ; ι2 = ι1
  ; trid₁ = trid⁻¹₂
  ; trid₂ = trid⁻¹₁
  }
  where open is-adj-equivalence-pair adjeqv

adjeqvp2eqvp : {ℓₒ₁ ℓₐ₁ ℓ~₁ : Level}{ℂ : ecategoryₗₑᵥ ℓₒ₁ ℓₐ₁ ℓ~₁}
               {ℓₒ₂ ℓₐ₂ ℓ~₂ : Level}{𝔻 : ecategoryₗₑᵥ ℓₒ₂ ℓₐ₂ ℓ~₂}
               {F : efunctorₗₑᵥ ℂ 𝔻}{G : efunctorₗₑᵥ 𝔻 ℂ}
                  → is-adj-equivalence-pair F G → is-equivalence-pair F G
adjeqvp2eqvp adjeqv = record
  { ι1 = ι1
  ; ι2 = ι2
  }
  where open is-adj-equivalence-pair adjeqv

{- to be moved to basic-props?
eqv-tr : {ℓₒ₁ ℓₐ₁ ℓ~₁ : Level}{𝔸 : ecategoryₗₑᵥ ℓₒ₁ ℓₐ₁ ℓ~₁}
         {ℓₒ₂ ℓₐ₂ ℓ~₂ : Level}{𝔹 : ecategoryₗₑᵥ ℓₒ₂ ℓₐ₂ ℓ~₂}
         {ℓₒ₃ ℓₐ₃ ℓ~₃ : Level}{ℂ : ecategoryₗₑᵥ ℓₒ₃ ℓₐ₃ ℓ~₃}
         {F : efunctorₗₑᵥ 𝔸 𝔹}{G : efunctorₗₑᵥ 𝔹 ℂ}{invG : efunctorₗₑᵥ ℂ 𝔹}{H : efunctorₗₑᵥ 𝔸 ℂ}
            → is-equivalence-pair G invG → G ○ F ≅ₐ H → invG ○ H ≅ₐ F
eqv-tr {F = F} {G} {invG} {H} eqvG tr =
  natiso-vcmp ○lid
              (natiso-vcmp (natiso-hcmp ι2 ≅ₐrefl)
                           (natiso-vcmp (○ass {F = F} {G} {invG})
                                        (natiso-hcmp (≅ₐrefl {F = invG}) (≅ₐsym tr))))
               where open is-equivalence-pair eqvG
-}

record is-equivalence {ℓₒ₁ ℓₐ₁ ℓ~₁ : Level}{ℂ : ecategoryₗₑᵥ ℓₒ₁ ℓₐ₁ ℓ~₁}
                      {ℓₒ₂ ℓₐ₂ ℓ~₂ : Level}{𝔻 : ecategoryₗₑᵥ ℓₒ₂ ℓₐ₂ ℓ~₂}
                      (F : efunctorₗₑᵥ ℂ 𝔻)
                      : Set (ecat.ℓₐₗₗ ℂ ⊔ ecat.ℓₐₗₗ 𝔻)
                      where
  field
    inv : efunctorₗₑᵥ 𝔻 ℂ
    iseqvp : is-equivalence-pair F inv
  open is-equivalence-pair iseqvp public

record is-adj-equivalence {ℓₒ₁ ℓₐ₁ ℓ~₁ : Level}{ℂ : ecategoryₗₑᵥ ℓₒ₁ ℓₐ₁ ℓ~₁}
                          {ℓₒ₂ ℓₐ₂ ℓ~₂ : Level}{𝔻 : ecategoryₗₑᵥ ℓₒ₂ ℓₐ₂ ℓ~₂}
                          (F : efunctorₗₑᵥ ℂ 𝔻)
                          : Set (ecat.ℓₐₗₗ ℂ ⊔ ecat.ℓₐₗₗ 𝔻) where
  field
    inv : efunctorₗₑᵥ 𝔻 ℂ
    isadjeqvp : is-adj-equivalence-pair F inv --iseqvp
  open is-adj-equivalence-pair isadjeqvp public


adjeqv2eqv : {ℓₒ₁ ℓₐ₁ ℓ~₁ : Level}{ℂ : ecategoryₗₑᵥ ℓₒ₁ ℓₐ₁ ℓ~₁}
             {ℓₒ₂ ℓₐ₂ ℓ~₂ : Level}{𝔻 : ecategoryₗₑᵥ ℓₒ₂ ℓₐ₂ ℓ~₂}
             {F : efunctorₗₑᵥ ℂ 𝔻}
                → is-adj-equivalence F → is-equivalence F
adjeqv2eqv adjeqv = record
  { inv = inv
  ; iseqvp = adjeqvp2eqvp isadjeqvp
  }
  where open is-adj-equivalence adjeqv

{-
adjeqv-cmp : {𝔹 ℂ 𝔻 : ecategory}{F : efunctor 𝔹 ℂ}{G : efunctor ℂ 𝔻}
               → is-adj-equivalence F → is-adj-equivalence G
                 → is-adj-equivalence (G ○ F)
adjeqv-cmp aeqvF aeqvG = record
  { inv = F.inv ○ G.inv
  ; isadjeqvp = record
              { ι1 = {!!}
              ; ι2 = {!!}
              ; trid₁ = {!!}
              ; trid₂ = {!!}
              }
  }
  where module F = is-adj-equivalence aeqvF
        module G = is-adj-equivalence aeqvG
-}

infix 10 _≡ᶜᵃᵗ_
record _≡ᶜᵃᵗ_ {ℓₒ₁ ℓₐ₁ ℓ~₁ : Level}(ℂ : ecategoryₗₑᵥ ℓₒ₁ ℓₐ₁ ℓ~₁)
             {ℓₒ₂ ℓₐ₂ ℓ~₂ : Level}(𝔻 : ecategoryₗₑᵥ ℓₒ₂ ℓₐ₂ ℓ~₂)
             : Set (ecat.ℓₐₗₗ ℂ ⊔ ecat.ℓₐₗₗ 𝔻) where
  field
    a12 : efunctorₗₑᵥ ℂ 𝔻
    a21 : efunctorₗₑᵥ 𝔻 ℂ
    iseqvpair : is-equivalence-pair a12 a21
  open is-equivalence-pair iseqvpair public
    
               

-- Other kind of functors

record is-full {ℓₒ₁ ℓₐ₁ ℓ~₁ : Level}{ℂ : ecategoryₗₑᵥ ℓₒ₁ ℓₐ₁ ℓ~₁}
               {ℓₒ₂ ℓₐ₂ ℓ~₂ : Level}{𝔻 : ecategoryₗₑᵥ ℓₒ₂ ℓₐ₂ ℓ~₂}
               (F : efunctorₗₑᵥ ℂ 𝔻)
               : Set (ecat.ℓₙₒ~ ℂ ⊔ ecat.ℓₕₒₘ 𝔻)
               where
  private
    module ℂ = ecat ℂ
    module 𝔻 = ecat 𝔻
    module F = efunctorₗₑᵥ F
  field
    ar : {X Y : ℂ.Obj} → || 𝔻.Hom (F.ₒ X) (F.ₒ Y) || → || ℂ.Hom X Y ||
    pf : {X Y : ℂ.Obj} {g : || 𝔻.Hom (F.ₒ X) (F.ₒ Y) ||}
                    → F.ₐ (ar g) 𝔻.~ g
  pfˢ : {X Y : ℂ.Obj} {g : || 𝔻.Hom (F.ₒ X) (F.ₒ Y) ||}
                    → g 𝔻.~ F.ₐ (ar g)
  pfˢ =  pf ˢ
      where open ecategory-aux-only 𝔻
  pfg : {X Y : ℂ.Obj} {g g' : || 𝔻.Hom (F.ₒ X) (F.ₒ Y) ||}
                    → g 𝔻.~ g' → F.ₐ (ar g) 𝔻.~ g'
  pfg eq = pf ⊙ eq
         where open ecategory-aux-only 𝔻
  pfgˢ : {X Y : ℂ.Obj} {g g' : || 𝔻.Hom (F.ₒ X) (F.ₒ Y) ||}
                    → g 𝔻.~ g' → g' 𝔻.~ F.ₐ (ar g)
  pfgˢ eq = pfg eq ˢ
          where open ecategory-aux-only 𝔻

full-cmp : {ℓₒ₁ ℓₐ₁ ℓ~₁ : Level}{𝔹 : ecategoryₗₑᵥ ℓₒ₁ ℓₐ₁ ℓ~₁}
           {ℓₒ₂ ℓₐ₂ ℓ~₂ : Level}{ℂ : ecategoryₗₑᵥ ℓₒ₂ ℓₐ₂ ℓ~₂}
           {ℓₒ₃ ℓₐ₃ ℓ~₃ : Level}{𝔻 : ecategoryₗₑᵥ ℓₒ₃ ℓₐ₃ ℓ~₃}
           {F : efunctorₗₑᵥ 𝔹 ℂ}{G : efunctorₗₑᵥ ℂ 𝔻}
               → is-full F → is-full G → is-full (G ○ F)
full-cmp {𝔻 = 𝔻} {F} {G} fullF fullG = record
  { ar = λ k → F.ar (G.ar k)
  ; pf = λ {_} {_} {k} → G.ext F.pf ⊙ G.pf
  }
  where module F = is-full fullF
        module G where
          open efunctor-aux G public
          open is-full fullG public
        open ecategory-aux-only 𝔻 using (_⊙_)

full-ext : {ℓₒ₁ ℓₐ₁ ℓ~₁ : Level}{ℂ : ecategoryₗₑᵥ ℓₒ₁ ℓₐ₁ ℓ~₁}
           {ℓₒ₂ ℓₐ₂ ℓ~₂ : Level}{𝔻 : ecategoryₗₑᵥ ℓₒ₂ ℓₐ₂ ℓ~₂}
           {F G : efunctorₗₑᵥ ℂ 𝔻}
               → is-full F → F ≅ₐ G → is-full G
full-ext {𝔻 = 𝔻} {F} {G} fullF α = record
  { ar = λ g → F.full.ar (α.fnc⁻¹ ∘ g ∘ α.fnc)
  ; pf = λ {X} {Y} {g} → ~proof
            G.ₐ (F.full.ar (α.fnc⁻¹ ∘ g ∘ α.fnc))                     ~[ α.C2Dₗ ] /
            (α.fnc ∘ F.ₐ (F.full.ar (α.fnc⁻¹ ∘ g ∘ α.fnc))) ∘ α.fnc⁻¹  ~[ ∘e r (∘e  F.full.pf r) ] /
            (α.fnc ∘ (α.fnc⁻¹ ∘ g ∘ α.fnc)) ∘ α.fnc⁻¹                  ~[ ∘e r ass ⊙ assˢ ⊙ ∘e assˢ r ] /
            (α.fnc ∘ α.fnc⁻¹) ∘ g ∘ α.fnc ∘ α.fnc⁻¹                ~[ lidgg (ridgg r α.idcod) α.idcod ]∎
            g ∎
  }
  where module F where
          module full = is-full fullF
          open efunctor-aux F public
        module G = efunctor-aux G
        module α = natural-iso α
        open ecategory-aux 𝔻



record is-faithful {ℓₒ₁ ℓₐ₁ ℓ~₁ : Level}{ℂ : ecategoryₗₑᵥ ℓₒ₁ ℓₐ₁ ℓ~₁}
                   {ℓₒ₂ ℓₐ₂ ℓ~₂ : Level}{𝔻 : ecategoryₗₑᵥ ℓₒ₂ ℓₐ₂ ℓ~₂}
                   (F : efunctorₗₑᵥ ℂ 𝔻)
                   : Set (ecat.ℓₐₗₗ ℂ ⊔ ecat.ℓ~ 𝔻)
                   where
  private
    module ℂ = ecat ℂ
    module 𝔻 = ecat 𝔻
    module F = efctr F
  field
    faith-pf : {X Y : ℂ.Obj} {f g : || ℂ.Hom X Y ||}
                  → F.ₐ f 𝔻.~ F.ₐ g → f ℂ.~ g

faith-cmp : {𝔹 ℂ 𝔻 : ecategory}{F : efunctor 𝔹 ℂ}{G : efunctor ℂ 𝔻}
               → is-faithful F → is-faithful G
                 → is-faithful (G ○ F)
faith-cmp faithF faithG = record
  { faith-pf = λ pf → F.faith-pf (G.faith-pf pf)
  }
  where module F = is-faithful faithF
        module G = is-faithful faithG

faith-ext : {ℂ 𝔻 : ecategory}{F G : efunctor ℂ 𝔻}
               → is-faithful F → F ≅ₐ G → is-faithful G
faith-ext {ℂ} {𝔻} {F} {G} faithF α = record
  { faith-pf = λ {_} {_} {f} {g}  pf → F.faith-pf (~proof
             F.ₐ f                   ~[ α.D2Cᵣ ] /
             α.fnc⁻¹ ∘ G.ₐ f ∘ α.fnc  ~[ ∘e (∘e r pf) r ] /
             α.fnc⁻¹ ∘ G.ₐ g ∘ α.fnc  ~[  α.D2Cᵣˢ ]∎
             F.ₐ g ∎)
  }
  where module F where
          open is-faithful faithF public
          open efunctor-aux F public
        module G = efunctor-aux G
        module α = natural-iso α
        open ecategory-aux 𝔻


record is-ess-surjective-ob {ℓₒ₁ ℓₐ₁ ℓ~₁ : Level}{ℂ : ecategoryₗₑᵥ ℓₒ₁ ℓₐ₁ ℓ~₁}
                            {ℓₒ₂ ℓₐ₂ ℓ~₂ : Level}{𝔻 : ecategoryₗₑᵥ ℓₒ₂ ℓₐ₂ ℓ~₂}
                            (F : efunctorₗₑᵥ ℂ 𝔻)
                            : Set (ecat.ℓₒ ℂ ⊔ ecat.ℓₐₗₗ 𝔻)
                            where
  private
    module ℂ = ecat ℂ
    module 𝔻 = ecat 𝔻
    module F = efunctorₗₑᵥ F
  open iso-defs 𝔻
  field
    ob : 𝔻.Obj → ℂ.Obj
    ar : (Y : 𝔻.Obj) → || 𝔻.Hom (F.ₒ (ob Y)) Y ||
    iso : (Y : 𝔻.Obj) → is-iso (ar Y)


private
  module cat-iso {ℓₒ ℓₐ ℓ~ : Level}(𝕏 : ecategoryₗₑᵥ ℓₒ ℓₐ ℓ~) where
    open ecat 𝕏 public
    open iso-defs 𝕏 public


record is-conservative {ℓₒ₁ ℓₐ₁ ℓ~₁ : Level}{ℂ : ecategoryₗₑᵥ ℓₒ₁ ℓₐ₁ ℓ~₁}
                       {ℓₒ₂ ℓₐ₂ ℓ~₂ : Level}{𝔻 : ecategoryₗₑᵥ ℓₒ₂ ℓₐ₂ ℓ~₂}
                       (F : efunctorₗₑᵥ ℂ 𝔻)
                       : Set (ecat.ℓₐₗₗ ℂ ⊔ ecat.ℓₕₒₘ 𝔻)
                       where
  private
    module ℂ = cat-iso ℂ
    module 𝔻 = cat-iso 𝔻
    module F = efunctorₗₑᵥ F
  field
    refl-iso : {A B : ℂ.Obj}{f : || ℂ.Hom A B ||} → 𝔻.is-iso (F.ₐ f) → ℂ.is-iso f


f&f-is-conservative : {ℓₒ₁ ℓₐ₁ ℓ~₁ : Level}{ℂ : ecategoryₗₑᵥ ℓₒ₁ ℓₐ₁ ℓ~₁}
                      {ℓₒ₂ ℓₐ₂ ℓ~₂ : Level}{𝔻 : ecategoryₗₑᵥ ℓₒ₂ ℓₐ₂ ℓ~₂}
                      {F : efunctorₗₑᵥ ℂ 𝔻} → is-full F → is-faithful F
                        → is-conservative F
f&f-is-conservative {ℂ = ℂ} {𝔻 = 𝔻} {F} isfull isfaith = record
  { refl-iso = λ isiso → record
             { invf = inv isiso
             ; isisopair = isop isiso
             }
  }
  where module ℂ = cat-iso ℂ
        module 𝔻 = cat-iso 𝔻
        module F where
          open efunctor-aux F public
          module full = is-full isfull
          open is-faithful isfaith public
        inv : {A B : ℂ.Obj}{f : || ℂ.Hom A B ||}
                 → 𝔻.is-iso (F.ₐ f) → || ℂ.Hom B A ||
        inv isiso = F.full.ar Ff.⁻¹
                  where module Ff = 𝔻.is-iso isiso
        Finv~invF : {A B : ℂ.Obj}{f : || ℂ.Hom A B ||}(isiso : 𝔻.is-iso (F.ₐ f))
                       → F.ₐ (inv isiso) 𝔻.~ 𝔻.is-iso.invf isiso
        Finv~invF isiso = F.full.pf
        isop : {A B : ℂ.Obj}{f : || ℂ.Hom A B ||}(isiso : 𝔻.is-iso (F.ₐ f))
                  → ℂ.is-iso-pair f (inv isiso)
        isop {A} {B} {f = f} isiso = record
          { iddom = F.faith-pf (F.cmpˢ f (inv isiso) ⊙ (∘e r (Finv~invF isiso) ⊙ Ff.iddom ⊙ F.idˢ))
          ; idcod = F.faith-pf (~proof F.ₐ (f ℂ.∘ inv isiso)      ~[ F.cmpˢ (inv isiso) f ] /
                                       F.ₐ f 𝔻.∘ F.ₐ (inv isiso)  ~[ ∘e (Finv~invF isiso) r ] /
                                       F.ₐ f 𝔻.∘ Ff.⁻¹            ~[ Ff.idcod ⊙ F.idˢ ]∎
                                       F.ₐ (ℂ.idar B) ∎)
          }
          where open ecategory-aux-only 𝔻
                module Ff = 𝔻.is-iso isiso


f&f-creates-isos : {ℓₒ₁ ℓₐ₁ ℓ~₁ : Level}{ℂ : ecategoryₗₑᵥ ℓₒ₁ ℓₐ₁ ℓ~₁}
                   {ℓₒ₂ ℓₐ₂ ℓ~₂ : Level}{𝔻 : ecategoryₗₑᵥ ℓₒ₂ ℓₐ₂ ℓ~₂}
                   {F : efunctorₗₑᵥ ℂ 𝔻} → is-full F → is-faithful F → {X Y : ecat.Obj ℂ}
                     → cat-iso._≅ₒ_ 𝔻 (efctr.ₒ F X)  (efctr.ₒ F Y) → cat-iso._≅ₒ_ ℂ X Y
f&f-creates-isos {ℂ = ℂ} {𝔻 = 𝔻} {F} isfull isfaith {X} {Y} isoF = record
  { a12 = a12
  ; a21 = a21
  ; isop = record
         { iddom = F.faith-pf (~proof F.ₐ (a21 ℂ.∘ a12)        ~[ F.cmpˢ a12 a21 ] /
                                      F.ₐ a21 𝔻.∘ F.ₐ a12      ~[ ∘e F.full.pf F.full.pf ] /
                                      ni.a21 𝔻.∘ ni.a12       ~[ ni.iddom ⊙ F.idˢ {X} ]∎
                                      F.ₐ (ℂ.idar X) ∎)
         ; idcod = F.faith-pf (~proof F.ₐ (a12 ℂ.∘ a21)        ~[ F.cmpˢ a21 a12 ] /
                                      F.ₐ a12 𝔻.∘ F.ₐ a21      ~[ ∘e F.full.pf F.full.pf ] /
                                      ni.a12 𝔻.∘ ni.a21       ~[ ni.idcod ⊙ F.idˢ {Y} ]∎
                                      F.ₐ (ℂ.idar Y) ∎)
         }
  }
  where open ecategory-aux-only 𝔻
        module ℂ = cat-iso ℂ
        module 𝔻 = cat-iso 𝔻
        module F where
          open efunctor-aux F public
          module full = is-full isfull
          open is-faithful isfaith public
        module ni = 𝔻._≅ₒ_ isoF
        a12 : || ℂ.Hom X Y ||
        a12 = F.full.ar ni.a12
        a21 : || ℂ.Hom Y X ||
        a21 = F.full.ar ni.a21




-- Essential equivalences

record is-ess-equivalence {ℓₒ₁ ℓₐ₁ ℓ~₁ : Level}{ℂ : ecategoryₗₑᵥ ℓₒ₁ ℓₐ₁ ℓ~₁}
                          {ℓₒ₂ ℓₐ₂ ℓ~₂ : Level}{𝔻 : ecategoryₗₑᵥ ℓₒ₂ ℓₐ₂ ℓ~₂}
                          (F : efunctorₗₑᵥ ℂ 𝔻)
                          : Set (ecat.ℓₐₗₗ ℂ ⊔ ecat.ℓₐₗₗ 𝔻)
                          where
  private
    module ℂ = ecat ℂ
    module 𝔻 = ecat 𝔻
    module F = efunctorₗₑᵥ F
  field
    isfull : is-full F
    isfaithful : is-faithful F
    isesurjobj : is-ess-surjective-ob F
  module isfull = is-full isfull
  module isesurj = is-ess-surjective-ob isesurjobj
  open is-faithful isfaithful renaming (faith-pf to isfaith) public
