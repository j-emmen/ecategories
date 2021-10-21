
{-# OPTIONS --without-K #-}

module ecats.functors.defs.basic-defs where

open import ecats.basic-defs.ecat-def&not
open import ecats.basic-defs.isomorphism
open import ecats.functors.defs.efunctor-d&n
open import ecats.functors.defs.natural-transformation



-- Adjunctions

record adjunction {ℂ 𝔻 : ecategory} (L : efunctor ℂ 𝔻) (R : efunctor 𝔻 ℂ) : Set₁ where
  private
    module ℂ = ecategory ℂ
    module 𝔻 = ecategory 𝔻
    module L = efunctor L
    module R = efunctor R
  field
    η : natural-transformation IdF (R ○ L)
    ε : natural-transformation (L ○ R) IdF
  open natural-transformation ε renaming (fnc to ε-f; nat to ε-n)
  open natural-transformation η renaming (fnc to η-f; nat to η-n)
  field
    trid₁ : {X : ℂ.Obj} → ε-f {L.ₒ X} 𝔻.∘ L.ₐ η-f 𝔻.~ 𝔻.idar (L.ₒ X)
    trid₂ : {Y : 𝔻.Obj} → R.ₐ ε-f ℂ.∘ η-f {R.ₒ Y} ℂ.~ ℂ.idar (R.ₒ Y)

infix 3 _⊣_

_⊣_ : {ℂ 𝔻 : ecategory} → (L : efunctor ℂ 𝔻) → (R : efunctor 𝔻 ℂ) → Set₁
L ⊣ R = adjunction L R


-- Equivalences

record is-equivalence-pair {ℂ 𝔻 : ecategory} (F : efunctor ℂ 𝔻) (G : efunctor 𝔻 ℂ) : Set₁ where
  private
    module ℂ = ecategory ℂ
    module 𝔻 = ecategory 𝔻
    module F = efunctor F
    module G = efunctor G
  field
    ι1 : natural-iso (F ○ G) IdF
    ι2 : natural-iso (G ○ F) IdF
  module ι1 = natural-iso ι1
  module ι2 = natural-iso ι2

inv-is-eqv : {ℂ 𝔻 : ecategory}{F : efunctor ℂ 𝔻}{G : efunctor 𝔻 ℂ}
                  → is-equivalence-pair F G → is-equivalence-pair G F
inv-is-eqv eqv = record
  { ι1 = ι2
  ; ι2 = ι1
  }
  where open is-equivalence-pair eqv


record is-adj-equivalence-pair {ℂ 𝔻 : ecategory}(F : efunctor ℂ 𝔻)(G : efunctor 𝔻 ℂ)
                               --(eqvp : is-equivalence-pair F G)
                               : Set₁ where
  private
    module ℂ = ecategory ℂ
    module 𝔻 = ecategory 𝔻
    module F = efunctor-aux F
    module G = efunctor-aux G
  field
    ι1 : natural-iso (F ○ G) IdF
    ι2 : natural-iso (G ○ F) IdF
  module ι1 = natural-iso ι1
  module ι2 = natural-iso ι2
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
  eq⁻¹₁ {X} = inv-uqg (F.ᵢₛₒ ι2.isiso) ι1.isiso eq₁
            where open iso-defs 𝔻
  eq⁻¹₂ : {Y : 𝔻.Obj} → G.ₐ (ι1.fnc⁻¹ {Y}) ℂ.~ ι2.fnc⁻¹ {G.ₒ Y}
  eq⁻¹₂ {X} = inv-uqg (G.ᵢₛₒ ι1.isiso) ι2.isiso eq₂
            where open iso-defs ℂ

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


inv-is-adjeqv : {ℂ 𝔻 : ecategory}{F : efunctor ℂ 𝔻}{G : efunctor 𝔻 ℂ}
                   → is-adj-equivalence-pair F G → is-adj-equivalence-pair G F
inv-is-adjeqv adjeqv = record
  { ι1 = ι2
  ; ι2 = ι1
  ; trid₁ = trid⁻¹₂
  ; trid₂ = trid⁻¹₁
  }
  where open is-adj-equivalence-pair adjeqv



adjeqvp2eqvp : {ℂ 𝔻 : ecategory}{F : efunctor ℂ 𝔻}{G : efunctor 𝔻 ℂ}
                  → is-adj-equivalence-pair F G → is-equivalence-pair F G
adjeqvp2eqvp adjeqv = record
  { ι1 = ι1
  ; ι2 = ι2
  }
  where open is-adj-equivalence-pair adjeqv


eqv-tr : {𝔸 𝔹 ℂ : ecategory}{F : efunctor 𝔸 𝔹}
         {G : efunctor 𝔹 ℂ}{invG : efunctor ℂ 𝔹}{H : efunctor 𝔸 ℂ}
            → is-equivalence-pair G invG → G ○ F ≅ₐ H → invG ○ H ≅ₐ F
eqv-tr {F = F} {G} {invG} {H} eqvG tr =
  natiso-vcmp ○lid
              (natiso-vcmp (natiso-hcmp ι2 ≅ₐrefl)
                           (natiso-vcmp (○ass {F = F} {G} {invG})
                                        (natiso-hcmp (≅ₐrefl {F = invG}) (≅ₐsym tr))))
               where open is-equivalence-pair eqvG


record is-equivalence {ℂ 𝔻 : ecategory} (F : efunctor ℂ 𝔻) : Set₁ where
  field
    invF : efunctor 𝔻 ℂ
    iseqvp : is-equivalence-pair F invF
  open is-equivalence-pair iseqvp public

record is-adj-equivalence {ℂ 𝔻 : ecategory}(F : efunctor ℂ 𝔻) : Set₁ where
  field
    invF : efunctor 𝔻 ℂ
    isadjeqvp : is-adj-equivalence-pair F invF --iseqvp
  open is-adj-equivalence-pair isadjeqvp public


adjeqv2eqv : {ℂ 𝔻 : ecategory}{F : efunctor ℂ 𝔻}
                → is-adj-equivalence F → is-equivalence F
adjeqv2eqv adjeqv = record
  { invF = invF
  ; iseqvp = adjeqvp2eqvp isadjeqvp
  }
  where open is-adj-equivalence adjeqv




-- Other properties of funtors

record is-full {ℂ 𝔻 : ecategory} (F : efunctor ℂ 𝔻) : Set₁ where
  private
    module ℂ = ecategory ℂ
    module 𝔻 = ecategory 𝔻
    module F = efunctor F
  field
    full-ar : {X Y : ℂ.Obj} → || 𝔻.Hom (F.ₒ X) (F.ₒ Y) || → || ℂ.Hom X Y ||
    full-pf : {X Y : ℂ.Obj} {g : || 𝔻.Hom (F.ₒ X) (F.ₒ Y) ||}
                    → F.ₐ (full-ar g) 𝔻.~ g
  full-pfˢ : {X Y : ℂ.Obj} {g : || 𝔻.Hom (F.ₒ X) (F.ₒ Y) ||}
                    → g 𝔻.~ F.ₐ (full-ar g)
  full-pfˢ =  full-pf ˢ
           where open ecategory-aux-only 𝔻
  full-pfg : {X Y : ℂ.Obj} {g g' : || 𝔻.Hom (F.ₒ X) (F.ₒ Y) ||}
                    → g 𝔻.~ g' → F.ₐ (full-ar g) 𝔻.~ g'
  full-pfg pf = full-pf ⊙ pf
              where open ecategory-aux-only 𝔻
  full-pfgˢ : {X Y : ℂ.Obj} {g g' : || 𝔻.Hom (F.ₒ X) (F.ₒ Y) ||}
                    → g 𝔻.~ g' → g' 𝔻.~ F.ₐ (full-ar g)
  full-pfgˢ pf = full-pfg pf ˢ
              where open ecategory-aux-only 𝔻


record is-faithful {ℂ 𝔻 : ecategory} (F : efunctor ℂ 𝔻) : Set₁ where
  private
    module ℂ = ecategory ℂ
    module 𝔻 = ecategory 𝔻
    module F = efunctor F
  field
    faith-pf : {X Y : ℂ.Obj} {f g : || ℂ.Hom X Y ||}
                  → F.ₐ f 𝔻.~ F.ₐ g → f ℂ.~ g


record is-ess-surjective-ob {ℂ 𝔻 : ecategory} (F : efunctor ℂ 𝔻) : Set₁ where
  private
    module ℂ = ecategory ℂ
    module 𝔻 = ecategory 𝔻
    module F = efunctor F
  open iso-defs 𝔻
  field
    ob : 𝔻.Obj → ℂ.Obj
    ar : (Y : 𝔻.Obj) → || 𝔻.Hom (F.ₒ (ob Y)) Y ||
    iso : (Y : 𝔻.Obj) → is-iso (ar Y)



-- Essential equivalences

record is-ess-equivalence {ℂ 𝔻 : ecategory} (F : efunctor ℂ 𝔻) : Set₁ where
  field
    isfull : is-full F
    isfaithful : is-faithful F
    isesurjobj : is-ess-surjective-ob F
  module isfull = is-full isfull
  module isesurj = is-ess-surjective-ob isesurjobj
  open is-faithful isfaithful renaming (faith-pf to isfaith) public
