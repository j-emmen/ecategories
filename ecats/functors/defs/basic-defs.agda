
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

record is-adj-equivalence-pair {ℂ 𝔻 : ecategory}(F : efunctor ℂ 𝔻)(G : efunctor 𝔻 ℂ)
                               --(eqvp : is-equivalence-pair F G)
                               : Set₁ where
  private
    module ℂ = ecategory ℂ
    module 𝔻 = ecategory 𝔻
    module F = efunctor-aux F
    module G = efunctor-aux G
  --open is-equivalence-pair eqvp
  field
    ι1 : natural-iso (F ○ G) IdF
    ι2 : natural-iso (G ○ F) IdF
  module ι1 = natural-iso ι1
  module ι2 = natural-iso ι2
  -- in this case the triangular identities say that
  -- F ι2 ~ ι1 F and G ι1 ~ ι2 G, respectively.
  field
    trid₁ : {X : ℂ.Obj} → ι1.fnc {F.ₒ X} 𝔻.∘ F.ₐ ι2.fnc⁻¹ 𝔻.~ 𝔻.idar (F.ₒ X)
    trid₂ : {Y : 𝔻.Obj} → G.ₐ ι1.fnc ℂ.∘ ι2.fnc⁻¹ {G.ₒ Y} ℂ.~ ℂ.idar (G.ₒ Y)
  -- triangle identities for the inverses  
  trid⁻¹₁ : {X : ℂ.Obj} → F.ₐ ι2.fnc 𝔻.∘ ι1.fnc⁻¹ {F.ₒ X} 𝔻.~ 𝔻.idar (F.ₒ X)
  trid⁻¹₁ {X} = ~proof F.ₐ ι2.fnc 𝔻.∘ ι1.fnc⁻¹ {F.ₒ X}            ~[ ridggˢ r trid₁ ⊙ assˢ ] /
                       F.ₐ ι2.fnc 𝔻.∘ ι1.fnc⁻¹ {F.ₒ X} 𝔻.∘ ι1.fnc {F.ₒ X} 𝔻.∘ F.ₐ ι2.fnc⁻¹
                                                                  ~[ ∘e (ass ⊙ lidgg r ι1.iddom) r ] /
                       F.ₐ ι2.fnc 𝔻.∘ F.ₐ ι2.fnc⁻¹                ~[ F.∘ax ι2.idcod ⊙ F.id ]∎
                       𝔻.idar (F.ₒ X) ∎
              where open ecategory-aux-only 𝔻
  trid⁻¹₂ : {Y : 𝔻.Obj} → ι2.fnc {G.ₒ Y} ℂ.∘ G.ₐ ι1.fnc⁻¹ ℂ.~ ℂ.idar (G.ₒ Y)
  trid⁻¹₂ {Y} = ~proof ι2.fnc {G.ₒ Y} ℂ.∘ G.ₐ ι1.fnc⁻¹         ~[ ridggˢ r trid₂ ⊙ assˢ ] /
                       ι2.fnc {G.ₒ Y} ℂ.∘ G.ₐ ι1.fnc⁻¹ ℂ.∘ G.ₐ ι1.fnc ℂ.∘ ι2.fnc⁻¹ {G.ₒ Y}
                                      ~[ ∘e (ass ⊙ lidgg r (G.∘ax ι1.iddom ⊙ G.id)) r ] /
                       ι2.fnc {G.ₒ Y} ℂ.∘ ι2.fnc⁻¹ {G.ₒ Y}                  ~[ ι2.idcod ]∎
                       ℂ.idar (G.ₒ Y) ∎
              where open ecategory-aux-only ℂ


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
  {-field
    eqv : is-equivalence F
  open is-equivalence eqv public-}
  field
    invF : efunctor 𝔻 ℂ
    isadj : is-adj-equivalence-pair F invF --iseqvp
  open is-adj-equivalence-pair isadj public


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
  private
    module ℂ = ecategory ℂ
    module 𝔻 = ecategory 𝔻
    module F = efunctor F
  field
    isfull : is-full F
    isfaithful : is-faithful F
    isesurjobj : is-ess-surjective-ob F
