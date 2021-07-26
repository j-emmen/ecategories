
{-# OPTIONS --without-K #-}

module ecats.functors.defs.basic-defs where

open import ecats.basic-defs.ecat-def&not
open import ecats.basic-defs.isomorphism
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


record is-equivalence {ℓₒ₁ ℓₐ₁ ℓ~₁ : Level}{ℂ : ecategoryₗₑᵥ ℓₒ₁ ℓₐ₁ ℓ~₁}
                      {ℓₒ₂ ℓₐ₂ ℓ~₂ : Level}{𝔻 : ecategoryₗₑᵥ ℓₒ₂ ℓₐ₂ ℓ~₂}
                      (F : efunctorₗₑᵥ ℂ 𝔻)
                      : Set (ecat.ℓₐₗₗ ℂ ⊔ ecat.ℓₐₗₗ 𝔻)
                      where
  field
    invF : efunctorₗₑᵥ 𝔻 ℂ
    iseqv : is-equivalence-pair F invF
  open is-equivalence-pair iseqv public


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
          open is-full isfull public
          open is-faithful isfaith public
        inv : {A B : ℂ.Obj}{f : || ℂ.Hom A B ||}
                 → 𝔻.is-iso (F.ₐ f) → || ℂ.Hom B A ||
        inv isiso = F.full-ar Ff.⁻¹
                  where module Ff = 𝔻.is-iso isiso
        Finv~invF : {A B : ℂ.Obj}{f : || ℂ.Hom A B ||}(isiso : 𝔻.is-iso (F.ₐ f))
                       → F.ₐ (inv isiso) 𝔻.~ 𝔻.is-iso.invf isiso
        Finv~invF isiso = F.full-pf
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
                                      F.ₐ a21 𝔻.∘ F.ₐ a12      ~[ ∘e F.full-pf F.full-pf ] /
                                      ni.a21 𝔻.∘ ni.a12       ~[ ni.iddom ⊙ F.idˢ {X} ]∎
                                      F.ₐ (ℂ.idar X) ∎)
         ; idcod = F.faith-pf (~proof F.ₐ (a12 ℂ.∘ a21)        ~[ F.cmpˢ a21 a12 ] /
                                      F.ₐ a12 𝔻.∘ F.ₐ a21      ~[ ∘e F.full-pf F.full-pf ] /
                                      ni.a12 𝔻.∘ ni.a21       ~[ ni.idcod ⊙ F.idˢ {Y} ]∎
                                      F.ₐ (ℂ.idar Y) ∎)
         }
  }
  where open ecategory-aux-only 𝔻
        module ℂ = cat-iso ℂ
        module 𝔻 = cat-iso 𝔻
        module F where
          open efunctor-aux F public
          open is-full isfull public
          open is-faithful isfaith public
        module ni = 𝔻._≅ₒ_ isoF
        a12 : || ℂ.Hom X Y ||
        a12 = F.full-ar ni.a12
        a21 : || ℂ.Hom Y X ||
        a21 = F.full-ar ni.a21




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
