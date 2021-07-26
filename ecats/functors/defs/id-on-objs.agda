
{-# OPTIONS --without-K #-}

module ecats.functors.defs.id-on-objs where

open import tt-basics.setoids using (setoid)
open import ecats.basic-defs.ecat-def&not
open import ecats.basic-defs.isomorphism
open import ecats.basic-props.isomorphism
open import ecats.functors.defs.efunctor-d&n
open import ecats.functors.defs.basic-defs
open import ecats.functors.defs.natural-transformation
open import ecats.functors.defs.natural-iso


-- Identity-on-objects functors and isomorphic categories over the same objects

mkecat : {ℓₒ ℓₐ ℓ~ : Level}{Obj : Set ℓₒ}{Hom : Obj → Obj → setoid {ℓₐ} {ℓ~}}
             → is-ecategory Obj Hom → ecategoryₗₑᵥ ℓₒ ℓₐ ℓ~
mkecat {Obj = Obj} {Hom} isecat = record
  { Obj = Obj
  ; Hom = Hom
  ; isecat = isecat
  }



record idobj-efunctor {ℓₒ : Level}{Obj : Set ℓₒ}
                      {ℓₐ₁ ℓ~₁ : Level}{Hom1 : Obj → Obj → setoid {ℓₐ₁} {ℓ~₁}}
                      (isecat1 : is-ecategory Obj Hom1)
                      {ℓₐ₂ ℓ~₂ : Level}{Hom2 : Obj → Obj → setoid {ℓₐ₂} {ℓ~₂}}
                      (isecat2 : is-ecategory Obj Hom2)
                      : Set (ℓₒ ⊔ ℓₐ₁ ⊔ ℓ~₁ ⊔ ℓₐ₂ ⊔ ℓ~₂) where
  open efunctor-defs (mkecat isecat1) (mkecat isecat2)
  field
    ₐ : {A B : Obj} → || Hom1 A B || → || Hom2 A B ||
    isfctr : is-functorial ₐ
  open is-functorial isfctr public


idobj-efunctor-is-efunctor : {ℓₒ : Level}{Obj : Set ℓₒ}
                             {ℓₐ₁ ℓ~₁ : Level}{Hom1 : Obj → Obj → setoid {ℓₐ₁} {ℓ~₁}}
                             {isecat1 : is-ecategory Obj Hom1}
                             {ℓₐ₂ ℓ~₂ : Level}{Hom2 : Obj → Obj → setoid {ℓₐ₂} {ℓ~₂}}
                             {isecat2 : is-ecategory Obj Hom2}
                               → idobj-efunctor isecat1 isecat2
                                 → efunctorₗₑᵥ (mkecat isecat1) (mkecat isecat2)
idobj-efunctor-is-efunctor {isecat1 = isecat1} {isecat2 = isecat2} F = record
  { FObj = λ X → X
  ; FHom = F.ₐ
  ; isF = record
        { ext = F.ext
        ; id = F.id
        ; cmp = F.cmp
        }
  }
  where module F = idobj-efunctor F

module idobj-efunctor-aux-only {ℓₒ : Level}{Obj : Set ℓₒ}
                               {ℓₐ₁ ℓ~₁ : Level}{Hom1 : Obj → Obj → setoid {ℓₐ₁} {ℓ~₁}}
                               {isecat1 : is-ecategory Obj Hom1}
                               {ℓₐ₂ ℓ~₂ : Level}{Hom2 : Obj → Obj → setoid {ℓₐ₂} {ℓ~₂}}
                               {isecat2 : is-ecategory Obj Hom2}
                               (F : idobj-efunctor isecat1 isecat2)
                               where
  open efunctor-aux-only (idobj-efunctor-is-efunctor F) public
-- end idobj-efunctor-aux-only

module idobj-efunctor-aux {ℓₒ : Level}{Obj : Set ℓₒ}
                          {ℓₐ₁ ℓ~₁ : Level}{Hom1 : Obj → Obj → setoid {ℓₐ₁} {ℓ~₁}}
                          {isecat1 : is-ecategory Obj Hom1}
                          {ℓₐ₂ ℓ~₂ : Level}{Hom2 : Obj → Obj → setoid {ℓₐ₂} {ℓ~₂}}
                          {isecat2 : is-ecategory Obj Hom2}
                          (F : idobj-efunctor isecat1 isecat2)
                          where
  open idobj-efunctor F public
  open idobj-efunctor-aux-only F public
-- end idobj-efunctor-aux


IdFᵢₒ : {ℓₒ : Level}{Obj : Set ℓₒ}{ℓₐ ℓ~ : Level}{Hom : Obj → Obj → setoid {ℓₐ} {ℓ~}}
       {isecat : is-ecategory Obj Hom}
          → idobj-efunctor isecat isecat
IdFᵢₒ {isecat = isecat} = record
  { ₐ = λ f → f
  ; isfctr = record
           { ext = λ pf → pf
           ; id = r
           ; cmp = λ f g → r
           }
  }
  where open ecategory-aux (mkecat isecat) using (r)


infixr 10 _○ᵢₒ_
_○ᵢₒ_ : {ℓₒ : Level}{Obj : Set ℓₒ}{ℓₐ₁ ℓ~₁ : Level}{Hom1 : Obj → Obj → setoid {ℓₐ₁} {ℓ~₁}}
        {isecat1 : is-ecategory Obj Hom1}{ℓₐ₂ ℓ~₂ : Level}{Hom2 : Obj → Obj → setoid {ℓₐ₂} {ℓ~₂}}
        {isecat2 : is-ecategory Obj Hom2}{ℓₐ₃ ℓ~₃ : Level}{Hom3 : Obj → Obj → setoid {ℓₐ₃} {ℓ~₃}}
        {isecat3 : is-ecategory Obj Hom3}
          → idobj-efunctor isecat2 isecat3 → idobj-efunctor isecat1 isecat2
            → idobj-efunctor isecat1 isecat3
_○ᵢₒ_ {isecat1 = isecat1} {isecat2 = isecat2} {isecat3 = isecat3} G F = record
  { ₐ = λ f → G.ₐ (F.ₐ f)
  ; isfctr = record
           { ext = λ pf → G.ext (F.ext pf)
           ; id = λ {A} → G.ext F.id 𝔼.⊙ G.id
           ; cmp = λ f g → G.cmp (F.ₐ f) (F.ₐ g) 𝔼.⊙ G.ext (F.cmp f g)
           }
  }
  where module 𝔼 = ecategory-aux (mkecat isecat3)
        module F = idobj-efunctor-aux F
        module G = idobj-efunctor-aux G



record is-idobj-iso-pair {ℓₒ : Level}{Obj : Set ℓₒ}{ℓₐ₁ ℓ~₁ : Level}
                         {Hom1 : Obj → Obj → setoid {ℓₐ₁} {ℓ~₁}}{isecat1 : is-ecategory Obj Hom1}
                         {ℓₐ₂ ℓ~₂ : Level}{Hom2 : Obj → Obj → setoid {ℓₐ₂} {ℓ~₂}}
                         {isecat2 : is-ecategory Obj Hom2}
                         (F : idobj-efunctor isecat1 isecat2)
                         (G : idobj-efunctor isecat2 isecat1)
                         : Set (ℓₒ ⊔ ℓₐ₁ ⊔ ℓ~₁ ⊔ ℓₐ₂ ⊔ ℓ~₂) where
  module dom = ecategory-aux (mkecat isecat1)
  module cod = ecategory-aux (mkecat isecat2)
  module F = idobj-efunctor-aux F
  module G = idobj-efunctor-aux G
  field
    iddom : {A B : Obj}(f : || Hom1 A B ||) → G.ₐ (F.ₐ f) dom.~ f
    idcod : {A B : Obj}(g : || Hom2 A B ||) → F.ₐ (G.ₐ g) cod.~ g

record is-idobj-isomorphism {ℓₒ : Level}{Obj : Set ℓₒ}{ℓₐ₁ ℓ~₁ : Level}
                            {Hom1 : Obj → Obj → setoid {ℓₐ₁} {ℓ~₁}}{isecat1 : is-ecategory Obj Hom1}
                            {ℓₐ₂ ℓ~₂ : Level}{Hom2 : Obj → Obj → setoid {ℓₐ₂} {ℓ~₂}}
                            {isecat2 : is-ecategory Obj Hom2}
                            (F : idobj-efunctor isecat1 isecat2)
                            : Set (ℓₒ ⊔ ℓₐ₁ ⊔ ℓ~₁ ⊔ ℓₐ₂ ⊔ ℓ~₂) where
  field
    inv : idobj-efunctor isecat2 isecat1
    isisopair : is-idobj-iso-pair F inv

infix 10 _≅ᶜᵃᵗ_
record _≅ᶜᵃᵗ_ {ℓₒ : Level}{Obj : Set ℓₒ}{ℓₐ₁ ℓ~₁ : Level}{Hom1 : Obj → Obj → setoid {ℓₐ₁} {ℓ~₁}}
             (isecat1 : is-ecategory Obj Hom1){ℓₐ₂ ℓ~₂ : Level}
             {Hom2 : Obj → Obj → setoid {ℓₐ₂} {ℓ~₂}}(isecat2 : is-ecategory Obj Hom2)
             : Set (ℓₒ ⊔ ℓₐ₁ ⊔ ℓ~₁ ⊔ ℓₐ₂ ⊔ ℓ~₂) where
  field
    a12 : idobj-efunctor isecat1 isecat2
    a21 : idobj-efunctor isecat2 isecat1
    isisopair : is-idobj-iso-pair a12 a21
  open is-idobj-iso-pair isisopair public


iso-cat→eqv-cat : {ℓₒ : Level}{Obj : Set ℓₒ}{ℓₐ₁ ℓ~₁ : Level}{Hom1 : Obj → Obj → setoid {ℓₐ₁} {ℓ~₁}}
                   {isecat1 : is-ecategory Obj Hom1}{ℓₐ₂ ℓ~₂ : Level}
                   {Hom2 : Obj → Obj → setoid {ℓₐ₂} {ℓ~₂}}{isecat2 : is-ecategory Obj Hom2}
                     → isecat1 ≅ᶜᵃᵗ isecat2 → (mkecat isecat1) ≡ᶜᵃᵗ (mkecat isecat2)
iso-cat→eqv-cat {isecat1 = isecat1} {isecat2 = isecat2} iso = record
  { a12 = idobj-efunctor-is-efunctor iso.a12
  ; a21 = idobj-efunctor-is-efunctor iso.a21
  ; iseqvpair = record
              { ι1 = record
                   { natt = record
                          { fnc = λ {A} → cod.idar A
                          ; nat = λ {A} {B} g → cod.~proof
                                  cod.idar B cod.∘ a12.ₐ (a21.ₐ g) ~[ cod.lidgen (iso.idcod g) ] cod./
                                  g                               ~[ cod.ridˢ ]∎
                                  g cod.∘ cod.idar A ∎
                          }
                   ; natt⁻¹ = record
                            { fnc = λ {A} → cod.idar A 
                            ; nat = λ {A} {B} g → cod.lid cod.⊙ cod.ridgenˢ (iso.idcod g cod.ˢ)
                            }
                   ; isiso = λ {A} → cod.idar-is-isopair A
                   }
              ; ι2 = record
                   { natt = record
                          { fnc = λ {A} → dom.idar A
                          ; nat = λ {A} {B} f → dom.~proof
                                  dom.idar B dom.∘ a21.ₐ (a12.ₐ f) ~[ dom.lidgen (iso.iddom f) ] dom./
                                  f                               ~[ dom.ridˢ ]∎
                                  f dom.∘ dom.idar A ∎
                          }
                   ; natt⁻¹ = record
                            { fnc = λ {A} → dom.idar A 
                            ; nat = λ {A} {B} f → dom.lid dom.⊙ dom.ridgenˢ (iso.iddom f dom.ˢ)
                            }
                   ; isiso = λ {A} → dom.idar-is-isopair A
                   }
              }
  }
  where module dom where
          open ecategory-aux (mkecat isecat1) public
          open iso-defs (mkecat isecat1) public
          open iso-props (mkecat isecat1) public
        module cod where
          open ecategory-aux (mkecat isecat2) public
          open iso-defs (mkecat isecat2) public
          open iso-props (mkecat isecat2) public
          module id (A : Obj) = is-iso-pair (idar-is-isopair A)
        module iso = _≅ᶜᵃᵗ_ iso
        module a12 = idobj-efunctor iso.a12
        module a21 = idobj-efunctor iso.a21
        
             
