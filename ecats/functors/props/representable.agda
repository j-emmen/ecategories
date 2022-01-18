
{-# OPTIONS --without-K #-}

module ecats.functors.props.representable where

open import ecats.basic-defs.ecat-def&not
open import ecats.basic-defs.initial
open import ecats.finite-limits.defs.terminal
open import ecats.small-limits.defs.small-limit
open import ecats.functors.defs.efunctor-d&n
open import ecats.functors.defs.basic-defs
open import ecats.functors.defs.natural-transformation
open import ecats.functors.defs.natural-iso
open import ecats.functors.defs.presheaf
open import ecats.functors.defs.representable
open import ecats.functors.defs.preserves-small-limits
open import ecats.constructions.ecat-elements
open import ecats.constructions.yoneda
open import ecats.concr-ecats.Std-lev



module repres-at-props {ℓ₁ ℓ₂ ℓ₃ : Level}(ℂ : ecategoryₗₑᵥ ℓ₁ ℓ₂ ℓ₃)(X : ecat.Obj ℂ) where
  private
    module ℂ where
      open ecategory-aux ℂ public
      --open small-limit-defs ℂ public
    module Std where
      open ecategory-aux (Stdₗₑᵥ ℂ.ℓₐᵣᵣ ℂ.ℓ~) public
      --open small-limit-defs (Stdₗₑᵥ ℂ.ℓₐᵣᵣ ℂ.ℓ~) public
    [X,─] : copresheafₗₑᵥ ℂ
    [X,─] = ℂ [ₒ X ,─]
    [─,X] : presheafₗₑᵥ ℂ
    [─,X] = ℂ [─, X ₒ]
    module [X,─] where
      open copresheafₗₑᵥ [X,─] public
      --open copresheafₗₑᵥ [X,─] public
      cone : {𝕀 : small-ecategory}(D : 𝕀 diag-in ℂ)
                → Cone/.Obj D → Cone/.Obj ([X,─] ○ D)
      cone = Fcone [X,─]
    module [─,X] where
      open presheafₗₑᵥ [─,X] public
      --open copresheafₗₑᵥ [X,─] public
      cone : {𝕀 : small-ecategory}(D : 𝕀 diag-in ℂ)
                → Cone/.Obj D → Cone/.Obj ([X,─] ○ D)
      cone = Fcone [X,─]
    elmts/X coelmts/X : ecategoryₗₑᵥ ℂ.ℓₙₒ~ ℂ.ℓₕₒₘ ℂ.ℓ~
    elmts/X = ecat-elmts [─,X]
    coelmts/X = ecat-coelmts [X,─]
    module elmts/X where
      open ecat-elmts [─,X] public
      open ecategory-aux elmts/X public
      open terminal-defs elmts/X public
    module coelmts/X where
      open ecat-coelmts [X,─] public
      open ecategory-aux coelmts/X public
      open initial-defs coelmts/X public

  term-ob : elmts/X.Obj
  term-ob = record
    { Ob = X
    ; el = ℂ.idar X
    }

  term-ar : (A : elmts/X.Obj) → || elmts/X.Hom A term-ob ||
  term-ar A = record
    { ar = A.el
    ; eq = ℂ.lid
    }
    where module A = elmts/X.ₒ A

  term-uq : {A : elmts/X.Obj} (f : || elmts/X.Hom A term-ob ||)
              → f elmts/X.~ term-ar A
  term-uq {A} f = ℂ.lidˢ ℂ.⊙ f.eq
                where module A = elmts/X.ₒ A
                      module f = elmts/X.ₐ f

  term-el : has-terminal elmts/X
  term-el = record
    { trmOb = term-ob
    ; istrm = record
            { ! = term-ar
            ; !uniq = term-uq
            }
    }

-- end repres-at-props


module representable-psheaf-props {ℓ₁ ℓ₂ ℓ₃ : Level}{ℂ : ecategoryₗₑᵥ ℓ₁ ℓ₂ ℓ₃}
                                  (F : presheafₗₑᵥ ℂ) where
  private
    module ℂ where
      open ecategory-aux ℂ public
      --open small-limit-defs ℂ public
    module Std where
      open ecategory-aux (Stdₗₑᵥ ℂ.ℓₐᵣᵣ ℂ.ℓ~) public
      --open small-limit-defs (Stdₗₑᵥ ℂ.ℓₐᵣᵣ ℂ.ℓ~) public
    module F = presheafₗₑᵥ F

    -- F is representable iff its category of elements ∫F has terminal object.
    
    ∫F : ecategoryₗₑᵥ ℂ.ℓₙₒ~ ℂ.ℓₕₒₘ ℂ.ℓ~
    ∫F = ecat-elmts F
    module ∫F where
      open ecat-elmts F public
      open ecategory-aux ∫F public
      open terminal-defs ∫F public

    module repr-to-term (isrepr : is-represble-psheaf F) where
      open is-represble-psheaf isrepr
      module ρ = natiso
      open yoneda-props.Lemma ℂ F Rob

      ob : ∫F.Obj
      ob = record
         { Ob = Rob
         ; el = natt2el.ap ρ.natt⁻¹
         }
      module ob = ∫F.ₒ ob

      ar : (A : ∫F.Obj) → || ∫F.Hom A ob ||
      ar A = record
           { ar = uar
           ; eq = ~proof F.ₐ.ap uar (ob.el)                     ~[ ρ.nat⁻¹ uar (ℂ.idar Rob) ˢ ] /
                         ρ.fnc⁻¹.ap A.Ob (ℂ.idar Rob ℂ.∘ uar)   ~[ ρ.fnc⁻¹.ext A.Ob ℂ.lid ] /
                         ρ.fnc⁻¹.ap A.Ob uar                    ~[ ρ.iddom {A.Ob} A.el ]∎
                         A.el ∎
           }
           where module A = ∫F.ₒ A
                 open StdObj (F.ₒ A.Ob)
                 uar : || ℂ.Hom A.Ob Rob ||
                 uar = ρ.fnc.ap A.Ob A.el
      module ar (A : ∫F.Obj) = ∫F.ₐ (ar A)

      uq : {A : ∫F.Obj} (f : || ∫F.Hom A ob ||) → f ∫F.~ ar A
      uq {A} f = ~proof f.ar                              ~[ lidggˢ r (ρ.idcod (ℂ.idar Rob)) ] /
                        ρ.fnc.ap Rob ob.el ℂ.∘ f.ar      ~[ ρ.nat f.ar ob.el ˢ ] /
                        ρ.fnc.ap A.Ob (F.ₐ.ap f.ar ob.el) ~[ ρ.fnc.ext A.Ob f.eq ]∎
                        ar.ar A ∎
               where module A = ∫F.ₒ A
                     module f = ∫F.ₐ f
                     open ecategory-aux-only ℂ

      isterm : ∫F.is-terminal ob
      isterm = record
             { ! = ar
             ; !uniq = uq
             }
      
    -- end repr-to-term
  -- end private
  
  repres→term : is-represble-psheaf F → has-terminal ∫F
  repres→term isrepr = record
    { trmOb = ob
    ; istrm = isterm
    }
    where open repr-to-term isrepr


-- end representable-psheaf-props


module representable-copsheaf-props {ℓ₁ ℓ₂ ℓ₃ : Level}{ℂ : ecategoryₗₑᵥ ℓ₁ ℓ₂ ℓ₃}
                                    (F : copresheafₗₑᵥ ℂ) where
  private
    module ℂ where
      open ecategory-aux ℂ public
      --open small-limit-defs ℂ public
    module Std where
      open ecategory-aux (Stdₗₑᵥ ℂ.ℓₐᵣᵣ ℂ.ℓ~) public
      --open small-limit-defs (Stdₗₑᵥ ℂ.ℓₐᵣᵣ ℂ.ℓ~) public
    module F = copresheafₗₑᵥ F

    -- F is representable iff its category of coelements ∫F has initial object.
    
    ∫F : ecategoryₗₑᵥ ℂ.ℓₙₒ~ ℂ.ℓₕₒₘ ℂ.ℓ~
    ∫F = ecat-coelmts F
    module ∫F where
      open ecat-coelmts F public
      open ecategory-aux ∫F public
      open initial-defs ∫F public

    module repr-to-init (isrepr : is-represble-copsheaf F) where
      open is-represble-copsheaf isrepr
      module ρ = natiso

      ob : ∫F.Obj
      ob = record
         { Ob = Rob
         ; el = ρ.fnc⁻¹.ap Rob (ℂ.idar Rob)
         }
      module ob = ∫F.ₒ ob

      ar : (A : ∫F.Obj) → || ∫F.Hom ob A ||
      ar A = record
           { ar = uar
           ; eq = ~proof F.ₐ.ap uar (ob.el)                     ~[ ρ.nat⁻¹ uar (ℂ.idar Rob) ˢ ] /
                         ρ.fnc⁻¹.ap A.Ob (uar ℂ.∘ ℂ.idar Rob)  ~[ ρ.fnc⁻¹.ext A.Ob ℂ.rid ] /
                         ρ.fnc⁻¹.ap A.Ob uar                    ~[ ρ.iddom {A.Ob} A.el ]∎
                         A.el ∎
           }
           where module A = ∫F.ₒ A
                 open StdObj (F.ₒ A.Ob)
                 uar : || ℂ.Hom Rob A.Ob ||
                 uar = ρ.fnc.ap A.Ob A.el
      module ar (A : ∫F.Obj) = ∫F.ₐ (ar A)

      uq : {A : ∫F.Obj} (f : || ∫F.Hom ob A ||) → f ∫F.~ ar A
      uq {A} f = ~proof f.ar                              ~[ ridggˢ r (ρ.idcod (ℂ.idar Rob)) ] /
                        f.ar ℂ.∘ (ρ.fnc.ap Rob ob.el)     ~[ ρ.nat f.ar ob.el ˢ ] /
                        ρ.fnc.ap A.Ob (F.ₐ.ap f.ar ob.el) ~[ ρ.fnc.ext A.Ob f.eq ]∎
                        ar.ar A ∎
               where module A = ∫F.ₒ A
                     module f = ∫F.ₐ f
                     open ecategory-aux-only ℂ

      isinit : ∫F.is-initial ob
      isinit = record
             { ø = ar
             ; øuq = uq
             }
      
    -- end repr-to-init
  -- end private

  repres→init : is-represble-copsheaf F → has-initial ∫F
  repres→init isrepr = record
    { initOb = ob
    ; isinit = isinit
    }
    where open repr-to-init isrepr


  private
    module init-to-repr (hasinit : has-initial ∫F) where
      open has-initial hasinit renaming (initOb to I)
      module I = ∫F.ₒ I
      module ø {A : ℂ.Obj}(x : || F.ₒ A ||) = ∫F.ₐ (ø (record {Ob = A; el = x}))

      ob : ℂ.Obj
      ob = I.Ob

      ar2el : natural-transformation (ℂ [ₒ ob ,─]) F
      ar2el = record
         { fnc = fnc
         ; nat = nat
         }
         where fnc : {A : ℂ.Obj} → || Std.Hom (ℂ.Hom ob A) (F.ₒ A) ||
               fnc {A} = record
                 { op = λ f → F.ₐ.ap f I.el 
                 ; ext = λ eq → F.ext eq I.el
                 }
               nat : {A B : ℂ.Obj} (f : || ℂ.Hom A B ||)(a : || ℂ.Hom ob A ||)
                        → F.ₐ.ap (f ℂ.∘ a) I.el F.ₒ~ F.ₐ.ap f (F.ₐ.ap a I.el)
               nat {A} {B} f a = F.cmpˢ a f I.el

      el2ar : natural-transformation F (ℂ [ₒ ob ,─])
      el2ar = record
        { fnc = fnc
        ; nat = nat
        }
        where øtrsp : {A : ℂ.Obj}{x x' : || F.ₒ A ||}(eq : x F.ₒ~ x')
                        → || ∫F.Hom I (∫F.el/ x') ||
              øtrsp {A} {x} {x'} eq = ∫F.~iso.a12 eq ∫F.∘ ø (∫F.el/ x)
              fnc : {A : ℂ.Obj} → || Std.Hom (F.ₒ A) (ℂ.Hom ob A) ||
              fnc {A} = record
                { op = ø.ar
                ; ext = λ {x} {x'} eq → ℂ.lidˢ ℂ.⊙ øuqg {∫F.el/ x'} {øtrsp eq} {ø (∫F.el/ x')}
                }
              nat-ar : {A B : ℂ.Obj} (f : || ℂ.Hom A B ||)(x : || F.ₒ A ||)
                          → || ∫F.Hom I (∫F.el/ (F.ₐ.ap f x)) ||
              nat-ar {A} {B} f x = record
                { ar = f ℂ.∘ ø.ar x
                ; eq = F.cmpˢ (ø.ar x) f I.el FB.⊙ F.ₐ.ext f (ø.eq x)
                }
                where module FA = F.ₒ A
                      module FB = F.ₒ B
              nat : {A B : ℂ.Obj} (f : || ℂ.Hom A B ||)(x : || F.ₒ A ||)
                       → ø.ar (F.ₐ.ap f x) ℂ.~ f ℂ.∘ ø.ar x
              nat f x = øuq (nat-ar f x) ℂ.ˢ

      id-el : {A : ℂ.Obj}(x : || F.ₒ A ||) → F.ₐ.ap (ø.ar x) I.el F.ₒ~ x
      id-el x = ø.eq x

      id-ar : {A : ℂ.Obj}(a : || ℂ.Hom ob A ||) → ø.ar (F.ₐ.ap a I.el) ℂ.~ a
      id-ar {A} a = øuq (∫F.ar/ a FA.r) ℂ.ˢ
                  where module FA = F.ₒ A

{-
      ni : F ≅ₐ ℂ [ ob ,─]
      ni = record
         { natt = el2ar
         ; natt⁻¹ = ar2el
         ; isiso = λ {A} → record
                 { iddom = ø.eq {A}
                 ; idcod = λ a → øuq (∫F.ar/ a (F.ₒ.r A)) ℂ.ˢ
                 }
         }
-}
    -- end init-to-repr
  -- end private

  init→repres : has-initial ∫F → is-represble-copsheaf F
  init→repres hasinit = record
    { Rob = ob
    ; natiso = record
             { natt = el2ar
             ; natt⁻¹ = ar2el
             ; isiso = λ {A} → record
                     { iddom = id-el {A}
                     ; idcod = id-ar {A}
                     }
             }
    }
    where open init-to-repr hasinit
    
-- end representable-copsheaf-props



-- this proves preservation of limits for copresheaves on loc small cats
module repres-at-props-ls (ℂ : ecategory)(X : ecat.Obj ℂ) where
  private
    module ℂ where
      open ecategory-aux ℂ public
      open small-limit-defs ℂ public
    module Std where
      open ecategory-aux Std public
      open small-limit-defs Std public
    [X,─] : efunctor ℂ Std
    [X,─] = ℂ [ₒ X ,─]
    module [X,─] where
      open efunctor-aux [X,─] public
      --open copresheafₗₑᵥ [X,─] public
      cone : {𝕀 : small-ecategory}(D : 𝕀 diag-in ℂ)
                → Cone/.Obj D → Cone/.Obj ([X,─] ○ D)
      cone = Fcone [X,─]


  module pres-lim {𝕀 : small-ecategory}(D : 𝕀 diag-in ℂ)
                  {L : Cone/.Obj D}(limL : ℂ.is-limit-cone L)
                  where
    private
      module 𝕀 = ecategory-aux 𝕀
      module D = diagram D
      module Cn/D where
        open Cone/ D public
        open terminal-defs (Cone/ D) public
      module Cn/[X,D] where
        open Cone/ ([X,─] ○ D) public
        module ₒₛ (A : Obj) where
          open ₒ A public
          module Vx = StdObj (ₒ.Vx A)
          module leg (I : 𝕀.Obj) = StdHom (ₒ.leg A I)
        module ₐₛ {A B : Obj}(f : || Hom A B ||) where
          open ₐ f public
          open StdHom ar public
        open terminal-defs (Cone/ ([X,─] ○ D)) public
      module L where
        open Cn/D.ₒ L public
        open ℂ.is-limit-cone limL public
      [X,L] : Cn/[X,D].Obj
      [X,L] = [X,─].cone D L
      module [X,L] = Cn/[X,D].ₒₛ [X,L]

      fam-cones : (A : Cn/[X,D].Obj) → Cn/[X,D].ₒₛ.Vx.ob A → Cone/.Obj D
      fam-cones A a = Cn/D.if-tr-then-ob {X} {f = λ I → A.leg.ap I a}
                                         (λ {I} {J} IJ → A.tr IJ a)
                    where module A = Cn/[X,D].ₒₛ A
      unv-ar : (A : Cn/[X,D].Obj) → || Std.Hom (Cn/[X,D].ₒ.Vx A) [X,L].Vx ||
      unv-ar A = record
        { op = λ a → L.unv.ar (fam-cones A a)
        ; ext = λ {a} {a'} eq → L.unv.uq (fam-cones A a')
                                         (λ I → ~proof
                                L.leg I ℂ.∘ L.unv.ar (fam-cones A a)  ~[ L.unv.tr (fam-cones A a) I ] /
                                A.leg.ap I a                          ~[ A.leg.ext I eq ]∎
                                A.leg.ap I a' ∎)
       }
        where open ecategory-aux-only ℂ
              module A = Cn/[X,D].ₒₛ A
      unv-tr : (A : Cn/[X,D].Obj)(I : 𝕀.Obj)
                  → [X,L].leg I Std.∘ unv-ar A Std.~ Cn/[X,D].ₒ.leg A I
      unv-tr A I a = L.unv.tr (fam-cones A a) I

      unv-mor : (A : Cn/[X,D].Obj) → || Cn/[X,D].Hom A [X,L] ||
      unv-mor A = record
        { arL = unv-ar A
        ; tr = unv-tr A
        }
      unv-uq : {A : Cn/[X,D].Obj}(f : || Cn/[X,D].Hom A [X,L] ||)
                  → f Cn/[X,D].~ unv-mor A
      unv-uq {A} f a = L.unv.uq (fam-cones A a) {f.ap a} (λ I → f.tr I a)
                     where open ecategory-aux-only ℂ
                           module A = Cn/[X,D].ₒₛ A
                           module f = Cn/[X,D].ₐₛ f
    -- end private

    islim : Std.is-limit-cone ([X,─].cone D L)
    islim = record
      { ! = unv-mor
      ; !uniq = unv-uq
      }
  -- end pres-lim
  
  pres-lim : preserves-limits [X,─]
  pres-lim = record
    { pres-lim = λ {𝕀} {D} → islim D
    }
    where open pres-lim

-- end repres-at-props
