
{-# OPTIONS --without-K #-}

module ecats.small-limits.defs.small-limit where

open import ecats.basic-defs.ecat-def&not
open import ecats.functors.defs.cone public
open import ecats.functors.defs.efunctor-d&n
open import ecats.functors.defs.natural-transformation
open import ecats.constructions.functor-ecat
open import ecats.finite-limits.defs.terminal public


module small-limit-defs {ℓ₁ ℓ₂ ℓ₃ : Level}(ℂ : ecategoryₗₑᵥ ℓ₁ ℓ₂ ℓ₃) where
  private
    module ℂ = ecat ℂ

  -- small limits
  is-universal-cone-over is-limit-cone : {𝕀 : small-ecategory}{D : 𝕀 diag-in ℂ}(cone : Cone/.Obj D)
                              → Set ℂ.ℓₐₗₗ -- = (Cone/.ℓₐₗₗ D)
  is-universal-cone-over {𝕀} {D} cone = is-terminal cone
                                      where open terminal-defs (Cone/ D)
  is-limit-cone = is-universal-cone-over
  
  module is-limit-cone {𝕀 : small-ecategory}{D : 𝕀 diag-in ℂ}{L : Cone/.Obj D}
                       (islim : is-limit-cone L)
                       where
    private
      module D = efctr D
      module Cone/D where
        open Cone/ D public
        open terminal-defs (Cone/ D) public
      module L where
        open Cone/D.ₒ L renaming (leg to π) public
        open Cone/D.is-terminal {L} islim public
    open L using () renaming (! to unv) public
    module unv (cn : Cone/.Obj D) where
      private module cn = Cone/D.ₒ cn
      open Cone/D.ₐ (L.! cn) public
      uq-cn : (f : || Cone/D.Hom cn L ||) → f Cone/D.~ unv cn
      uq-cn = L.!uniq {cn}
      uq : {f : || ℂ.Hom cn.Vx L.Vx ||}(trf : ∀ i → L.π i ℂ.∘ f ℂ.~ cn.leg i)
              → f ℂ.~ ar
      uq {f} tr = L.!uniq {cn} (Cone/.if-tr-then-ar D cn L tr)
    π-jm :  {A : ℂ.Obj}{f g : || ℂ.Hom A L.Vx ||}
            (eq : ∀ i → L.π i ℂ.∘ f ℂ.~ L.π i ℂ.∘ g)
              → f ℂ.~ g
    π-jm {f = f} {g} eq = L.!uqg {f = Cone/D.ar-is-mor L f}
                                 {g = Cone/D.if-tr-then-ar (Cone/D.ar-is-mor-dom L f) L {g}
                                                           (λ I → eq I ˢ)}
                        where open ecategory-aux-only ℂ using (_ˢ)

  record limit-of {𝕀 : small-ecategory}(D : 𝕀 diag-in ℂ) : Set ℂ.ℓₐₗₗ where
    private module Cn = Cone/.ₒ D
    field
      cone : Cone/.Obj D
      islim : is-limit-cone cone
    open Cone/.ₒ D cone renaming (leg to π; sides to π-natt) public
    open is-limit-cone {𝕀} {D} {cone} islim public


  -- small products
  is-product : {I : Set}{D : I → ecat.Obj ℂ}(span : Span/.Obj ℂ D)
                  → Set ℂ.ℓₐₗₗ -- = MSpan/.ℓₐₗₗ ℂ D
  is-product {_} {D} = is-terminal
                     where open terminal-defs (Span/ ℂ D)

  module is-product {I : Set}{D : I → ecat.Obj ℂ}{P : Span/.Obj ℂ D}
                    (isprd : is-product P)
                    where
    private
      module Sp/D = Span/ ℂ D
      module P = Sp/D.ₒ P renaming (leg to π)
    open terminal-defs.is-terminal {ℂ = Span/ ℂ D} {P} isprd
    module unv (sp : Sp/D.Obj) where
      private module sp = Sp/D.ₒ sp
      open Sp/D.ₐ (! sp) public
      uq : {f : || ℂ.Hom sp.Vx P.Vx ||}(trf : ∀ i → P.π i ℂ.∘ f ℂ.~ sp.leg i)
              → f ℂ.~ ar
      uq {f} tr = !uniq {sp} (Sp/D.if-tr-then-ar sp P tr)
    π-jm :  (sp : Sp/D.Obj){f g : || ℂ.Hom (Sp/D.ₒ.Vx sp) P.Vx ||}
            (trf : ∀ i → P.π i ℂ.∘ f ℂ.~ Sp/D.ₒ.leg sp i)
            (trg : ∀ i → P.π i ℂ.∘ g ℂ.~ Sp/D.ₒ.leg sp i)
              → f ℂ.~ g
    π-jm sp trf trg = !uqg {f = Sp/D.if-tr-then-ar sp P trf}
                           {g = Sp/D.if-tr-then-ar sp P trg}

  
  record product-of {I : Set}(D : I → ecat.Obj ℂ) : Set ℂ.ℓₐₗₗ where
    private module Sp/D = Span/ ℂ D
    field
      span/ : Sp/D.Obj
      isprd : is-product span/
    open Sp/D.ₒ span/ renaming (leg to π) public
    open is-product isprd public

-- end small-limit-defs


record has-small-limits {ℓ₁ ℓ₂ ℓ₃ : Level}(ℂ : ecategoryₗₑᵥ ℓ₁ ℓ₂ ℓ₃) : Set (1ₗₑᵥ ⊔ ecat.ℓₐₗₗ ℂ) where
  open small-limit-defs ℂ
  field
    lim-of : {𝕀 : small-ecategory}(D : 𝕀 diag-in ℂ) → limit-of D
  module lim-of {𝕀 : small-ecategory}(D : 𝕀 diag-in ℂ) = limit-of (lim-of D)
  open lim-of public

has-small-limits-lc : ecategory → Set₁
has-small-limits-lc = has-small-limits

record has-small-products {ℓ₁ ℓ₂ ℓ₃ : Level}(ℂ : ecategoryₗₑᵥ ℓ₁ ℓ₂ ℓ₃) : Set (1ₗₑᵥ ⊔ ecat.ℓₐₗₗ ℂ) where
  open small-limit-defs ℂ
  field
    prd-of : {I : Set}(D : I → ecat.Obj ℂ) → product-of D
  module prd-of {I : Set}(D : I → ecat.Obj ℂ) = product-of (prd-of D)
  open prd-of public

