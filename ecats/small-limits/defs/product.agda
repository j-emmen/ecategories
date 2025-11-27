{-# OPTIONS --without-K #-}

module ecats.small-limits.defs.product where

open import tt-basics.basics
open import ecats.basic-defs.ecat-def&not
open import ecats.functors.defs.cone
open import ecats.finite-limits.defs.terminal

module product-defs {ℓₒ ℓₕ ℓ~ : Level}(ℂ : ecategoryₗₑᵥ ℓₒ ℓₕ ℓ~) where
  private
    module ℂ = ecat ℂ

  is-product : {I : Set}{D : I → ecat.Obj ℂ}(span : Span/.Obj ℂ D)
                  → Set ℂ.ℓₐₗₗ
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


  -- binary products
  bin-diag : (A B : ℂ.Obj) → N₁ + N₁ → ℂ.Obj
  bin-diag A B (inl x) = A
  bin-diag A B (inr x) = B
  
  is-bin-product : {A B : ℂ.Obj} → Span/.Obj ℂ (bin-diag A B) → Set ℂ.ℓₐₗₗ
  is-bin-product sp = is-product sp
  module is-bin-product = is-product

  bin-product-of : (A B : ℂ.Obj) → Set ℂ.ℓₐₗₗ
  bin-product-of A B = product-of (bin-diag A B)
  module bin-product-of {A B : ℂ.Obj} (bp : bin-product-of A B) = product-of bp

-- end product-defs


record has-small-products {ℓ₁ ℓ₂ ℓ₃ : Level}(ℂ : ecategoryₗₑᵥ ℓ₁ ℓ₂ ℓ₃) : Set (1ₗₑᵥ ⊔ ecat.ℓₐₗₗ ℂ) where
  open product-defs ℂ
  field
    prd-of : {I : Set}(D : I → ecat.Obj ℂ) → product-of D
  module prd-of {I : Set}(D : I → ecat.Obj ℂ) = product-of (prd-of D)
  open prd-of public
