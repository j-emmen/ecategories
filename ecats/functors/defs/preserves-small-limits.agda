
{-# OPTIONS --without-K #-}

module ecats.functors.defs.preserves-small-limits where

open import Agda.Primitive
open import ecats.basic-defs.ecat-def&not
open import ecats.basic-defs.isomorphism
open import ecats.basic-props.isomorphism
open import ecats.small-limits.defs.small-limit
open import ecats.small-limits.props.small-limit
open import ecats.functors.defs.efunctor-d&n
open import ecats.functors.defs.natural-transformation
open import ecats.functors.defs.natural-iso
open import ecats.functors.defs.basic-defs
open import ecats.constructions.discrete-ecat

private
  module pres-lim-aux {ℓₒ ℓₐ ℓ~ : Level}(𝕏 : ecategoryₗₑᵥ ℓₒ ℓₐ ℓ~) where
    open ecat 𝕏 public
    open small-limit-defs 𝕏 public

record preserves-limits {ℓₒ₁ ℓₐ₁ ℓ~₁ : Level}{ℂ : ecategoryₗₑᵥ ℓₒ₁ ℓₐ₁ ℓ~₁}
                        {ℓₒ₂ ℓₐ₂ ℓ~₂ : Level}{𝔻 : ecategoryₗₑᵥ ℓₒ₂ ℓₐ₂ ℓ~₂}
                        (F : efunctorₗₑᵥ ℂ 𝔻)
                        : Set (1ₗₑᵥ ⊔ ecat.ℓₐₗₗ ℂ ⊔ ecat.ℓₐₗₗ 𝔻) where
  private
    module ℂ = pres-lim-aux ℂ
    module 𝔻 = pres-lim-aux 𝔻
    module F = efctr F
  field
    pres-lim : {𝕀 : small-ecategory}{D : 𝕀 diag-in ℂ}{C : Cone/.Obj D}
                  → ℂ.is-limit-cone C → 𝔻.is-limit-cone (Fcone F D C)
  pres-limof : {𝕀 : small-ecategory}{D : 𝕀 diag-in ℂ}
                  → ℂ.limit-of D → 𝔻.limit-of (F ○ D)
  pres-limof {D = D} L = record
    { cone = Fcone F D L.cone
    ; islim = pres-lim L.islim
    }
    where module L = ℂ.limit-of L



record preserves-products {ℓₒ₁ ℓₐ₁ ℓ~₁ : Level}{ℂ : ecategoryₗₑᵥ ℓₒ₁ ℓₐ₁ ℓ~₁}
                          {ℓₒ₂ ℓₐ₂ ℓ~₂ : Level}{𝔻 : ecategoryₗₑᵥ ℓₒ₂ ℓₐ₂ ℓ~₂}
                          (F : efunctorₗₑᵥ ℂ 𝔻)
                          : Set (1ₗₑᵥ ⊔ ecat.ℓₐₗₗ ℂ ⊔ ecat.ℓₐₗₗ 𝔻) where
  private
    module ℂ = pres-lim-aux ℂ
    module 𝔻 = pres-lim-aux 𝔻
    module F = efctr F
  field
    pres-prd : {I : Set}{D : I → ℂ.Obj}{S : Span/.Obj ℂ D}
                  → ℂ.is-product S → 𝔻.is-product (Fspan F D S)
  pres-prdof : {I : Set}{D : I → ℂ.Obj}
                  → ℂ.product-of D → 𝔻.product-of (λ i → F.ₒ (D i))
  pres-prdof {D = D} L = record
    { span/ = Fspan F D L.span/
    ; isprd = pres-prd L.isprd
    }
    where module L = ℂ.product-of L



pres-lim→pres-prd : {ℓₒ₁ ℓₐ₁ ℓ~₁ : Level}{ℂ : ecategoryₗₑᵥ ℓₒ₁ ℓₐ₁ ℓ~₁}
                     {ℓₒ₂ ℓₐ₂ ℓ~₂ : Level}{𝔻 : ecategoryₗₑᵥ ℓₒ₂ ℓₐ₂ ℓ~₂}{F : efunctorₗₑᵥ ℂ 𝔻}
                       → preserves-limits F → preserves-products F
pres-lim→pres-prd {ℂ = ℂ} {𝔻 = 𝔻} {F = F} limF = record
  { pres-prd = λ {I} {D} {S} Sprd →
             𝔻.is-lim→is-prod (λ i → F.ₒ (D i))
                                {span→cone 𝔻 (Fspan F D S)}
                                (𝔻.trsp-lim-conv (disc-ecat-tr D F)
                                                  (𝔻.isolim-is-lim (iso D S)
                                                                    (F.pres-lim (ℂ.is-prod→is-lim D Sprd))))
  }
  where module ℂ where
          open pres-lim-aux ℂ public
          open small-limit-props ℂ public
          open small-prod-is-small-limit public
        module 𝔻 where
          open pres-lim-aux 𝔻 public
          open iso-defs 𝔻 public
          open iso-props 𝔻 public
          open small-limit-props 𝔻 public
          open small-prod-is-small-limit public
          open limit-invariant-under-natiso public
          --module cone {𝕀 : small-ecategory}{D D' : 𝕀 diag-in ℂ}(D≅D' : D ≅ₐ D')
            --          = _≡ᶜᵃᵗ_ (cone-iso-trsp D≅D')
        module F where
          open efunctor-aux F public
          open preserves-limits limF public
        module F○↑D≅↑FD  {I : Set}(D : I → ℂ.Obj) where
          open natural-iso (disc-ecat-tr D F) public
          open _≡ᶜᵃᵗ_ (cone-iso-trsp (disc-ecat-tr D F)) public
          module a12 = efctr a12
          module a21 = efctr a21
        -- proof that the image of the cone induced by a span is isomorphic
        -- to the cone induced by the image of the span
        -- TO BE MOVED
        iso : {I : Set}(D : I → ℂ.Obj)(S : Span/.Obj ℂ D)
                 → iso-defs._≅ₒ_ (Cone/ (F ○ ℂ.↑Dg D)) (Fcone F (ℂ.↑Dg D) (span→cone ℂ S))
                                                        (F○↑D≅↑FD.a21.ₒ D (span→cone 𝔻 (Fspan F D S)))
        iso {I} D S = record
          { a12 = record
                { arL = 𝔻.idar (F.ₒ S.Vx)
                ; tr = λ i → ~proof
                Cn/F↑D.ₒ.leg (F○↑D≅↑FD.a21.ₒ D (span→cone 𝔻 (Fspan F D S))) i 𝔻.∘ 𝔻.idar (F.ₒ S.Vx)
                                                                                        ~[ rid ] /
                𝔻.idar (F.ₒ (D i))  𝔻.∘ Cn/↑FD.ₒ.leg (span→cone 𝔻 (Fspan F D S)) i
                                                                                        ~[ lid ]∎
                Cn/F↑D.ₒ.leg (Fcone F (ℂ.↑Dg D) (span→cone ℂ S)) i ∎
                }
          ; a21 = record
                { arL = 𝔻.idar (F.ₒ S.Vx)
                ; tr = λ i → ~proof
                Cn/F↑D.ₒ.leg ((Fcone F (ℂ.↑Dg D) (span→cone ℂ S))) i 𝔻.∘ 𝔻.idar (F.ₒ S.Vx)
                                                                                        ~[ rid ] /
                Cn/↑FD.ₒ.leg (span→cone 𝔻 (Fspan F D S)) i
                                                                                        ~[ lidˢ ]∎
                Cn/F↑D.ₒ.leg (F○↑D≅↑FD.a21.ₒ D (span→cone 𝔻 (Fspan F D S))) i ∎
                }
          ; isop = record
                 { iddom = rid
                 ; idcod = rid
                 }
          }
          where module Cn/D = Cone/ (ℂ.↑Dg D)
                module Cn/F↑D = Cone/ (F ○ ℂ.↑Dg D)
                module Cn/↑FD = Cone/ (𝔻.↑Dg (λ i → F.ₒ (D i)))
                module S = Span/.ₒ ℂ D S
                open ecategory-aux-only 𝔻

