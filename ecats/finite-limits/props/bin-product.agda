
{-# OPTIONS --without-K #-}

module ecats.finite-limits.props.bin-product where

open import ecats.basic-defs.ecat-def&not
open import ecats.basic-defs.commut-shapes
open import ecats.basic-defs.isomorphism
open import ecats.basic-defs.epi&mono
open import ecats.finite-limits.d&n-bin-product




module bin-product-props (ℂ : ecategory) where
  open ecategory-aux ℂ
  open iso-defs ℂ
  open epis&monos-defs ℂ
  open comm-shapes ℂ
  open binary-products ℂ 



  module product-is-unique-uptoiso {A B : Obj} (×1 ×2 : product-of A B) where
    private
      module ×1 = product-of-not ×1
      module ×2 = product-of-not ×2

    ×uq-ar : || Hom ×1.O12 ×2.O12 ||
    ×uq-ar = ×2.< ×1.π₁ , ×1.π₂ >

    ×uq-ar⁻¹ : || Hom ×2.O12 ×1.O12 ||
    ×uq-ar⁻¹ = ×1.< ×2.π₁ , ×2.π₂ >

    ×uq-iso-pair : is-iso-pair ×uq-ar ×uq-ar⁻¹
    ×uq-iso-pair = record
                 { iddom = ×1.<>ar~ar (ridgen ×2.×tr₁ˢ) (ridgen ×2.×tr₂ˢ)
                 ; idcod = ×2.<>ar~ar (ridgen ×1.×tr₁ˢ) (ridgen ×1.×tr₂ˢ)
                 }
    ×uq-ar-iso : is-iso ×uq-ar
    ×uq-ar-iso = mkis-iso ×uq-iso-pair
    ×uq-ar⁻¹-iso : is-iso ×uq-ar⁻¹
    ×uq-ar⁻¹-iso = mkis-iso (inv-iso-pair ×uq-iso-pair)

    ×-iso : ×1.O12 ≅ₒ ×2.O12
    ×-iso = mk≅ ×uq-iso-pair

    ×-iso-gen : {f : || Hom ×1.O12 ×2.O12 ||} → ×2.π₁ ∘ f ~ ×1.π₁ → ×2.π₂ ∘ f ~ ×1.π₂
                   → is-iso f
    ×-iso-gen pf₁ pf₂ = iso-ext ×uq-ar-iso (×2.ar~<> pf₁ pf₂)
  -- end product-is-unique-uptoiso
-- end bin-product-props
