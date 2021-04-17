 
{-# OPTIONS --without-K #-}

module ecats.basic-props.groupoid where

open import ecats.basic-defs.ecat-def&not
open import ecats.basic-defs.isomorphism
open import ecats.basic-defs.opposite
open import ecats.basic-defs.groupoid
open import ecats.functors.defs.id-on-objs


module groupoids-are-self-dual {𝔾 : ecategory}(isgpd : is-groupoid 𝔾) where
  module 𝔾 where
    open ecategory-aux 𝔾 public
    open is-groupoid isgpd public
    open iso-defs 𝔾 public
  module 𝔾ᵒ where
    open ecategory (𝔾 ᵒᵖ) using (isecat; _∘_) public

  dbl-inv-id : {X Y : 𝔾.Obj}(f : || 𝔾.Hom X Y ||) → 𝔾.inv (𝔾.inv f) 𝔾.~ f
  dbl-inv-id f = 𝔾.inv-uq-r (𝔾.isisopair (𝔾.inv f)) (𝔾.inv-iso-pair (𝔾.isisopair f))
  
  into-dual : idobj-efunctor 𝔾.isecat 𝔾ᵒ.isecat
  into-dual = record
    { ₐ = 𝔾.inv
    ; isfnct = record
             { ext = λ {_} {_} {f} {f'} → 𝔾.inv-uq (𝔾.isisopair f) (𝔾.isisopair f')
             ; id = λ {A} → 𝔾.inv-uq-r (𝔾.isisopair (𝔾.idar A)) (𝔾.idar-is-isopair A)
             ; cmp = λ f g → 𝔾.inv-uq-r (𝔾.isopair-cmp (𝔾.isisopair f) (𝔾.isisopair g))
                                         (𝔾.isisopair (g 𝔾.∘ f))
             }
    }

  out-dual : idobj-efunctor 𝔾ᵒ.isecat 𝔾.isecat
  out-dual = record
    { ₐ = 𝔾.inv
    ; isfnct = record
             { ext = λ {_} {_} {f} {f'} → 𝔾.inv-uq (𝔾.isisopair f) (𝔾.isisopair f')
             ; id = λ {A} → 𝔾.inv-uq-r (𝔾.isisopair (𝔾.idar A)) (𝔾.idar-is-isopair A)
             ; cmp = λ f g → 𝔾.inv-uq-r (𝔾.isopair-cmp (𝔾.isisopair g) (𝔾.isisopair f))
                                         (𝔾.isisopair (g 𝔾ᵒ.∘ f))
             }
    }

  self-dual-iso-pair : is-idobj-iso-pair into-dual out-dual
  self-dual-iso-pair = record
    { iddom = dbl-inv-id
    ; idcod = dbl-inv-id
    }

  self-dual-iso : is-idobj-isomorphism into-dual
  self-dual-iso = record
    { inv = out-dual
    ; isisopair = self-dual-iso-pair
    }

-- end groupoids-are-self-dual
