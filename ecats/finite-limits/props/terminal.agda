
{-# OPTIONS --without-K #-}

module ecats.finite-limits.props.terminal where

open import ecats.basic-defs.ecat-def&not
--open import ecats.basic-defs.commut-shapes
open import ecats.basic-defs.isomorphism
open import ecats.finite-limits.defs.terminal
--open import ecats.finite-limits.d&n-bin-product
--open import ecats.finite-limits.d&n-pullback


module terminal-props {ℓₒ ℓₐ ℓ~ : Level}(ℂ : ecategoryₗₑᵥ ℓₒ ℓₐ ℓ~) where
  open ecategory-aux ℂ
  --open comm-shapes ℂ
  open iso-defs ℂ
  open terminal-defs ℂ
  --open binary-products ℂ
  --open pullback-squares ℂ

  !uq-iso : {T T' : Obj} → is-terminal T → is-terminal T' → T ≅ₒ T'
  !uq-iso {T} {T'} !T !T' = record
    { a12 = !T'.! T
    ; a21 = !T.! T'
    ; isop = record { iddom = !T.!uqg ; idcod = !T'.!uqg }
    }
    where module !T = is-terminal !T
          module !T' = is-terminal !T'


  iso!-is! : {T T' : Obj} → T ≅ₒ T' → is-terminal T → is-terminal T'
  iso!-is! {T} {T'} iso !T = record
    { ! = λ A → a12 ∘ ! A
    ; !uniq = λ {A} f → ~proof f                ~[ lidggˢ r idcod ⊙ assˢ ] /
                                a12 ∘ a21 ∘ f    ~[ ∘e (!uniq (a21 ∘ f)) r ]∎
                                a12 ∘ ! A ∎
    }
    where open _≅ₒ_ iso
          open is-terminal !T
    
-- end terminal-props
