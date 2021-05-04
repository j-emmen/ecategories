
{-# OPTIONS --without-K #-}

module ecats.constructions.free-ecat where

open import Agda.Primitive using (Level; _⊔_)
open import tt-basics.basics
--open import tt-basics.id-type
open import tt-basics.setoids renaming (||_|| to ||_||std)
open import ecats.basic-defs.ecat-def&not
--open import ecats.concr-ecats.Std

module free-ecat-defs {ℓₒ ℓₕ : Level}{V : Set ℓₒ}(E : V → V → Set ℓₕ) where


  record non-empty-fin-path (v₁ v₂ : V) : Set (ℓₒ ⊔ ℓₕ) where
    field
      length : N
      v : (i : Fin length) → V
    v' : (i : Fin (s (s length))) → V
    v' i = sumEl {C = λ _ → V} (λ x → {!x!}) (λ _ → v₁) i
    field
      e : (i : Fin (s length)) → {!!} --E (v (Fin-emb {length} i)) (v (Fin-s {length} i))


  record fin-path (v₁ v₂ : V) : Set (ℓₒ ⊔ ℓₕ) where
    field
      length : N
      v : (i : Fin (s length)) → V
      e : (i : Fin length) → E (v (Fin-emb {length} i)) (v (Fin-s {length} i))

  empty-path : (v : V) → fin-path v v
  empty-path v = record
    { length = O
    ; v = λ _ → v
    ; e = λ ()
    }

  --dom : fin-path → V
  --dom = {!!}
