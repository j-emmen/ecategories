
{-# OPTIONS --without-K #-}

module ecats.concr-ecats.FinStd where

open import tt-basics.basics
open import tt-basics.setoids hiding (||_||) --using (setoid)
open import ecats.basic-defs.ecat-def&not
--open import ecats.basic-defs.isomorphism
--open import ecats.basic-props.isomorphism
open import ecats.functors.defs.efunctor-d&n
open import ecats.functors.defs.basic-defs
open import ecats.functors.defs.natural-transformation
open import ecats.functors.defs.natural-iso
open import ecats.functors.defs.id-on-objs
open import ecats.functors.defs.id-on-objs-full-factorisation
open import ecats.concr-ecats.finite-ecat
open import ecats.concr-ecats.Std-lev


-- embedding of ω into Std

ωEmb : efunctorₗₑᵥ ω Std
ωEmb = record
     { FObj = Finstd
     ; FHom = λ {n} {m} → Iωₐ {n} {m}
     ; isF = record
           { ext = {!!} -- λ {n} {m} {f} {f'} eq x →
           ; id = λ {n} x → {!!}
           ; cmp = {!!}
           }
     }
     where module Std = ecategory-aux Std
           Iω-fnc : {n m : ω.Obj} → || ω.Hom n m || → Fin n → Fin m
           Iω-fnc {O} {m} n≤m = N₀rec
           Iω-fnc {s n} {s m} n≤m = Fin-insl n (λ i → Fin-suc m (Iω-fnc {n} {m} n≤m i)) (Fin-min m)
           -- Finsrec n (λ i → Fin-emb m (Iω-fnc {n} {m} n≤m i)) (Fin-suc m (Iω-fnc {n} {m} n≤m {!!}))
           Iωₐ : {n m : ω.Obj} → || ω.Hom n m || → || Std.Hom (Finstd n) (Finstd m) ||
           Iωₐ {n} {m} n≤m = free-stdmap (Iω-fnc {n} {m} n≤m)


FinStd-Emb : {n : N} → efunctorₗₑᵥ (𝔽inCat n) Std
FinStd-Emb {n} = record
  { FObj = {!!}
  ; FHom = {!!}
  ; isF = {!!}
  }
