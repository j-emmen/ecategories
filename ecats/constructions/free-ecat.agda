
{-# OPTIONS --without-K --show-implicit #-}

module ecats.constructions.free-ecat where

open import Agda.Primitive using (Level; _⊔_)
open import tt-basics.basics
--open import tt-basics.id-type
open import tt-basics.setoids renaming (||_|| to ||_||std)
open import ecats.basic-defs.ecat-def&not
--open import ecats.concr-ecats.Std

module free-ecat-defs {ℓₒ ℓₕ : Level}{V : Set ℓₒ}(E : V → V → setoid {ℓₕ} {ℓₕ}) where

{-
  record non-empty-fin-path (v₁ v₂ : V) : Set (ℓₒ ⊔ ℓₕ) where
    field
      length : N
      v : (i : Fin length) → V
    v' : (i : Fin (s (s length))) → V
    v' i = sumEl {C = λ _ → V} (λ x → {!x!}) (λ _ → v₁) i
    field
      e : (i : Fin (s length)) → {!!} --E (v (Fin-emb {length} i)) (v (Fin-s {length} i))
-}

  --data FinPathsFrom (c d : V)(length : N) : Set (ℓₒ ⊔ ℓₕ) where
    --Fin (s length) → V
    

  record FinPathsᵣ (d c : V) : Set (ℓₒ ⊔ ℓₕ) where
    field
      e₀ : || E d c ||
      v : (length : N)(i : Fin (s length)) → V
      --eᵈ : || E d 
    {-flip : Finᵢ (s (s length)) → Finᵢ (s (s length))
    flip f0 = {!!}
    flip (finj f0) = {!!}
    flip (finj (finj n)) = {!!}-}
    --flip (inl x) = Finsrec {n = {!!}} {C = λ _ → Fin (s (s length))} {!!} {!!} {!!}
    --flip (inr x) = inr x


  -- non-empty path between endpoints

  realpath : (d c : V)(length : N) → Set (ℓₒ ⊔ ℓₕ)
  realpath d c length = Σ (Fin length → V)
                          λ v → (i : Fin (s length))
                                  → || E (addends v (Fin-emb {s length} i))
                                          (addends v (Fin-suc {s length} i)) ||
                      where addends : (Fin length → V) → Fin (s (s length)) → V
                            addends v = Fin-insr {n = s length} (Fin-insl {n = length} v d) c
    
  
  record fin-path (d c : V)(length : N) : Set (ℓₒ ⊔ ℓₕ) where
    field
      v : Fin length → V
    vandends : Fin (s (s length)) → V
    vandends = Fin-insr {n = s length} (Fin-insl {n = length} v d) c
    field
      e : (i : Fin (s length)) → || E (vandends (Fin-emb {s length} i))
                                       (vandends (Fin-suc {s length} i)) ||
    ck : Set
    ck = {!vandends (Fin-O {s length})!}


  ck : {d c : V}{l : N}(fp : fin-path d c (s l)) → || E d (fin-path.v fp (Fin-O {l})) ||
  ck fp = {!fin-path.e fp ?!}
      
  
  record fin-path-from (v₀ : V)(length : N) : Set (ℓₒ ⊔ ℓₕ) where
    field
      v : Fin length → V
    v' : Fin (s length) → V
    v' = Fin-insl {n = length} v v₀
    field
      e : (i : Fin length) → || E (v' (Fin-emb {length} i)) (v' (Fin-suc {length} i)) ||
    
  
  record fin-pathᵣ : Set (ℓₒ ⊔ ℓₕ) where
    field
      length : N
      v : (i : Fin (s length)) → V
      e : (i : Fin length) → || E (v (Fin-emb {length} i)) (v (Fin-suc {length} i)) ||


  dom cod : fin-pathᵣ → V
  dom p = p.v (Fin-O {p.length})
        where module p = fin-pathᵣ p
  cod p = p.v (Fin-max {p.length})
        where module p = fin-pathᵣ p


  -- record FPath (v₁ v₂ : V) : setoid {ℓₕ} {ℓₕ} where
  --   field
  --     p : fin-path
  --     d :
  --     c :
  
  -- empty-path : (v : V) → fin-path
  -- empty-path v = record
  --   { length = O
  --   ; v = λ _ → v
  --   ; e = λ ()
  --   }
