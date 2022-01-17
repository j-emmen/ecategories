
{-# OPTIONS --without-K #-}

module ecats.constructions.free-ecat-on-refl-graph where

open import tt-basics.all-basics hiding (||_||)
open import ecats.basic-defs.ecat-def&not
open import ecats.basic-defs.isomorphism
open import ecats.basic-props.isomorphism
open import ecats.functors.defs.efunctor-d&n
open import ecats.functors.defs.natural-iso



module free-category-on-graph-defs {ℓ₁ ℓ₂ ℓ₃ : Level}(ℂ : ecategoryₗₑᵥ ℓ₁ ℓ₂ ℓ₃)
                                   {V : Set ℓ₁}(E : V → V → setoid {ℓ₂} {ℓ₃})
                                   (refl : (u : V) → || E u u ||)
                                   {FO : V → ecat.Obj ℂ}
                                   (FE : {u v : V} → || E u v || → || ecat.Hom ℂ (FO u) (FO v) ||)
                                   (FEext : {u v : V}{uv uv' : || E u v ||} → < E u v > uv ~ uv'
                                              → < ecat.Hom ℂ (FO u) (FO v) > FE uv ~ FE uv')
                                   (Frefl : (u : V) → < ecat.Hom ℂ (FO u) (FO u) > FE (refl u) ~ ecat.idar ℂ (FO u))
                                   where
  private
    ||E|| : V → V → Set ℓ₂
    ||E|| u v = || E u v ||
    module E {u v : V} = setoid-aux (E u v)
    module ℂ = ecat ℂ
    module unvprop-aux {ℓ₁' ℓ₂' ℓ₃' : Level}(𝕏 : ecategoryₗₑᵥ ℓ₁' ℓ₂' ℓ₃') where
      open ecat 𝕏 public
      open iso-defs 𝕏 public
      open iso-props 𝕏 public



  record pos-path (u v : V) : Set (ℓ₁ ⊔ ℓ₂) where
    field
      length : N
      vx : (i : Fin length) → V
    vx+end : (i : Fin (s length)) → V
    vx+end = Fin-insr length vx v
    vx+end-fst : V
    vx+end-fst = vx+end (Fin-min length)
    field
      e₀ : || E u vx+end-fst ||
      eₚ : (i : Fin length) → || E (vx i) (vx+end (Fin-suc length i)) ||
    --srt+vx+end : (i : Fin (one +N s length)) → V
    --srt+vx+end = Fin-insl (s length) vx+end u
    --e : (i : Fin (s length)) → || E (srt+vx+end i) (vx+end (Fin-suc length i)) ||

  ppath-cmp : {u v w : V} → pos-path v w → pos-path u v → pos-path u w
  ppath-cmp {u} {v} {w} vew uev = record
    { length = (s uev.length) +N vew.length
    ; vx = uev+v+vew
    ; e₀ = (||E|| u ● e₀-eq) uev.e₀
    ; eₚ = eₚ
    }
    where module vew = pos-path vew
          module uev = pos-path uev
          uev+v+vew : Fin (s uev.length +N vew.length) → V
          uev+v+vew = Fin-+unvar (s uev.length) vew.length uev.vx+end vew.vx
          all-vx : Fin (s uev.length +N s vew.length) → V
          all-vx = Fin-insr (s uev.length +N vew.length) uev+v+vew w
          
          uev+v+vew-l : (i : Fin (s uev.length))
                      → uev+v+vew (Fin-inl (s uev.length) vew.length i) == uev.vx+end i
          uev+v+vew-l = Fin-+unv-trl (s uev.length) vew.length uev.vx+end vew.vx
          uev+v+vew-r : (i : Fin vew.length)
                      → uev+v+vew (Fin-inr (s uev.length) vew.length i) == vew.vx i
          uev+v+vew-r = Fin-+unv-trr (s uev.length) vew.length uev.vx+end vew.vx

          all-vx-l : (i : Fin (s uev.length))
                      → all-vx (Fin-inl (s uev.length) (s vew.length) i) == uev.vx+end i
          all-vx-l i = =proof
            all-vx (Fin-inl (s uev.length) (s vew.length) i)
                   ==[ Fin-+unv-trl (s uev.length +N vew.length) one uev+v+vew (λ _ → w) _ ] /
                   -- using that
            -- Fin-inl (s uev.length) (s vew.length) i
            -- = Fin-inl (s uev.length +N vew.length) one (Fin-inl (s uev.length) vew.length i)
            uev+v+vew (Fin-inl (s uev.length) vew.length i)     ==[ uev+v+vew-l i ]∎
            uev.vx+end i ∎
            
          all-vx-r : (i : Fin (s vew.length))
                      → all-vx (Fin-inr (s uev.length) (s vew.length) i) == vew.vx+end i
          all-vx-r = sumrec {A = Fin vew.length} {N₁} {C = λ i → all-vx (Fin-inr (s uev.length) (s vew.length) i) == vew.vx+end i}
                            (λ i → =proof
            all-vx (Fin-inr (s uev.length) (s vew.length) (Fin-emb vew.length i))
                   ==[ Fin-+unv-trl (s uev.length +N vew.length) one uev+v+vew (λ _ → w) _ ] /
                   -- using that
            -- Fin-inr (s uev.length) (s vew.length) (Fin-emb vew.length i)
            -- = Fin-inl (s uev.length +N vew.length) one (Fin-inr (s uev.length) vew.length i)
            uev+v+vew (Fin-inr (s uev.length) vew.length i)     ==[ uev+v+vew-r i ]∎
            vew.vx+end (Fin-emb vew.length i) ∎)
                            (N₁rec =rf) -- this proves that both are w on Fin-max vew.length

          e₀-eq : uev.vx+end (Fin-min uev.length) == all-vx (Fin-min (s uev.length +N vew.length))
          e₀-eq = all-vx-l (Fin-min uev.length) ⁻¹ ■ =ap all-vx (Fin-inl-min uev.length vew.length)
          
          eₚ : (i : Fin (s uev.length +N vew.length)) → || E (uev+v+vew i) (all-vx (Fin-suc (s uev.length +N vew.length) i)) ||
          eₚ = Fin-+rec (s uev.length) vew.length
                        {A = λ i → ||E|| (uev+v+vew i) (all-vx (Fin-suc (s uev.length +N vew.length) i))}
                        ( Finsrec uev.length (λ i → =transp²cnst¹ ||E||
                                                                   (uev+v+vew-l (Fin-emb uev.length i) ⁻¹)
             (all-vx-l (Fin-suc uev.length i) ⁻¹ ■ =ap all-vx (Fin-suc-inl uev.length vew.length i))
                                                                   (uev.eₚ i))
                                            (=transp²cnst¹ ||E||
                                                           (uev+v+vew-l (Fin-max uev.length) ⁻¹)
                                                           (all-vx-r (Fin-min vew.length) ⁻¹
                                                            ■ =ap all-vx (Fin-ass₁ uev.length vew.length))
                                                           vew.e₀) )

                        ( λ i → =transp²cnst¹ ||E||
                                               (uev+v+vew-r i ⁻¹)
                                               (=proof
             vew.vx+end (Fin-suc vew.length i)               ==[ all-vx-r (Fin-suc vew.length i) ⁻¹ ] /
             all-vx (Fin-inr (s uev.length) (s vew.length) (Fin-suc vew.length i))
                                            ==[ =ap all-vx (Fin-suc-inr (s uev.length) vew.length i) ]∎
             all-vx (Fin-suc (s uev.length +N vew.length) (Fin-inr (s uev.length) vew.length i)) ∎)
                                               (vew.eₚ i ) )
