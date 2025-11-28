
{-# OPTIONS --without-K #-}

module ecats.constructions.free-ecat-on-refl-graph where

open import tt-basics.all-basics hiding (||_||)
open import ecats.basic-defs.ecat-def&not
open import ecats.basic-defs.isomorphism
open import ecats.basic-props.isomorphism
open import ecats.functors.defs.efunctor-d&n
open import ecats.functors.defs.natural-iso




-- Constructions of the free ecategory on a graph using inductive types

module free-ecat-on-refl-graph-via-inductive-paths {ℓ₁ ℓ₂ ℓ₃ : Level}{V : Set ℓ₁}
                                                   (E : V → V → setoid {ℓ₂} {ℓ₃})
                                                   (rf : (v : V) → || E v v ||)
                                                   where
  private
    ||E|| : V → V → Set ℓ₂
    ||E|| u v = || E u v ||
    module E {u v : V} = setoid-aux (E u v)

  -- non-empty paths
  data fin-path₀  (u v : V) : Set (ℓ₁ ⊔ ℓ₂) where
    indv : ||E|| u v → fin-path₀ u v
    apnd : {w : V} → fin-path₀ u w → ||E|| w v → fin-path₀ u v

  path₀-id : (v : V) → fin-path₀ v v
  path₀-id v = indv (rf v)

  path₀-cmp : {u v w : V} → fin-path₀ v w → fin-path₀ u v → fin-path₀ u w
  path₀-cmp (indv e) p = apnd p e
  path₀-cmp (apnd p e) p' = apnd (path₀-cmp p p') e

  twocmp : {u v w : V} → ||E|| u v → ||E|| v w → fin-path₀ u w
  twocmp e e' = path₀-cmp (indv e') (indv e)

{-
  path₀-rec : {u : V}{ℓ : Level}{PP : {v : V} → fin-path₀ u v → Set ℓ}
                → (PP (indv (rf u)))
                → ({w v : V}(p : fin-path₀ u w)(e : ||E|| w v) → PP (apnd p e))
                  → {v : V}(p : fin-path₀ u v) → PP p
  path₀-rec {PP = PP} P∅ Pₐ = ?

  path₀-rec-all : {ℓ : Level}{PP : {u v : V} → fin-path₀ u v → Set ℓ}
                    → ({u : V} → PP (emty {u}))
                    → ({u v w : V}(p : fin-path₀ u v)(e : ||E|| v w) → PP (apnd p e))
                      → {u v : V}(p : fin-path₀ u v) → PP p
  path₀-rec-all {PP = PP} P∅ Pₐ emty = P∅
  path₀-rec-all {PP = PP} P∅ᵢ Pₐ (apnd p e) = Pₐ p e
-}

  -- setoid of finite path₀s modulo rf as unit for concatenation
  data path₀-eq {u v : V} : fin-path₀ u v → fin-path₀ u v → Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃) where
    indv-eq : {e₁ e₂ : ||E|| u v}
                  → e₁ E.~ e₂ → path₀-eq (indv e₁) (indv e₂)
    apnd-eq : {w : V}{p₁ p₂ : fin-path₀ u w}{e₁ e₂ : ||E|| w v}
                  → path₀-eq p₁ p₂ → e₁ E.~ e₂ → path₀-eq (apnd p₁ e₁) (apnd p₂ e₂)
    path₀-lun : {p : fin-path₀ u v} → path₀-eq (apnd p (rf v)) p
    path₀-run : {e : ||E|| u v} → path₀-eq (apnd (indv (rf u)) e) (indv e)
    path₀-tran : {p₁ p₂ p₃ : fin-path₀ u v} → path₀-eq p₁ p₂ → path₀-eq p₂ p₃ → path₀-eq p₁ p₃
    path₀-sym : {p₁ p₂ : fin-path₀ u v} → path₀-eq p₁ p₂ → path₀-eq p₂ p₁

{-
    {-run₀ : {p : fin-path₀ u u} → path₀-eq p (indv (rf u))
             → ∀ {e₁ e₂} → e₁ E.~ e₂ → path₀-eq (apnd p e₁) (indv e₂)
    run₀ˢ : {p : fin-path₀ u u} → path₀-eq p (indv (rf u))
             → ∀ {e₁ e₂} → e₁ E.~ e₂ → path₀-eq (indv e₂) (apnd p e₁)-}
    run : {p : fin-path₀ u u} → path₀-eq p (indv (rf u))
             → ∀ {p₁ p₂} → path₀-eq p₁ p₂ → path₀-eq (path₀-cmp p₁ p) p₂
    runˢ : {p : fin-path₀ u u} → path₀-eq p (indv (rf u))
             → ∀ {p₁ p₂} → path₀-eq p₁ p₂ → path₀-eq p₂ (path₀-cmp p₁ p)
    lun : {e : ||E|| v v} → e E.~ rf v
             → ∀ {p₁ p₂} → path₀-eq {u} {v} p₁ p₂ → path₀-eq (apnd p₁ e) p₂
    lunˢ : {e : ||E|| v v} → e E.~ rf v
             → ∀ {p₁ p₂} → path₀-eq {u} {v} p₁ p₂ → path₀-eq p₂ (apnd p₁ e)
-}

  path₀-refl : {u v : V}(p : fin-path₀ u v) → path₀-eq p p
  path₀-refl (indv e) =
    indv-eq (E.r {a = e})
  path₀-refl (apnd p e) =
    apnd-eq (path₀-refl p) E.r

{-
  path₀-eq-sym : {u v : V}{p₁ p₂ : fin-path₀ u v}
                     → path₀-eq p₁ p₂ → path₀-eq p₂ p₁
  path₀-eq-sym (indv-eq e~e') = indv-eq (e~e' E.ˢ)
  path₀-eq-sym (apnd-eq eq e~e') = apnd-eq (path₀-eq-sym eq) (e~e' E.ˢ)
--  path₀-eq-sym (run₀ eq e~e') = run₀ˢ eq e~e'
--  path₀-eq-sym (run₀ˢ eq e~e') = run₀ eq e~e'
  path₀-eq-sym (run eqr eq) = runˢ eqr eq
  path₀-eq-sym (runˢ eqr eq) = run eqr eq
  path₀-eq-sym (lun e~r eq) = lunˢ e~r eq
  path₀-eq-sym (lunˢ e~r eq) = lun e~r eq

  path₀-eq-trans : {u v : V}{p₁ p₂ p₃ : fin-path₀ u v}
                     → path₀-eq p₁ p₂ → path₀-eq p₂ p₃ → path₀-eq p₁ p₃
  path₀-eq-trans (indv-eq x) eq' = {!!}
  path₀-eq-trans (apnd-eq eq x) eq' = {!!}

  path₀-eq-trans (run eqr eq) eq' =
    run eqr (path₀-eq-trans eq eq')
  path₀-eq-trans (runˢ eqr eq) eq' = {!eq'!}
  path₀-eq-trans (lun e~r eq) eq' = {!!}
  path₀-eq-trans (lunˢ e~r eq) eq' = {!eq'!}

{-
  path₀-eq-trans (indv-eq e₁~e₂) (indv-eq e₂~e₃) =
    indv-eq (e₁~e₂ E.⊙ e₂~e₃)
  path₀-eq-trans (indv-eq e₁~e₂) (run₀ˢ eq' e₂~e₃) =
    run₀ˢ eq' (e₂~e₃ E.⊙ e₁~e₂ E.ˢ)
  path₀-eq-trans (indv-eq e₁~e₂) (lunˢ e₂~e₃ eq') =
    lunˢ e₂~e₃ (path₀-eq-trans eq' (indv-eq (e₁~e₂ E.ˢ)))

  path₀-eq-trans (apnd-eq eq e₁~e₂) (apnd-eq eq' e₂~e₃) =
    apnd-eq (path₀-eq-trans eq eq') (e₁~e₂ E.⊙ e₂~e₃)
  path₀-eq-trans (apnd-eq eq e₁~e₂) (run₀ eq' e₂~e₃) =
    run₀ (path₀-eq-trans eq eq') (e₁~e₂ E.⊙ e₂~e₃)
  path₀-eq-trans (apnd-eq eq e₁~e₂) (lun e₂~r eq') =
    lun (e₁~e₂ E.⊙ e₂~r) (path₀-eq-trans eq eq')
  path₀-eq-trans (apnd-eq eq e₁~e₂) (lunˢ e~r eq') =
    lunˢ e~r (path₀-eq-trans eq' (apnd-eq (path₀-eq-sym eq) (e₁~e₂ E.ˢ)))

  path₀-eq-trans (run₀ eq e₁~e₂) (indv-eq x) = {!!}
  path₀-eq-trans (run₀ eq e₁~e₂) (run₀ˢ eq' x) = {!!}
  path₀-eq-trans (run₀ eq e₁~e₂) (lunˢ x eq') = {!!}

  path₀-eq-trans (run₀ˢ eq e₁~e₂) eq' = {!eq'!}

  path₀-eq-trans (lun e~r eq) eq' =
    lun e~r (path₀-eq-trans eq eq')
  path₀-eq-trans (lunˢ e~r eq) eq' = {!!}
-}


{-
  path₀-eq-trans (indv-eq e₁~e₂) (sym eq') = {!!}
  --sym (path₀-eq-trans eq' (indv-eq (e₁~e₂ E.ˢ)))
  path₀-eq-trans (run₀ eq e₁~e₂) (indv-eq e₂~e₃) =
    run₀ eq (e₁~e₂ E.⊙ e₂~e₃)
  path₀-eq-trans (run₀ eq e₁~e₂) (sym eq') = {!!}
  path₀-eq-trans (lun e~r eq) eq' =
    lun e~r (path₀-eq-trans eq eq')
  path₀-eq-trans (sym eq) eq' = {!!}
-}
-}

  HomStd : V → V → setoid {ℓ₁ ⊔ ℓ₂} {ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃}
  HomStd u v = record
    { object = fin-path₀ u v
    ; _∼_ = path₀-eq {u} {v}
    ; istteqrel = record
                { refl = path₀-refl {u} {v}
                ; sym = path₀-sym {u} {v} -- path₀-eq-
                ; tra = path₀-tran {u} {v}
                }
    }

  private
    ||H|| : V → V → Set (ℓ₁ ⊔ ℓ₂)
    ||H|| u v = || HomStd u v ||
    module H {u v : V} = setoid-aux (HomStd u v)

  path₀-cmp-extl : {u v w : V}(p₁ : fin-path₀ u v){p₂ p₂' : fin-path₀ v w}
                    → p₂ H.~ p₂' → path₀-cmp p₂ p₁ H.~ path₀-cmp p₂' p₁
  path₀-cmp-extl p₁ (indv-eq e₁~e₂) = apnd-eq (path₀-refl _) e₁~e₂
  path₀-cmp-extl p₁ (apnd-eq eq e₁~e₂) = apnd-eq (path₀-cmp-extl p₁ eq) e₁~e₂
  path₀-cmp-extl p₁ path₀-lun = path₀-lun
  path₀-cmp-extl p₁ path₀-run = apnd-eq path₀-lun E.r
  path₀-cmp-extl p₁ (path₀-tran eq₁ eq₂) = path₀-tran (path₀-cmp-extl p₁ eq₁) (path₀-cmp-extl p₁ eq₂) 
  path₀-cmp-extl p₁ (path₀-sym eq) = path₀-sym (path₀-cmp-extl p₁ eq)

  path₀-cmp-extr : {u v w : V}{p₁ p₁' : fin-path₀ u v}(p₂ : fin-path₀ v w)
                    → p₁ H.~ p₁' → path₀-cmp p₂ p₁ H.~ path₀-cmp p₂ p₁'
  path₀-cmp-extr (indv e) eq = apnd-eq eq E.r
  path₀-cmp-extr (apnd p e) eq = apnd-eq (path₀-cmp-extr p eq) E.r


  path₀-cmp-ext : {u v w : V}{p₁ p₁' : fin-path₀ u v}{p₂ p₂' : fin-path₀ v w}
                    → p₁ H.~ p₁' → p₂ H.~ p₂' → path₀-cmp p₂ p₁ H.~ path₀-cmp p₂' p₁'
  path₀-cmp-ext eq₁ eq₂ = path₀-tran (path₀-cmp-extr _ eq₁) (path₀-cmp-extl _ eq₂)

  path₀-rid : {u v : V} (p : fin-path₀ u v) → path₀-cmp p (path₀-id u) H.~ p
  path₀-rid (indv e) = path₀-run
  path₀-rid (apnd p e) = apnd-eq (path₀-rid p) E.r

  path₀-ass : {u v w z : V}(p₁ : fin-path₀ u v)(p₂ : fin-path₀ v w)(p₃ : fin-path₀ w z)
                → path₀-cmp p₃ (path₀-cmp p₂ p₁) H.~ path₀-cmp (path₀-cmp p₃ p₂) p₁
  path₀-ass p₁ p₂ (indv e) = path₀-refl _
  path₀-ass p₁ p₂ (apnd p₃ e) = apnd-eq (path₀-ass p₁ p₂ p₃) E.r
--- end free-ecat-on-graph-via-inductive-path₀s



-- module free-category-on-graph-defs {ℓ₁ ℓ₂ ℓ₃ : Level}(ℂ : ecategoryₗₑᵥ ℓ₁ ℓ₂ ℓ₃)
--                                    {V : Set ℓ₁}(E : V → V → setoid {ℓ₂} {ℓ₃})
--                                    (refl : (u : V) → || E u u ||)
--                                    {FO : V → ecat.Obj ℂ}
--                                    (FE : {u v : V} → || E u v || → || ecat.Hom ℂ (FO u) (FO v) ||)
--                                    (FEext : {u v : V}{uv uv' : || E u v ||} → < E u v > uv ~ uv'
--                                               → < ecat.Hom ℂ (FO u) (FO v) > FE uv ~ FE uv')
--                                    (Frefl : (u : V) → < ecat.Hom ℂ (FO u) (FO u) > FE (refl u) ~ ecat.idar ℂ (FO u))
--                                    where
--   private
--     ||E|| : V → V → Set ℓ₂
--     ||E|| u v = || E u v ||
--     module E {u v : V} = setoid-aux (E u v)
--     module ℂ = ecat ℂ
--     module unvprop-aux {ℓ₁' ℓ₂' ℓ₃' : Level}(𝕏 : ecategoryₗₑᵥ ℓ₁' ℓ₂' ℓ₃') where
--       open ecat 𝕏 public
--       open iso-defs 𝕏 public
--       open iso-props 𝕏 public



--   record pos-path₀ (u v : V) : Set (ℓ₁ ⊔ ℓ₂) where
--     field
--       length : N
--       vx : (i : Fin length) → V
--     vx+end : (i : Fin (s length)) → V
--     vx+end = Fin-inr length vx v
--     vx+end-fst : V
--     vx+end-fst = vx+end (Fin-min length)
--     field
--       e₀ : || E u vx+end-fst ||
--       eₚ : (i : Fin length) → || E (vx i) (vx+end (Fin-suc length i)) ||
--     --srt+vx+end : (i : Fin (one +N s length)) → V
--     --srt+vx+end = Fin-insl (s length) vx+end u
--     --e : (i : Fin (s length)) → || E (srt+vx+end i) (vx+end (Fin-suc length i)) ||

--   ppath₀-cmp : {u v w : V} → pos-path₀ v w → pos-path₀ u v → pos-path₀ u w
--   ppath₀-cmp {u} {v} {w} vew uev = record
--     { length = (s uev.length) +N vew.length
--     ; vx = uev+v+vew
--     ; e₀ = (||E|| u ● e₀-eq) uev.e₀
--     ; eₚ = eₚ
--     }
--     where module vew = pos-path₀ vew
--           module uev = pos-path₀ uev
--           uev+v+vew : Fin (s uev.length +N vew.length) → V
--           uev+v+vew = Fin-+unvar (s uev.length) vew.length uev.vx+end vew.vx
--           all-vx : Fin (s uev.length +N s vew.length) → V
--           all-vx = Fin-insr (s uev.length +N vew.length) uev+v+vew w
          
--           uev+v+vew-l : (i : Fin (s uev.length))
--                       → uev+v+vew (Fin-inl (s uev.length) vew.length i) == uev.vx+end i
--           uev+v+vew-l = Fin-+unv-trl (s uev.length) vew.length uev.vx+end vew.vx
--           uev+v+vew-r : (i : Fin vew.length)
--                       → uev+v+vew (Fin-inr (s uev.length) vew.length i) == vew.vx i
--           uev+v+vew-r = Fin-+unv-trr (s uev.length) vew.length uev.vx+end vew.vx

--           all-vx-l : (i : Fin (s uev.length))
--                       → all-vx (Fin-inl (s uev.length) (s vew.length) i) == uev.vx+end i
--           all-vx-l i = =proof
--             all-vx (Fin-inl (s uev.length) (s vew.length) i)
--                    ==[ Fin-+unv-trl (s uev.length +N vew.length) one uev+v+vew (λ _ → w) _ ] /
--                    -- using that
--             -- Fin-inl (s uev.length) (s vew.length) i
--             -- = Fin-inl (s uev.length +N vew.length) one (Fin-inl (s uev.length) vew.length i)
--             uev+v+vew (Fin-inl (s uev.length) vew.length i)     ==[ uev+v+vew-l i ]∎
--             uev.vx+end i ∎
            
--           all-vx-r : (i : Fin (s vew.length))
--                       → all-vx (Fin-inr (s uev.length) (s vew.length) i) == vew.vx+end i
--           all-vx-r = sumrec {A = Fin vew.length} {N₁} {C = λ i → all-vx (Fin-inr (s uev.length) (s vew.length) i) == vew.vx+end i}
--                             (λ i → =proof
--             all-vx (Fin-inr (s uev.length) (s vew.length) (Fin-emb vew.length i))
--                    ==[ Fin-+unv-trl (s uev.length +N vew.length) one uev+v+vew (λ _ → w) _ ] /
--                    -- using that
--             -- Fin-inr (s uev.length) (s vew.length) (Fin-emb vew.length i)
--             -- = Fin-inl (s uev.length +N vew.length) one (Fin-inr (s uev.length) vew.length i)
--             uev+v+vew (Fin-inr (s uev.length) vew.length i)     ==[ uev+v+vew-r i ]∎
--             vew.vx+end (Fin-emb vew.length i) ∎)
--                             (N₁rec =rf) -- this proves that both are w on Fin-max vew.length

--           e₀-eq : uev.vx+end (Fin-min uev.length) == all-vx (Fin-min (s uev.length +N vew.length))
--           e₀-eq = all-vx-l (Fin-min uev.length) ⁻¹ ■ =ap all-vx (Fin-inl-min uev.length vew.length)
          
--           eₚ : (i : Fin (s uev.length +N vew.length)) → || E (uev+v+vew i) (all-vx (Fin-suc (s uev.length +N vew.length) i)) ||
--           eₚ = Fin-+rec (s uev.length) vew.length
--                         {A = λ i → ||E|| (uev+v+vew i) (all-vx (Fin-suc (s uev.length +N vew.length) i))}
--                         ( Finsrec uev.length (λ i → =transp²cnst¹ ||E||
--                                                                    (uev+v+vew-l (Fin-emb uev.length i) ⁻¹)
--              (all-vx-l (Fin-suc uev.length i) ⁻¹ ■ =ap all-vx (Fin-suc-inl uev.length vew.length i))
--                                                                    (uev.eₚ i))
--                                             (=transp²cnst¹ ||E||
--                                                            (uev+v+vew-l (Fin-max uev.length) ⁻¹)
--                                                            (all-vx-r (Fin-min vew.length) ⁻¹
--                                                             ■ =ap all-vx (Fin-ass₁ uev.length vew.length))
--                                                            vew.e₀) )

--                         ( λ i → =transp²cnst¹ ||E||
--                                                (uev+v+vew-r i ⁻¹)
--                                                (=proof
--              vew.vx+end (Fin-suc vew.length i)               ==[ all-vx-r (Fin-suc vew.length i) ⁻¹ ] /
--              all-vx (Fin-inr (s uev.length) (s vew.length) (Fin-suc vew.length i))
--                                             ==[ =ap all-vx (Fin-suc-inr (s uev.length) vew.length i) ]∎
--              all-vx (Fin-suc (s uev.length +N vew.length) (Fin-inr (s uev.length) vew.length i)) ∎)
--                                                (vew.eₚ i ) )
