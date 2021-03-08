
-- disable the K axiom:

{-# OPTIONS --without-K #-}

-- Agda version 2.5.4.1

module ecats.exact-completion.definition where

open import ecats.basic-defs.ecat-def&not
open import ecats.basic-defs.exact-ecat
open import ecats.functors.defs.efunctor-d&n
open import ecats.functors.defs.natural-transformation
open import ecats.functors.defs.basic-defs
open import ecats.functors.defs.left-covering

--------------------------------------------------------------------------
-- An exact completion of ℂ
-- is a (conservative?) full and faithful ℂ → Ex[ℂ] into Ex[ℂ] exact
-- which is initial among left-covering functors ℂ → 𝔼 into 𝔼 exact.
--------------------------------------------------------------------------

record is-left-cov-initial {ℂ 𝔼 : ecategory}(isex : is-exact 𝔼)
                           {F : efunctor ℂ 𝔼}(islcov : is-left-covering F)
                           : Set₂ where
  field
    univ-fnct : {𝔻 : ecategory}(isexD : is-exact 𝔻)
                {G : efunctor ℂ 𝔻}(islcovG : is-left-covering G)
                  → efunctor 𝔼 𝔻
    univ-tr : {𝔻 : ecategory}(isexD : is-exact 𝔻)
              {G : efunctor ℂ 𝔻}(islcovG : is-left-covering G)
                →  univ-fnct isexD islcovG ○ F ≅ₐ G
    univ-eqv : {𝔻 : ecategory}(isexD : is-exact 𝔻)
               {G : efunctor ℂ 𝔻}(islcovG : is-left-covering G)
                 →  is-equivalence (univ-fnct isexD islcovG)


record is-exact-completion {ℂ Exℂ : ecategory}(emb : efunctor ℂ Exℂ)
                           : Set₂ where
  field
    isex : is-exact Exℂ
    emb-full : is-full emb
    emb-faith : is-faithful emb
    emb-lcov : is-left-covering emb
    emb-init : is-left-cov-initial isex emb-lcov
  open is-full emb-full public
  open is-faithful emb-faith public
  open is-left-cov-initial emb-init public

syntax is-exact-completion {ℂ} emb = emb is-exact-completion-of ℂ
    

