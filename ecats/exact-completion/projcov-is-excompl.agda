
{-# OPTIONS --without-K  #-}

module ecats.exact-completion.projcov-is-excompl where

open import ecats.basic-defs.ecat-def&not
open import ecats.basic-defs.exact-ecat
open import ecats.finite-limits.defs.collective
open import ecats.functors.defs.efunctor-d&n
open import ecats.functors.defs.left-covering
open import ecats.functors.defs.projective-cover
open import ecats.exact-completion.def
open import ecats.exact-completion.projcov-is-excompl.universal-prop

-----------------------------------------------------------------
-- A projective cover ℙ → 𝔼 of 𝔼 exact is the exact completion
-- of ℙ  as a category with finite weak limits
-----------------------------------------------------------------

projcov-is-excompl : {𝔼 : ecategory}(ex𝔼 : is-exact 𝔼)
                     {ℙ : ecategory}(fwlℙ : has-fin-weak-limits ℙ)
                     {PC : efunctor ℙ 𝔼}(lcovPC : is-left-covering PC)
                     (pjcPC : is-projective-cover PC)
                       → is-exwlex-completion fwlℙ PC
projcov-is-excompl ex𝔼 fwlℙ lcovPC pjcPC = record
  { cat-ex = ex𝔼
  ; emb-full = PC.isfull
  ; emb-faith = PC.isfaith
  ; emb-lcov = lcovPC
  ; emb-unv = projcov-is-init-lcov-ex
  }
  where module PC = is-projective-cover pjcPC
        open proj-cover-universal-property ex𝔼 fwlℙ lcovPC pjcPC
