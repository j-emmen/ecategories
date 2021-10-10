
{-# OPTIONS --without-K  #-}

module ecats.exact-completion.projcov-is-excompl where

open import ecats.basic-defs.ecat-def&not
open import ecats.basic-defs.exact-ecat
open import ecats.basic-props.exact-ecat
open import ecats.functors.defs.efunctor-d&n
open import ecats.functors.defs.projective-cover
open import ecats.functors.props.projective-cover
open import ecats.exact-completion.def
open import ecats.exact-completion.projcov-is-excompl.def

-----------------------------------------------------------------
-- A projective cover ℙ → 𝔼 of 𝔼 exact is the exact completion
-- of ℙ  as a category with finite weak limits
-----------------------------------------------------------------

projcov-is-excompl : {𝔼 : ecategory} (ex𝔼 : is-exact 𝔼)
                     {ℙ : ecategory} {PC : efunctor ℙ 𝔼} (pjcPC : is-projective-cover PC)
                       → is-exwlex-completion (proj-cov-has-wlim pjcPC (is-exact.hasfl ex𝔼))
                                               PC
projcov-is-excompl ex𝔼 pjcPC = record
  { cat-ex = ex𝔼
  ; emb-full = pjc.isfull
  ; emb-faith = pjc.isfaith
  ; emb-lcov = pjcov-of-reg-is-lcov (exact2reg ex𝔼) pjcPC
  ; emb-unv = λ ex𝔻 lcovF → record
            { fctr = ↑ex  ex𝔻 lcovF
            ; tr = {!!}
            ; ex = {!!}
            ; uq = {!!}
            }
  }
  where module pjc = is-projective-cover pjcPC
        open exact-compl-universal-def ex𝔼 pjcPC
