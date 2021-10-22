
{-# OPTIONS --without-K  #-}

module ecats.exact-completion.projcov-is-excompl where

open import ecats.basic-defs.ecat-def&not
open import ecats.basic-defs.exact-ecat
open import ecats.finite-limits.defs.collective
open import ecats.functors.defs.efunctor-d&n
open import ecats.functors.defs.left-covering
open import ecats.functors.defs.projective-cover
--open import ecats.functors.props.projective-cover
open import ecats.exact-completion.def
open import ecats.exact-completion.projcov-is-excompl.eqv-to-CVconstr
open import ecats.exact-completion.projcov-is-excompl.def
open import ecats.exact-completion.projcov-is-excompl.commut
open import ecats.exact-completion.projcov-is-excompl.is-exact-fun
open import ecats.exact-completion.projcov-is-excompl.uniqueness

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
  ; emb-full = pjc.isfull
  ; emb-faith = pjc.isfaith
  ; emb-lcov = lcovPC
  ; emb-unv = λ ex𝔻 lcovF → record
            { fctr = ↑ex ex𝔻 lcovF
            ; tr = ↑ex-tr ex𝔻 lcovF
            ; ex = ↑ex-is-exact ex𝔻 lcovF
            ; uq = ↑ex-uq ex𝔻 lcovF
            }
  }
  where module pjc = is-projective-cover pjcPC
        open proj-cover-universal-def ex𝔼 fwlℙ lcovPC pjcPC
        open proj-cover-universal-comm ex𝔼 fwlℙ lcovPC pjcPC
        open proj-cover-universal-is-exact ex𝔼 fwlℙ lcovPC pjcPC
        open proj-cover-universal-uniq ex𝔼 fwlℙ lcovPC pjcPC
