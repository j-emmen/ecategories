
{-# OPTIONS --without-K #-}

module ecats.exact-completion.projcov-is-excompl.universal-prop where


open import ecats.basic-defs.ecat-def&not
open import ecats.basic-defs.exact-ecat
open import ecats.finite-limits.defs.collective
open import ecats.functors.defs.efunctor-d&n
open import ecats.functors.defs.left-covering
open import ecats.functors.defs.projective-cover
open import ecats.exact-completion.def
open import ecats.exact-completion.projcov-is-excompl.eqv-to-CVconstr
open import ecats.exact-completion.projcov-is-excompl.def
open import ecats.exact-completion.projcov-is-excompl.commut
open import ecats.exact-completion.projcov-is-excompl.is-exact-fun
open import ecats.exact-completion.projcov-is-excompl.uniqueness

module proj-cover-universal-property {𝔼 : ecategory}(ex𝔼 : is-exact 𝔼)
                                     {ℙ : ecategory}(fwlℙ : has-fin-weak-limits ℙ)
                                     {PC : efunctor ℙ 𝔼}(lcovPC : is-left-covering PC)
                                     (pjcPC : is-projective-cover PC)
                                     where

  projcov-is-init-lcov-ex : {𝔻 : ecategory}(ex𝔻 : is-exact 𝔻)
                            {F : efunctor ℙ 𝔻}(lcovF : is-left-covering F)  
                              → exwlex-universal-prop PC ex𝔻 lcovF
  projcov-is-init-lcov-ex ex𝔻 {F} lcovF = record
    { fctr = F pjc↑ex[ ex𝔻 , lcovF ]
    ; ex = ↑ex-is-exact ex𝔻 lcovF
    ; tr = pjc↑ex-tr ex𝔻 lcovF
    ; uq = ↑ex-uq ex𝔻 lcovF
    }
    where open proj-cover-universal-def ex𝔼 fwlℙ lcovPC pjcPC
          open proj-cover-universal-comm ex𝔼 fwlℙ lcovPC pjcPC
          open proj-cover-universal-is-exact ex𝔼 fwlℙ lcovPC pjcPC
          open proj-cover-universal-uniq ex𝔼 fwlℙ lcovPC pjcPC
-- end proj-cover-universal-propperty
