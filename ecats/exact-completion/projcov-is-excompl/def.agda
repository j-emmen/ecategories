
{-# OPTIONS --without-K #-}

module ecats.exact-completion.projcov-is-excompl.def where

open import ecats.basic-defs.ecat-def&not
open import ecats.basic-defs.exact-ecat
open import ecats.finite-limits.defs.collective
open import ecats.functors.defs.efunctor-d&n
open import ecats.functors.defs.basic-defs
open import ecats.functors.defs.left-covering
open import ecats.functors.defs.projective-cover
open import ecats.exact-completion.def
open import ecats.exact-completion.CVconstr-is-excompl
open import ecats.exact-completion.projcov-is-excompl.eqv-to-CVconstr



-- Definition of the functor 𝔼 → 𝔻 induced by a left covering ℙ → 𝔻 into 𝔻 exact.

module proj-cover-universal-def {𝔼 : ecategory}(ex𝔼 : is-exact 𝔼)
                                {ℙ : ecategory}(fwlℙ : has-fin-weak-limits ℙ)
                                {PC : efunctor ℙ 𝔼}(lcovPC : is-left-covering PC)
                                (pjcPC : is-projective-cover PC)
                                where
         
  pjc↑ex : {𝔻 : ecategory}(ex𝔻 : is-exact 𝔻){F : efunctor ℙ 𝔻}(Flcov : is-left-covering F)
              → efunctor 𝔼 𝔻
  pjc↑ex ex𝔻 Flcov = fctr ○ inv
                    where open is-exwlex-completion (CVconstr-is-excompl fwlℙ) using (emb-unv)
                          open emb-unv ex𝔻 Flcov using (fctr)
                          open pjc-eqv-CV ex𝔼 fwlℙ lcovPC pjcPC using (inv)

  syntax pjc↑ex ex𝔻 {F} Flcov = F pjc↑ex[ ex𝔻 , Flcov ]
-- end proj-cover-universal-def
