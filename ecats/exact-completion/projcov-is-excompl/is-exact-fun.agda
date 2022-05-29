
{-# OPTIONS --without-K  #-}

module ecats.exact-completion.projcov-is-excompl.is-exact-fun where

open import ecats.basic-defs.ecat-def&not
open import ecats.basic-defs.exact-ecat
open import ecats.finite-limits.defs.collective
open import ecats.functors.defs.efunctor-d&n
open import ecats.functors.defs.basic-defs
open import ecats.functors.defs.preserving-functor
open import ecats.functors.defs.left-covering
open import ecats.functors.defs.projective-cover
open import ecats.functors.props.basic-props
open import ecats.functors.props.preserving-functor
open import ecats.exact-completion.def
open import ecats.exact-completion.CVconstruction
open import ecats.exact-completion.CVconstr-is-excompl
open import ecats.exact-completion.projcov-is-excompl.def
open import ecats.exact-completion.projcov-is-excompl.eqv-to-CVconstr



module proj-cover-universal-is-exact {𝔼 : ecategory}(ex𝔼 : is-exact 𝔼)
                                     {ℙ : ecategory}(fwlℙ : has-fin-weak-limits ℙ)
                                     {PC : efunctor ℙ 𝔼}(lcovPC : is-left-covering PC)
                                     (pjcPC : is-projective-cover PC)
                                     where
  open proj-cover-universal-def ex𝔼 fwlℙ lcovPC pjcPC
  private
    module CVex where
      open is-exwlex-completion (CVconstr-is-excompl fwlℙ) public
    module CV↑PC where
      open pjc-eqv-CV ex𝔼 fwlℙ lcovPC pjcPC public
      module inv = equivalence-props inv fctr

  ↑ex-is-exact :{𝔻 : ecategory}(ex𝔻 : is-exact 𝔻){F : efunctor ℙ 𝔻}(lcovF : is-left-covering F)
                   → is-exact-functor (F pjc↑ex[ ex𝔻 , lcovF ])
  ↑ex-is-exact ex𝔻 lcovF = exact-cmp {F = CV↑PC.inv} {CV↑F.fctr}
                                      (CV↑PC.inv.isexact (inv-is-adjeqv CV↑PC.isaeqvp))
                                      CV↑F.ex
                          where module CV↑F where
                                  open CVex.emb-unv ex𝔻 lcovF public
                                  open efunctor-aux fctr public
-- end proj-cover-universal-is-exact
