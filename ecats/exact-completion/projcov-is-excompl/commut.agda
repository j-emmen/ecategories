
{-# OPTIONS --without-K #-}

module ecats.exact-completion.projcov-is-excompl.commut where

open import ecats.basic-defs.ecat-def&not
open import ecats.basic-defs.regular-ecat
open import ecats.basic-defs.exact-ecat
open import ecats.finite-limits.defs.collective
open import ecats.functors.defs.efunctor-d&n
open import ecats.functors.defs.basic-defs
open import ecats.functors.defs.natural-transformation
open import ecats.functors.defs.natural-iso
open import ecats.functors.defs.left-covering
open import ecats.functors.defs.projective-cover
open import ecats.exact-completion.def
open import ecats.exact-completion.CVconstruction
open import ecats.exact-completion.CVconstr-is-excompl
open import ecats.exact-completion.projcov-is-excompl.def
open import ecats.exact-completion.projcov-is-excompl.eqv-to-CVconstr




-- Commutativity of the functor ↑ex F : 𝔼 → 𝔻 induced by a left covering F : ℙ → 𝔻 into 𝔻 exact.


module proj-cover-universal-comm {𝔼 : ecategory}(ex𝔼 : is-exact 𝔼)
                                 {ℙ : ecategory}(fwlℙ : has-fin-weak-limits ℙ)
                                 {PC : efunctor ℙ 𝔼}(lcovPC : is-left-covering PC)
                                 (pjcPC : is-projective-cover PC)
                                 where  
  private
    module CVex where
      open efunctor-aux CVex ℙ [ fwlℙ ] public
      open is-exwlex-completion (CVconstr-is-excompl fwlℙ) public
    module PC where
      open efunctor-aux PC public
      open is-projective-cover pjcPC public
  open proj-cover-universal-def ex𝔼 fwlℙ lcovPC pjcPC
  private
    module ↑PC where
      open efunctor-aux (pjc↑ex ex𝔼 lcovPC) public
      open pjc-eqv-CV ex𝔼 fwlℙ lcovPC pjcPC public

  pjc↑ex-tr : {𝔻 : ecategory}(ex𝔻 : is-exact 𝔻){F : efunctor ℙ 𝔻}(lcovF : is-left-covering F)
                 → (F pjc↑ex[ ex𝔻 , lcovF ]) ○ PC ≅ₐ F
  pjc↑ex-tr {𝔻}ex𝔻 {F} lcovF = natiso-vcmp
    ↑F.tr
    (natiso-vcmp (natiso-hcmp (≅ₐrefl {F = ↑F.fctr})
                              ↑PC.inv-tr)
                 (≅ₐsym (○ass {F = PC} {↑PC.inv} {↑F.fctr})))
    where module ↑F = CVex.emb-unv ex𝔻 lcovF
-- end proj-cover-universal-comm
