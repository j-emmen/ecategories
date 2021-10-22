
{-# OPTIONS --without-K #-}

module ecats.exact-completion.projcov-is-excompl.uniqueness where

open import ecats.basic-defs.ecat-def&not
open import ecats.basic-defs.exact-ecat
open import ecats.finite-limits.defs.collective
open import ecats.functors.defs.efunctor-d&n
open import ecats.functors.defs.natural-transformation
open import ecats.functors.defs.basic-defs
open import ecats.functors.defs.preserving-functor
open import ecats.functors.defs.left-covering
open import ecats.functors.defs.projective-cover
open import ecats.functors.props.preserving-functor
open import ecats.exact-completion.def
open import ecats.exact-completion.CVconstruction
open import ecats.exact-completion.CVconstr-is-excompl
open import ecats.exact-completion.projcov-is-excompl.def
open import ecats.exact-completion.projcov-is-excompl.eqv-to-CVconstr



-- Definition of the functor Ex ℂ [ hasfwl ] → 𝔼 induced by a left covering ℂ → 𝔼 into 𝔼 exact.

module proj-cover-universal-uniq {𝔼 : ecategory}(ex𝔼 : is-exact 𝔼)
                                 {ℙ : ecategory}(fwlℙ : has-fin-weak-limits ℙ)
                                 {PC : efunctor ℙ 𝔼}(lcovPC : is-left-covering PC)
                                 (pjcPC : is-projective-cover PC)
                                 where
  open proj-cover-universal-def ex𝔼 fwlℙ lcovPC pjcPC
  private
    module CV↑PC where
      open pjc-eqv-CV ex𝔼 fwlℙ lcovPC pjcPC public
      open is-adj-equivalence-pair isaeqvp public

  module ↑ex-uniqueness {𝔻 : ecategory}(ex𝔻 : is-exact 𝔻)
                        {F : efunctor ℙ 𝔻}(lcovF : is-left-covering F)
                        {G : efunctor 𝔼 𝔻}(exG : is-exact-functor G)(trG : G ○ PC ≅ₐ F)
                        where
    private
      module CV↑F = is-exwlex-completion.emb-unv (CVconstr-is-excompl fwlℙ) ex𝔻 lcovF
    uq-aux : G ○ CV↑PC.fctr ≅ₐ CV↑F.fctr
    uq-aux = CV↑F.uq (exact-cmp CV↑PC.ex exG)
                     (natiso-vcmp (natiso-vcmp trG
                                               (natiso-hcmp (≅ₐrefl {F = G})
                                                            CV↑PC.tr))
                     (≅ₐsym (○ass {F = CVex ℙ [ fwlℙ ]} {CV↑PC.fctr} {G})))

    uq : G ≅ₐ F ↑ex[ ex𝔻 , lcovF ]
    uq = natiso-vcmp (natiso-hcmp uq-aux
                                  (≅ₐrefl {F = CV↑PC.inv}))
                     (natiso-vcmp (○ass {F = CV↑PC.inv} {CV↑PC.fctr} {G})
                                  (natiso-vcmp (natiso-hcmp (≅ₐrefl {F = G}) CV↑PC.ι1⁻¹)
                                               (≅ₐsym (○rid {F = G}))))
-- end ↑ex-uniqueness


  ↑ex-uq : {𝔻 : ecategory}(ex𝔻 : is-exact 𝔻){F : efunctor ℙ 𝔻}(lcovF : is-left-covering F)
             {G : efunctor 𝔼 𝔻}(exG : is-exact-functor G)
             → G ○ PC ≅ₐ F → G ≅ₐ F ↑ex[ ex𝔻 , lcovF ]
  ↑ex-uq {𝔻} ex𝔻 {F} lcovF {G} exG trG = uq
                                         where open ↑ex-uniqueness ex𝔻 lcovF exG trG
-- end proj-cover-universal-uniq
