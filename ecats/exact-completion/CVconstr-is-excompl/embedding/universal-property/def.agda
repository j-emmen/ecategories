
{-# OPTIONS --without-K #-}

module ecats.exact-completion.CVconstr-is-excompl.embedding.universal-property.def where

open import ecats.basic-defs.ecat-def&not
open import ecats.basic-defs.regular-ecat
open import ecats.basic-defs.exact-ecat
open import ecats.basic-props.exact-ecat
open import ecats.finite-limits.defs.collective
open import ecats.functors.defs.efunctor-d&n
open import ecats.functors.defs.basic-defs
open import ecats.functors.defs.left-covering
open import ecats.constructions.ecat-eqrel
open import ecats.exact-completion.CVconstruction
open import ecats.exact-completion.CVconstr-is-excompl.embedding.universal-property.eqrel-from-peq public



-- Definition of the functor Ex ℂ [ hasfwl ] → 𝔼 induced by a left covering ℂ → 𝔼 into 𝔼 exact.

CV↑ex : {ℂ : ecategory} (hasfwl : has-fin-weak-limits ℂ)
        {𝔼 : ecategory} (exE : is-exact 𝔼)
        {F : efunctor ℂ 𝔼} (Flcov : is-left-covering F)
             → efunctor Ex ℂ [ hasfwl ] 𝔼
CV↑ex hasfwl {𝔼} exE Flcov = QER exE ○ Peq2Rel hasfwl 𝔼-is-regular Flcov
                             where 𝔼-is-regular : is-regular 𝔼
                                   𝔼-is-regular = exact-cat-props.is-reg exE

syntax CV↑ex hasfwl exE {F} Flcov = F CV↑ex[ hasfwl , exE , Flcov ]

-- end exact-compl-universal-def
