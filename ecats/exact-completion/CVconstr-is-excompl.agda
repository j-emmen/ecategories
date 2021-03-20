
-- disable the K axiom:

{-# OPTIONS --without-K #-}

-- Agda version 2.5.4.1

module ecats.exact-completion.CVconstr-is-excompl where

open import ecats.basic-defs.ecat-def&not
open import ecats.basic-defs.exact-ecat
open import ecats.finite-limits.defs&not
open import ecats.functors.defs.efunctor-d&n
open import ecats.functors.defs.left-covering
open import ecats.functors.defs.natural-transformation
open import ecats.exact-completion.def
open import ecats.exact-completion.CVconstruction
open import ecats.exact-completion.CVconstr-is-excompl.exact.is-exact
open import ecats.exact-completion.CVconstr-is-excompl.exact.is-regular
open import ecats.exact-completion.CVconstr-is-excompl.embedding.is-projective-cover
open import ecats.exact-completion.CVconstr-is-excompl.embedding.universal-prop

--------------------------------------------------------------
-- The construction by A. Carboni and E.M. Vitale is
-- the exact completion of a category with finite weak limits
--------------------------------------------------------------

CVconstr-is-excompl : {ℂ : ecategory} (hasfwl : has-fin-weak-limits ℂ)
                         → is-exwlex-completion hasfwl (CVex ℂ [ hasfwl ])
CVconstr-is-excompl hasfwl = record
  { cat-ex = exact-compl-is-exact hasfwl
  ; emb-full = CVex-full hasfwl
  ; emb-faith = CVex-faith hasfwl
  ; emb-lcov = excmpl-embed-is-left-covering hasfwl
  {-; unv-fctr = ↑ex
  ; unv-tr = tr
  ; unv-ex = ex
  ; unv-uq = uq-}
  --; unv-prop = ↑ex-uqst
  ; emb-unv = CVexcmpl-is-init-lcov-ex hasfwl
  }
  --where open exact-compl-universal-prop hasfwl

