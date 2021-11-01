
{-# OPTIONS --without-K  #-}

module ecats.exact-completion.CVconstr-is-excompl.embedding.universal-prop where

open import ecats.basic-defs.ecat-def&not
open import ecats.basic-defs.exact-ecat
open import ecats.finite-limits.defs.collective
open import ecats.functors.defs.efunctor-d&n
open import ecats.functors.defs.natural-transformation
open import ecats.functors.defs.preserving-functor
open import ecats.functors.defs.left-covering
open import ecats.functors.defs.projective-cover
open import ecats.functors.props.projective-cover
open import ecats.exact-completion.def
open import ecats.exact-completion.CVconstruction
open import ecats.exact-completion.CVconstr-is-excompl.exact.is-regular
open import ecats.exact-completion.CVconstr-is-excompl.exact.is-exact
open import ecats.exact-completion.CVconstr-is-excompl.embedding.is-projective-cover
open import ecats.exact-completion.CVconstr-is-excompl.embedding.universal-property.def
open import ecats.exact-completion.CVconstr-is-excompl.embedding.universal-property.commut
open import ecats.exact-completion.CVconstr-is-excompl.embedding.universal-property.is-exact-fun
open import ecats.exact-completion.CVconstr-is-excompl.embedding.universal-property.uniqueness


CVexcmpl-is-init-lcov-ex : {ℂ : ecategory}(hasfwl : has-fin-weak-limits ℂ)
                           {𝔻 : ecategory}(ex𝔻 : is-exact 𝔻)
                           {F : efunctor ℂ 𝔻}(lcovF : is-left-covering F)  
                             → exwlex-universal-prop (CVex ℂ [ hasfwl ]) ex𝔻 lcovF
CVexcmpl-is-init-lcov-ex hasfwl ex𝔻 {F} lcovF = record
  { fctr = F CV↑ex[ hasfwl , ex𝔻 , lcovF ]
  ; ex = ex.CV↑ex-is-exact ex𝔻 lcovF
  ; tr = tr.CV↑ex-tr ex𝔻 lcovF
  ; uq = uq.CV↑ex-uq ex𝔻 lcovF
  }
  where module tr = exact-compl-universal-commut hasfwl
        module ex = exact-compl-universal-is-exact hasfwl
        module uq = exact-compl-universal-uniq hasfwl
