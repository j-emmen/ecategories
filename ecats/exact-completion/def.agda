
-- disable the K axiom:

{-# OPTIONS --without-K #-}

-- Agda version 2.5.4.1

module ecats.exact-completion.def where

open import ecats.basic-defs.ecat-def&not
open import ecats.finite-limits.defs.collective
open import ecats.basic-defs.exact-ecat
open import ecats.functors.defs.efunctor-d&n
open import ecats.functors.defs.natural-transformation
open import ecats.functors.defs.basic-defs
open import ecats.functors.defs.preserving-functor
open import ecats.functors.defs.left-covering

--------------------------------------------------------------------------
-- An exact completion of ℂ
-- is a (conservative?) full and faithful ℂ → Ex[ℂ] into Ex[ℂ] exact
-- which is initial among left-covering functors ℂ → 𝔼 into 𝔼 exact.
--------------------------------------------------------------------------

module exwlex-universal-prop-data {ℂ 𝔼 : ecategory}(F : efunctor ℂ 𝔼)
                                  {𝔻 : ecategory}(G : efunctor ℂ 𝔻)
                                  where
  
  record def-props-of-fnct (fnct : efunctor 𝔼 𝔻) : Set₂ where
    field
      ex : is-exact-functor fnct
      tr :  fnct ○ F ≅ₐ G

  record is-unique-ex+tr (fnct : efunctor 𝔼 𝔻) : Set₂ where
    field
      ex+tr : def-props-of-fnct fnct
      isuq : {E : efunctor 𝔼 𝔻}(propsE : def-props-of-fnct E)
             →  E ≅ₐ fnct
    open def-props-of-fnct ex+tr public

  record univprop-data : Set₂ where
    field
      fnct : efunctor 𝔼 𝔻
      prop : is-unique-ex+tr fnct
    module fnct where
      open efunctor-aux fnct public
      open is-unique-ex+tr prop public
      --open def-props-of-fnct ex+tr public
      uq : {E : efunctor 𝔼 𝔻}(exE : is-exact-functor E)(trE : E ○ F ≅ₐ G)
              →  E ≅ₐ fnct
      uq exE trE = isuq (record { ex = exE ; tr = trE })
    {-module fnct = efunctor fnct
    module ex = is-exact-functor ex
    module tr = natural-iso tr
    module uq {E : efunctor 𝔼 𝔻}(exE : is-exact-functor E)(trE : E ○ F ≅ₐ G)
              = natural-iso (uq exE trE)-}

-- end exwlex-universal-prop-data

record exwlex-universal-prop {ℂ 𝔼 : ecategory}--(hasfwl : has-fin-weak-limits ℂ)(isex : is-exact 𝔼)
                             (emb : efunctor ℂ 𝔼)--(islcov : is-left-covering emb)
                             {𝔻 : ecategory}(ex𝔻 : is-exact 𝔻)
                             {F : efunctor ℂ 𝔻}(lcovF : is-left-covering F)
                             : Set₂ where
  --open exwlex-universal-prop-data F
  field
    fctr : efunctor 𝔼 𝔻
    tr : fctr ○ emb ≅ₐ F
    ex : is-exact-functor fctr
    uq : {G : efunctor 𝔼 𝔻}(exG : is-exact-functor G)(trG : G ○ emb ≅ₐ F)
            → G ≅ₐ fctr
{-
    univ : {𝔻 : ecategory}(ex𝔻 : is-exact 𝔻)
           {G : efunctor ℂ 𝔻}(lcovG : is-left-covering G)
             → univprop-data {𝔻} G
  module univ {𝔻 : ecategory}(ex𝔻 : is-exact 𝔻)
              {G : efunctor ℂ 𝔻}(lcovG : is-left-covering G)
              = univprop-data G (univ ex𝔻 lcovG)
-}
  --open univ public


record is-exwlex-completion {ℂ : ecategory}(hasfwl : has-fin-weak-limits ℂ)
                            {Exℂ : ecategory}(emb : efunctor ℂ Exℂ)
                            : Set₂ where
  open exwlex-universal-prop-data emb
  field
    cat-ex : is-exact Exℂ
    emb-full : is-full emb
    emb-faith : is-faithful emb
    emb-lcov : is-left-covering emb
    {-unv-prop : {𝔻 : ecategory}(ex𝔻 : is-exact 𝔻)
               {F : efunctor ℂ 𝔻}(lcovF : is-left-covering F)
                 → is-unique-ex+tr F (unv-fctr ex𝔻 lcovF)-}
    emb-unv : {𝔻 : ecategory}(ex𝔻 : is-exact 𝔻)
              {F : efunctor ℂ 𝔻}(lcovF : is-left-covering F)
                → exwlex-universal-prop emb ex𝔻 lcovF
  open is-full emb-full public
  open is-faithful emb-faith public
  --open exwlex-universal-prop emb-init public
  module unv {𝔻 : ecategory}(ex𝔻 : is-exact 𝔻)
             {F : efunctor ℂ 𝔻}(lcovF : is-left-covering F)
             = exwlex-universal-prop (emb-unv ex𝔻 lcovF)
  module check {𝔻 : ecategory}(ex𝔻 : is-exact 𝔻)
               {F : efunctor ℂ 𝔻}(lcovF : is-left-covering F)
               where
    fctr : efunctor Exℂ 𝔻
    fctr = unv.fctr ex𝔻 lcovF
    tr : fctr ○ emb ≅ₐ F
    tr = unv.tr ex𝔻 lcovF
  --open univ public

syntax is-exwlex-completion {ℂ} hasfwl emb = emb is-exact-completion-of ℂ [ hasfwl ]
    

