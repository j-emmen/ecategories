
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

record exwlex-universal-prop {ℂ 𝔼 : ecategory}(hasfwl : has-fin-weak-limits ℂ)(isex : is-exact 𝔼)
                             {F : efunctor ℂ 𝔼}(islcov : is-left-covering F)
                             : Set₂ where
  field
    fnct : {𝔻 : ecategory}(isexD : is-exact 𝔻)
           {G : efunctor ℂ 𝔻}(islcovG : is-left-covering G)
             → efunctor 𝔼 𝔻
    ex : {𝔻 : ecategory}(isexD : is-exact 𝔻)
         {G : efunctor ℂ 𝔻}(islcovG : is-left-covering G)
           → is-exact-functor (fnct isexD islcovG)
    tr : {𝔻 : ecategory}(isexD : is-exact 𝔻)
         {G : efunctor ℂ 𝔻}(islcovG : is-left-covering G)
           →  fnct isexD islcovG ○ F ≅ₐ G
    uq : {𝔻 : ecategory}(isexD : is-exact 𝔻)
         {G : efunctor ℂ 𝔻}(islcovG : is-left-covering G)
         {E : efunctor 𝔼 𝔻}(exE : is-exact-functor E)(trE : E ○ F ≅ₐ G)
           →  E ≅ₐ fnct isexD islcovG
  module fnct {𝔻 : ecategory}(isexD : is-exact 𝔻)
              {G : efunctor ℂ 𝔻}(islcovG : is-left-covering G)
              = efunctor (fnct isexD islcovG)
  module ex {𝔻 : ecategory}(isexD : is-exact 𝔻)
            {G : efunctor ℂ 𝔻}(islcovG : is-left-covering G)
            = is-exact-functor (ex isexD islcovG)
  module tr {𝔻 : ecategory}(isexD : is-exact 𝔻)
            {G : efunctor ℂ 𝔻}(islcovG : is-left-covering G)
            = natural-iso (tr isexD islcovG)
  module uq {𝔻 : ecategory}(isexD : is-exact 𝔻)
            {G : efunctor ℂ 𝔻}(islcovG : is-left-covering G)
            {E : efunctor 𝔼 𝔻}(exE : is-exact-functor E)(trE : E ○ F ≅ₐ G)
            = natural-iso (uq isexD islcovG exE trE)


record is-exwlex-completion {ℂ : ecategory}(hasfwl : has-fin-weak-limits ℂ)
                            {Exℂ : ecategory}(emb : efunctor ℂ Exℂ)
                            : Set₂ where
  field
    cat-ex : is-exact Exℂ
    emb-full : is-full emb
    emb-faith : is-faithful emb
    emb-lcov : is-left-covering emb
    emb-init : exwlex-universal-prop hasfwl cat-ex emb-lcov
  open is-full emb-full public
  open is-faithful emb-faith public
  open exwlex-universal-prop emb-init public

syntax is-exwlex-completion {ℂ} hasfwl emb = emb is-exact-completion-of ℂ [ hasfwl ]
    

