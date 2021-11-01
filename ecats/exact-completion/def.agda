
{-# OPTIONS --without-K #-}

module ecats.exact-completion.def where

open import ecats.basic-defs.ecat-def&not
open import ecats.finite-limits.defs.collective
open import ecats.basic-defs.exact-ecat
open import ecats.basic-props.exact-ecat
open import ecats.functors.defs.efunctor-d&n
open import ecats.functors.defs.natural-transformation
open import ecats.functors.defs.basic-defs
open import ecats.functors.defs.preserving-functor
open import ecats.functors.defs.left-covering
open import ecats.functors.props.left-covering

--------------------------------------------------------------------------
-- An exact completion of ℂ
-- is a full and faithful ℂ → Ex[ℂ] into Ex[ℂ] exact
-- which is initial among left-covering functors ℂ → 𝔼 into 𝔼 exact.
--------------------------------------------------------------------------


record exwlex-universal-prop {ℂ 𝔼 : ecategory}(emb : efunctor ℂ 𝔼)
                             {𝔻 : ecategory}(ex𝔻 : is-exact 𝔻)
                             {F : efunctor ℂ 𝔻}(lcovF : is-left-covering F)
                             : Set₂ where
  field
    fctr : efunctor 𝔼 𝔻
    tr : fctr ○ emb ≅ₐ F
    ex : is-exact-functor fctr
    uq : {G : efunctor 𝔼 𝔻}(exG : is-exact-functor G)(trG : G ○ emb ≅ₐ F)
            → G ≅ₐ fctr


record is-exwlex-completion {ℂ : ecategory}(hasfwl : has-fin-weak-limits ℂ)
                            {Exℂ : ecategory}(emb : efunctor ℂ Exℂ)
                            : Set₂ where
  field
    cat-ex : is-exact Exℂ
    emb-full : is-full emb
    emb-faith : is-faithful emb
    emb-lcov : is-left-covering emb
    emb-unv : {𝔻 : ecategory}(ex𝔻 : is-exact 𝔻)
              {F : efunctor ℂ 𝔻}(lcovF : is-left-covering F)
                → exwlex-universal-prop emb ex𝔻 lcovF
  module full = is-full emb-full
  module faith = is-faithful emb-faith
  module emb-unv {𝔻 : ecategory}(ex𝔻 : is-exact 𝔻)
                 {F : efunctor ℂ 𝔻}(lcovF : is-left-covering F)
                 = exwlex-universal-prop (emb-unv ex𝔻 lcovF)
  je : {𝔼 : ecategory}(ex𝔼 : is-exact 𝔼){G G' : efunctor Exℂ 𝔼}
       (exG : is-exact-functor G)(exG' : is-exact-functor G')
          → G ○ emb ≅ₐ G' ○ emb → G ≅ₐ G'
  je {𝔼} ex𝔼 {G} {G'} exG exG' α = natiso-vcmp {G = unv'.fctr}
     (≅ₐsym (unv'.uq exG' (≅ₐrefl {F = G' ○ emb})))
     (unv'.uq exG α)
     where open has-fin-weak-limits hasfwl using (hasweql; haswpb)
           open is-exact cat-ex using () renaming (hasfl to flExℂ)
           open exact-cat-props ex𝔼 using () renaming (is-reg to reg𝔼)
           module unv' = emb-unv ex𝔼 {G' ○ emb} (ex○lcov-is-lcov hasweql haswpb flExℂ reg𝔼 emb-lcov exG')
     -- need to prove that left covering followed by exact is left covering

syntax is-exwlex-completion {ℂ} hasfwl emb = emb is-exact-completion-of ℂ [ hasfwl ]




{-
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
-}
{-
    univ : {𝔻 : ecategory}(ex𝔻 : is-exact 𝔻)
           {G : efunctor ℂ 𝔻}(lcovG : is-left-covering G)
             → univprop-data {𝔻} G
  module univ {𝔻 : ecategory}(ex𝔻 : is-exact 𝔻)
              {G : efunctor ℂ 𝔻}(lcovG : is-left-covering G)
              = univprop-data G (univ ex𝔻 lcovG)
-}
  --open univ public


