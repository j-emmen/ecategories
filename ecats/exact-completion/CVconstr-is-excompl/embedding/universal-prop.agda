
-- disable the K axiom:

{-# OPTIONS --without-K  #-}

-- Agda version 2.5.4.1

module ecats.exact-completion.embedding.universal-prop where

open import ecats.basic-defs.ecat-def&not
open import ecats.basic-defs.exact-ecat
open import ecats.finite-limits.defs.collective
open import ecats.functors.defs.efunctor-d&n
open import ecats.functors.defs.natural-transformation
open import ecats.functors.defs.preserving-functor
open import ecats.functors.defs.left-covering
open import ecats.exact-completion.CVconstruction
open import ecats.exact-completion.embedding.universal-property.def
open import ecats.exact-completion.embedding.universal-property.commut
open import ecats.exact-completion.embedding.universal-property.is-exact-fun
open import ecats.exact-completion.embedding.universal-property.uniqueness



module exact-compl-universal-prop {ℂ : ecategory} (hasfwl : has-fin-weak-limits ℂ)
                                  {𝔼 : ecategory} (ex𝔼 : is-exact 𝔼)
                                  {F : efunctor ℂ 𝔼} (lcovF : is-left-covering F)
                                  where
  ↑ex : efunctor Ex ℂ [ hasfwl ] 𝔼
  ↑ex = ↑exd ex𝔼 lcovF
      where open exact-compl-universal-def hasfwl renaming (↑ex to ↑exd)
  ↑ex-tr : natural-iso (↑ex ○ Γex ℂ [ hasfwl ]) F
  ↑ex-tr = ↑ex-trd ex𝔼 lcovF
         where open exact-compl-universal-commut hasfwl renaming (↑ex-tr to ↑ex-trd)
  ↑ex-is-exact : is-exact-functor ↑ex
  ↑ex-is-exact = ↑ex-is-exactd ex𝔼 lcovF
               where open exact-compl-universal-is-exact hasfwl renaming (↑ex-is-exact to ↑ex-is-exactd)
  ↑ex-uq : {G : efunctor Ex ℂ [ hasfwl ] 𝔼} (exG : is-exact-functor G)
           (Gtr : natural-iso (G ○ Γex ℂ [ hasfwl ]) F)
             → natural-iso G ↑ex
  ↑ex-uq = ↑ex-uqd ex𝔼 lcovF
         where open exact-compl-universal-uniq hasfwl renaming (↑ex-uq to ↑ex-uqd)
  module ↑ex where
    open efunctor-aux ↑ex public
    module tr = natural-iso ↑ex-tr
    module ex = is-exact-functor ↑ex-is-exact 
    module uq {G : efunctor Ex ℂ [ hasfwl ] 𝔼} (exG : is-exact-functor G)
              (Gtr : natural-iso (G ○ Γex ℂ [ hasfwl ]) F)
                = natural-iso (↑ex-uq exG Gtr)
-- end exact-compl-universal-prop
