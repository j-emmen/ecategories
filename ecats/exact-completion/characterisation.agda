
{-# OPTIONS --without-K  #-}

module ecats.exact-completion.characterisation where

open import ecats.basic-defs.ecat-def&not
open import ecats.basic-defs.all-arrows
open import ecats.basic-defs.regular-ecat
open import ecats.basic-defs.exact-ecat
open import ecats.basic-props.epi&mono
open import ecats.basic-props.exact-ecat
open import ecats.finite-limits.all
open import ecats.functors.defs.efunctor-d&n
open import ecats.functors.defs.natural-transformation
open import ecats.functors.defs.basic-defs
open import ecats.functors.defs.preserving-functor
open import ecats.functors.defs.projective-cover
open import ecats.functors.defs.left-covering
open import ecats.functors.props.basic-props
open import ecats.functors.props.left-covering
open import ecats.functors.props.projective-cover
open import ecats.exact-completion.def
open import ecats.exact-completion.CVconstruction
open import ecats.exact-completion.CVconstr-is-excompl
open import ecats.exact-completion.CVconstr-is-excompl.embedding.is-projective-cover



-- The underlying functor of an exact completion is a projective cover, that is,
-- projective covers of exact categories are the initial among left covering functors into exact categories


module exacompl-is-proj-cover {ℂ : ecategory}(fwlℂ : has-fin-weak-limits ℂ)
                              {𝔼 : ecategory}(emb : efunctor ℂ 𝔼)
                              (isexwlex : is-exwlex-completion fwlℂ emb)
                              where
  private
    module ℂ = ecategory ℂ
    module 𝔼 = ecategory 𝔼
    module emb where
      open efunctor-props emb public
      open is-exwlex-completion isexwlex public
    -- the exact completion of ℂ
    module Exℂ where
      open ecategory Ex ℂ [ fwlℂ ] public
      open iso-defs Ex ℂ [ fwlℂ ] public
      open epis&monos-defs Ex ℂ [ fwlℂ ] public
      open epis&monos-props Ex ℂ [ fwlℂ ] public
      open image-fact-defs Ex ℂ [ fwlℂ ] public
    module CVex where
      open efunctor-aux CVex ℂ [ fwlℂ ] public
      open is-exwlex-completion (CVconstr-is-excompl fwlℂ) public
      pjc : is-projective-cover CVex ℂ [ fwlℂ ]
      pjc = excmpl-embed-is-projective-cover fwlℂ
      module pjc where
        open is-projective-cover pjc public
        open projective-cover-props pjc public
    -- the canonical functor Exℂ → 𝔼 induced by emb
    module emb↑ where
      open CVex.emb-unv emb.cat-ex emb.emb-lcov public
      open efunctor-aux fctr public
    -- the canonical functor 𝔼 → Exℂ induced by CVexℂ
    module CVex↑ where
      open emb.emb-unv CVex.cat-ex CVex.emb-lcov using (fctr) public
      open efunctor-aux fctr public
    module emb↑○CVex where
      open efunctor-aux (emb↑.fctr ○ CVex ℂ [ fwlℂ ]) public
      pjc : is-projective-cover (emb↑.fctr ○ CVex ℂ [ fwlℂ ])
      pjc = CVex.pjc.eqv-pjc {F = emb↑.fctr} {!!}
      module pjc where
        open is-projective-cover pjc public
        open projective-cover-props pjc public
      

  ispjc : is-projective-cover emb
  ispjc = emb↑○CVex.pjc.iso-pjc emb↑.tr

-- end exacompl-is-proj-cover
