
{-# OPTIONS --without-K #-}

module ecats.exact-completion.characterisation where

open import ecats.basic-defs.ecat-def&not
open import ecats.basic-defs.isomorphism
open import ecats.basic-defs.exact-ecat
open import ecats.basic-props.exact-ecat
open import ecats.finite-limits.defs.collective
open import ecats.functors.defs.efunctor-d&n
open import ecats.functors.defs.natural-transformation
open import ecats.functors.defs.natural-iso
open import ecats.functors.defs.basic-defs
open import ecats.functors.defs.preserving-functor
open import ecats.functors.defs.projective-cover
open import ecats.functors.defs.left-covering
open import ecats.functors.props.basic-props
open import ecats.functors.props.preserving-functor
open import ecats.functors.props.left-covering
open import ecats.functors.props.projective-cover
open import ecats.exact-completion.def
open import ecats.exact-completion.CVconstruction
open import ecats.exact-completion.CVconstr-is-excompl
open import ecats.exact-completion.CVconstr-is-excompl.embedding.is-projective-cover

--open import ecats.exact-completion.CVconstr-is-excompl.embedding.universal-property.def



-- The underlying functor of an exact completion of a category ℂ is a projective cover.
-- It follows that projective covers out of ℂ into exact categories are the initial objects
-- in the (non-full) subcategory of ℂ/Cat on left covering functors into exact categories
-- and exact functors.


module exwlex-completion-is-unique {ℂ : ecategory}(fwlℂ : has-fin-weak-limits ℂ)
                                   {𝔻 : ecategory}(D : efunctor ℂ 𝔻)
                                   (exwlexD : is-exwlex-completion fwlℂ D)
                                   {𝔼 : ecategory}(E : efunctor ℂ 𝔼)
                                   (exwlexE : is-exwlex-completion fwlℂ E)
                                   where
  private
    module ℂ = ecategory ℂ
    module 𝔻 = ecategory 𝔻
    module 𝔼 = ecategory 𝔼
    module D where
      open efunctor-aux D public
      open is-exwlex-completion exwlexD public
    module E where
      open efunctor-aux E public
      open is-exwlex-completion exwlexE public
    module E↑ where
      open D.emb-unv E.cat-ex E.emb-lcov public
      --open efunctor-aux fctr public
    module D↑ where
      open E.emb-unv D.cat-ex D.emb-lcov public
      --open efunctor-aux fctr public
    D↑○E↑-ex : is-exact-functor (D↑.fctr ○ E↑.fctr)
    D↑○E↑-ex = exact-cmp E↑.ex D↑.ex
    E↑○D↑-ex : is-exact-functor (E↑.fctr ○ D↑.fctr)
    E↑○D↑-ex = exact-cmp D↑.ex E↑.ex
    trcod : (D↑.fctr ○ E↑.fctr) ○  D ≅ₐ IdF ○ D
    trcod = natiso-vcmp
      (≅ₐsym (○lid {F = D}))
      (natiso-vcmp D↑.tr
                   (natiso-vcmp (natiso-hcmp (≅ₐrefl {F = D↑.fctr})
                                             E↑.tr)
                                (≅ₐsym (○ass {F = D} {E↑.fctr} {H = D↑.fctr}))
                   ))
    trdom : (E↑.fctr ○ D↑.fctr) ○ E ≅ₐ IdF ○ E
    trdom = natiso-vcmp
      (≅ₐsym (○lid {F = E}))
      (natiso-vcmp E↑.tr
                   (natiso-vcmp (natiso-hcmp (≅ₐrefl {F = E↑.fctr})
                                             D↑.tr)
                                (≅ₐsym (○ass {F = E} {D↑.fctr} {E↑.fctr}))
                   ))
    idcod : D↑.fctr ○ E↑.fctr ≅ₐ IdF
    idcod = D.je D.cat-ex D↑○E↑-ex (IdF-is-exact {𝔻}) trcod
    iddom : E↑.fctr ○ D↑.fctr ≅ₐ IdF
    iddom = E.je E.cat-ex E↑○D↑-ex (IdF-is-exact {𝔼}) trdom
    module idcod = natural-iso idcod
    module iddom = natural-iso iddom
  -- end private

  eqv↑ : is-equivalence-pair D↑.fctr E↑.fctr
  eqv↑ = record
    { ι1 = idcod
    ; ι2 = iddom
    }

  adjeqv↑ adjeqv↑direct : is-adj-equivalence-pair D↑.fctr E↑.fctr
  adjeqv↑ = eqv-is-adj-eqv-ε eqv↑
          where open equivalence-props D↑.fctr E↑.fctr
{-
  adjeqv↑direct = record
    { ι1 = idcod
    ; ι2 = iddom
    ; trid₁ = λ {X} → {!!}
    ; trid₂ = {!!}
    }
-}

-- end exwlex-completion-is-unique


module exwlex-completion-is-proj-cover {ℂ : ecategory}(fwlℂ : has-fin-weak-limits ℂ)
                                       {𝔼 : ecategory}(emb : efunctor ℂ 𝔼)
                                       (isexwlex : is-exwlex-completion fwlℂ emb)
                                       where
  private
    module ℂ = ecategory ℂ
    module 𝔼 = ecategory 𝔼
    module emb where
      open efunctor-aux emb public
      open is-exwlex-completion isexwlex public
    ex𝔼 : is-exact 𝔼
    ex𝔼 = emb.cat-ex
    module Exℂ = ecategory Ex ℂ [ fwlℂ ]
    module CVex where
      open efunctor-aux CVex ℂ [ fwlℂ ] public
      open is-exwlex-completion (CVconstr-is-excompl fwlℂ) public
      pjc : is-projective-cover CVex ℂ [ fwlℂ ]
      pjc = excmpl-embed-is-projective-cover fwlℂ
      module pjc where
        open is-projective-cover pjc public
        open projective-cover-props pjc public
    -- the canonical extension Exℂ → 𝔼 of emb along CVex
    module emb↑ where
      open CVex.emb-unv ex𝔼 emb.emb-lcov public
      open efunctor-aux fctr public
      open is-exact-functor ex public    
    -- the canonical extension 𝔼 → Exℂ of CVex along emb
    module CVex↑ where
      open emb.emb-unv CVex.cat-ex CVex.emb-lcov public
      open efunctor-aux fctr public
      open is-exact-functor ex public

  emb≡CVex : is-adj-equivalence-pair emb↑.fctr CVex↑.fctr
  emb≡CVex = adjeqv↑
       where open exwlex-completion-is-unique fwlℂ emb isexwlex (CVex ℂ [ fwlℂ ]) (CVconstr-is-excompl fwlℂ)

  private
    module emb↑○CVex where
      open efunctor-aux (emb↑.fctr ○ CVex ℂ [ fwlℂ ]) public
      -- emb↑○CVex is a projective cover followed by an equivalence, so a projective cover
      pjc : is-projective-cover (emb↑.fctr ○ CVex ℂ [ fwlℂ ])
      pjc = CVex.pjc.eqv-pjc {F = emb↑.fctr} (record { inv =  CVex↑.fctr ; isadjeqvp = emb≡CVex })
      module pjc where
        open is-projective-cover pjc public
        open projective-cover-props pjc public
      
  -- emb is naturally isomorphic to the projective cover emb↑ ○ CVex, so a projective cover
  ispjc : is-projective-cover emb
  ispjc = emb↑○CVex.pjc.iso-pjc emb↑.tr

-- end exwlex-completion-is-proj-cover



exwlex-compl-is-proj-cover : {ℂ : ecategory}(fwlℂ : has-fin-weak-limits ℂ)
                             {𝔼 : ecategory}(emb : efunctor ℂ 𝔼)
                               → is-exwlex-completion fwlℂ emb
                                 → is-projective-cover emb
exwlex-compl-is-proj-cover fwlℂ emb isexwlex = ispjc
                                    where open exwlex-completion-is-proj-cover fwlℂ emb isexwlex
                              
