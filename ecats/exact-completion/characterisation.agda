
{-# OPTIONS --without-K #-}
 --show-implicit

module ecats.exact-completion.characterisation where

open import ecats.basic-defs.ecat-def&not
--open import ecats.basic-defs.isomorphism
open import ecats.basic-defs.exact-ecat
open import ecats.basic-props.exact-ecat
open import ecats.finite-limits.defs.collective
open import ecats.functors.defs.efunctor-d&n
open import ecats.functors.defs.natural-transformation
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
    ex𝔻 : is-exact 𝔻
    ex𝔻 = D.cat-ex
    ex𝔼 : is-exact 𝔼
    ex𝔼 = E.cat-ex
    -- the extension of E along D
    module E↑ where
      open D.emb-unv ex𝔼 E.emb-lcov public
      open efunctor-aux fctr public
      open is-exact-functor ex public
    -- the extension of D along E
    module D↑ where
      open E.emb-unv ex𝔻 D.emb-lcov public
      open efunctor-aux fctr public
      open is-exact-functor ex public

    D↑○E↑-ex : is-exact-functor (D↑.fctr ○ E↑.fctr)
    D↑○E↑-ex = exact-cmp E↑.ex D↑.ex
    E↑○D↑-ex : is-exact-functor (E↑.fctr ○ D↑.fctr)
    E↑○D↑-ex = exact-cmp D↑.ex E↑.ex

    trdom : (D↑.fctr ○ E↑.fctr) ○  D ≅ₐ IdF ○ D
    trdom = natiso-vcmp
      (≅ₐsym (○lid {F = D}))
      (natiso-vcmp D↑.tr
                   (natiso-vcmp (natiso-hcmp (≅ₐrefl {F = D↑.fctr})
                                             E↑.tr)
                                (≅ₐsym (○ass {F = D} {E↑.fctr} {H = D↑.fctr}))
                   ))
    trcod : (E↑.fctr ○ D↑.fctr) ○ E ≅ₐ IdF ○ E
    trcod = natiso-vcmp
      (≅ₐsym (○lid {F = E}))
      (natiso-vcmp E↑.tr
                   (natiso-vcmp (natiso-hcmp (≅ₐrefl {F = E↑.fctr})
                                             D↑.tr)
                                (≅ₐsym (○ass {F = E} {D↑.fctr} {E↑.fctr}))
                   ))

  eqv↑ : is-adj-equivalence-pair D↑.fctr E↑.fctr
  eqv↑ = record
    { ι1 = ι1
    ; ι2 = ι2
    ; trid₁ = λ {X} → {!!}
    ; trid₂ = {!!}
    }
    where ι1 : D↑.fctr ○ E↑.fctr ≅ₐ IdF
          ι1 = D.je D.cat-ex D↑○E↑-ex (IdF-is-exact {𝔻}) trdom
          ι2 : E↑.fctr ○ D↑.fctr ≅ₐ IdF
          ι2 = E.je ex𝔼 E↑○D↑-ex (IdF-is-exact {𝔼}) trcod
          module ι1 = natural-iso ι1
          module ι2 = natural-iso ι2

-- end exwlex-completion-is-unique


module exacompl-is-proj-cover {ℂ : ecategory}(fwlℂ : has-fin-weak-limits ℂ)
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
    emb-lcov : is-left-covering emb
    emb-lcov = emb.emb-lcov
    module Exℂ where
      open ecategory Ex ℂ [ fwlℂ ] public
      --open iso-defs Ex ℂ [ fwlℂ ] public
      --open epis&monos-defs Ex ℂ [ fwlℂ ] public
      --open epis&monos-props Ex ℂ [ fwlℂ ] public
      --open image-fact-defs Ex ℂ [ fwlℂ ] public
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
      module source = CVex.emb-unv ex𝔼 emb-lcov
      --renaming (ex to ex2; tr to tr2) public
      fctr : efunctor Ex ℂ [ fwlℂ ] 𝔼
      fctr = source.fctr
      ex : is-exact-functor fctr
      ex = source.ex
      tr : fctr ○ CVex ℂ [ fwlℂ ] ≅ₐ emb
      tr = source.tr
      open efunctor-aux fctr public
      open is-exact-functor ex public
    emb↑ : efunctor Ex ℂ [ fwlℂ ] 𝔼
    emb↑ = emb↑.fctr
    
    -- the canonical extension 𝔼 → Exℂ of CVex along emb
    module CVex↑ where
      open emb.emb-unv CVex.cat-ex CVex.emb-lcov renaming (ex to ex2; tr to tr2) public
      ex : is-exact-functor fctr
      ex = ex2
      tr : fctr ○ emb ≅ₐ CVex ℂ [ fwlℂ ]
      tr = tr2
      open efunctor-aux fctr public
      open is-exact-functor ex public

{-
    module emb↑○CVex↑ where
      fctr : efunctor 𝔼 𝔼
      fctr = emb↑.fctr ○ CVex↑.fctr
      open efunctor-aux fctr public
      ex : is-exact-functor fctr
      ex = {!!} --exact-cmp CVex↑.ex emb↑.ex
      open is-exact-functor ex public
    module CVex↑○emb↑ where
      fctr : efunctor Ex ℂ [ fwlℂ ] Ex ℂ [ fwlℂ ]
      fctr = CVex↑.fctr ○ emb↑.fctr
      open efunctor-aux fctr public
      ex : is-exact-functor fctr
      ex = {!!} --exact-cmp emb↑.ex CVex↑.ex
      open is-exact-functor ex public
-}

{-
    {-emb↑○CVex↑-trm : preserves-terminal emb↑○CVex↑.fctr
    --(_○_ {𝔻 = Ex ℂ [ fwlℂ ]} emb↑.fctr CVex↑.fctr)
    emb↑○CVex↑-trm = pres-term-cmp CVex↑.prestrm emb↑.prestrm 
    emb↑○CVex↑-fl : preserves-fin-limits (emb↑.fctr ○ CVex↑.fctr)
    emb↑○CVex↑-fl = {!!} --pres-fl-cmp CVex↑.presfl emb↑.presfl-}

    emb↑○CVex↑-ex : is-exact-functor (emb↑.fctr ○ CVex↑.fctr)
    emb↑○CVex↑-ex = exact-cmp CVex↑.ex emb↑.ex

    CVex↑○emb↑-ex : is-exact-functor (CVex↑.fctr ○ emb↑.fctr)
    CVex↑○emb↑-ex = exact-cmp emb↑.ex CVex↑.ex
    
    trcod-aux : emb↑.fctr ○ CVex↑.fctr ○ emb ≅ₐ IdF ○ emb
    trcod-aux = natiso-vcmp
      (natiso-vcmp (≅ₐsym (○lid {F = emb}))
                   emb↑.tr)
      (natiso-hcmp (≅ₐrefl {F = emb↑.fctr})
                    CVex↑.tr)
      -- {!!} (≅ₐsym (○ass {F = emb} {CVex↑.fctr}))

    trcod-aux2 : emb↑ ○ CVex↑.fctr ○ emb ≅ₐ (emb↑ ○ CVex↑.fctr) ○ emb
    trcod-aux2 = ○ass

    trcod : (emb↑.fctr ○ CVex↑.fctr) ○ emb ≅ₐ IdF ○ emb
    trcod = natiso-vcmp trcod-aux {!!} --(≅ₐsym trcod-aux2)

{-
      (≅ₐsym (○lid {F = emb}))
      (natiso-vcmp emb↑.tr
                   (natiso-vcmp (natiso-hcmp (≅ₐrefl {F = emb↑.fctr})
                                             CVex↑.tr)
                                {!≅ₐsym (○ass {ℂ} {𝔼} {𝔼 = Ex ℂ [ fwlℂ ]} {𝔼} {F = emb} {CVex↑.fctr} {emb↑.fctr})!}))
-}

    trdom : (CVex↑.fctr ○ emb↑.fctr) ○  CVex ℂ [ fwlℂ ] ≅ₐ IdF ○ CVex ℂ [ fwlℂ ]
    trdom = natiso-vcmp
      (≅ₐsym (○lid {F = CVex ℂ [ fwlℂ ]}))
      (natiso-vcmp CVex↑.tr
                   (natiso-vcmp (natiso-hcmp (≅ₐrefl {F = CVex↑.fctr})
                                             emb↑.tr)
                                (≅ₐsym {!!}) --(≅ₐsym (○ass {F = CVex ℂ [ fwlℂ ]} {H = CVex↑.fctr}))
                   ))

{-
natiso-vcmp
      (natiso-vcmp (≅ₐsym (○lid {F = CVex ℂ [ fwlℂ ]}))
                   (natiso-vcmp CVex↑.tr
                                (natiso-hcmp (≅ₐrefl {F = CVex↑.fctr})
                                             emb↑.tr)) )
      (≅ₐsym (○ass {F = CVex ℂ [ fwlℂ ]} {emb↑.fctr} {CVex↑.fctr}))
-------
natiso-vcmp
      (natiso-vcmp (≅ₐsym (○lid {F = CVex ℂ [ fwlℂ ]}))
                   CVex↑.tr )
      natiso-vcmp (natiso-hcmp (≅ₐrefl {F = CVex↑.fctr})
                               emb↑.tr)
                  (≅ₐsym (○ass {F = CVex ℂ [ fwlℂ ]} {emb↑.fctr} {CVex↑.fctr}))
-}

{-
(natiso-vcmp (natiso-hcmp 
                                ?)
                   ?)
-}

-}

  emb≡CVex : is-adj-equivalence-pair emb↑.fctr CVex↑.fctr
  emb≡CVex = eqv↑
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
      
  -- emb is naturally isomorphic to a projective cover, so a projective cover
  ispjc : is-projective-cover emb
  ispjc = emb↑○CVex.pjc.iso-pjc emb↑.tr

-- end exacompl-is-proj-cover
