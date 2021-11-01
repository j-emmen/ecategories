
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
  where --module def = exact-compl-universal-def hasfwl
        module tr = exact-compl-universal-commut hasfwl
        module ex = exact-compl-universal-is-exact hasfwl
        module uq = exact-compl-universal-uniq hasfwl

{-
module check {ℂ : ecategory}(fwlℂ : has-fin-weak-limits ℂ)
             (flℂ : has-fin-limits ℂ)
             --{PC : efunctor ℂ 𝔼}(pjcPC : is-projective-cover PC)
             {𝔻 : ecategory}(ex𝔻 : is-exact 𝔻)
             {F : efunctor ℂ 𝔻}(lcovF : is-left-covering F)
             where
  --module CVex = is-exwlex-completion (CVconstr-is-excompl hasfwl)
  --module ℂ where
  ℂfwl : has-fin-weak-limits ℂ
  ℂfwl = fwlℂ --has-flim→has-fwlim flℂ
  --proj-cov-has-wlim pjcPC fl𝔼
  module unv {𝔻 : ecategory}(ex𝔻 : is-exact 𝔻)
             {F : efunctor ℂ 𝔻}(lcovF : is-left-covering F)
             = exwlex-universal-prop (CVexcmpl-is-init-lcov-ex fwlℂ ex𝔻 lcovF)
  fctr : efunctor Ex ℂ [ fwlℂ ] 𝔻
  fctr = unv.fctr ex𝔻 lcovF
  --CVcheck : CVex ℂ [ ℂfwl ] ≅ₐ CVex ℂ [ fwlℂ ]
  --CVcheck = ≅ₐrefl
  fctr-check : fctr ≅ₐ (exact-compl-universal-def.↑ex fwlℂ ex𝔻 lcovF)
  fctr-check = ≅ₐrefl
  tr : _○_ {_} {Ex ℂ [ fwlℂ ]} {_} fctr CVex ℂ [ fwlℂ ] ≅ₐ F
  tr = unv.tr ex𝔻 lcovF

-- with ℂfwl = has-flim→has-fwlim flℂ it takes too long...
-}


-- module exact-compl-universal-prop {ℂ : ecategory} (hasfwl : has-fin-weak-limits ℂ)
--                                   {𝔼 : ecategory} (ex𝔼 : is-exact 𝔼)
--                                   {F : efunctor ℂ 𝔼} (lcovF : is-left-covering F)
--                                   where
--   ↑ex : efunctor Ex ℂ [ hasfwl ] 𝔼
--   ↑ex = ↑exd ex𝔼 lcovF
--       where open exact-compl-universal-def hasfwl renaming (↑ex to ↑exd)

--   open exwlex-universal-prop-data (CVex ℂ [ hasfwl ]) F
--   --hasfwl (exact-compl-is-exact hasfwl) (excmpl-embed-is-left-covering hasfwl)
-- {-
--   ↑ex-ex+tr : def-props-of-fnct ↑ex
--   ↑ex-ex+tr = record
--     { ex = ↑ex-is-exact ex𝔼 lcovF
--     ; tr = ↑ex-tr ex𝔼 lcovF
--     }
--     where open exact-compl-universal-commut hasfwl
--           open exact-compl-universal-is-exact hasfwl
-- -}

--   tr : natural-iso (↑ex ○ CVex ℂ [ hasfwl ]) F
--   tr = ↑ex-tr ex𝔼 lcovF
--      where open exact-compl-universal-commut hasfwl --renaming (↑ex-tr to ↑ex-trd)
--   ex : is-exact-functor ↑ex
--   ex = ↑ex-is-exact ex𝔼 lcovF
--      where open exact-compl-universal-is-exact hasfwl --renaming (↑ex-is-exact to ↑ex-is-exactd)
--   uq : {G : efunctor Ex ℂ [ hasfwl ] 𝔼}(exG : is-exact-functor G)(trG : G ○ CVex ℂ [ hasfwl ] ≅ₐ F)
--          → G ≅ₐ ↑ex
--   uq = ↑ex-uq ex𝔼 lcovF
--      where open exact-compl-universal-uniq hasfwl --renaming (↑ex-is-exact to ↑ex-is-exactd)
-- {-
--   ↑ex-uqst : is-unique-ex+tr ↑ex
--   --{G : efunctor Ex ℂ [ hasfwl ] 𝔼}(propsG : def-props-of-fnct F G)
--   --(exG : is-exact-functor G)
-- --           (Gtr : natural-iso (G ○ CVex ℂ [ hasfwl ]) F)
--              -- → natural-iso G ↑ex
--   ↑ex-uqst = record
--     { ex+tr = ↑ex-ex+tr
--     ; isuq = λ propsE → ↑ex-uqd ex𝔼 lcovF (ex propsE) (tr propsE)
--     } --↑ex-uqd ex𝔼 lcovF ex tr
--     where open exact-compl-universal-uniq hasfwl renaming (↑ex-uq to ↑ex-uqd)
--           open def-props-of-fnct
-- -}
--   {-module ↑ex where
--     open efunctor-aux ↑ex public
--     module tr = natural-iso ↑ex-tr
--     module ex = is-exact-functor ↑ex-is-exact 
--     module uq {G : efunctor Ex ℂ [ hasfwl ] 𝔼} (exG : is-exact-functor G)
--               (Gtr : natural-iso (G ○ CVex ℂ [ hasfwl ]) F)
--                 = natural-iso (↑ex-uq exG Gtr)-}
-- -- end exact-compl-universal-prop

-- {-
-- CVexcmpl-is-init-lcov-ex : {ℂ : ecategory}(hasfwl : has-fin-weak-limits ℂ)
--   → exwlex-universal-prop hasfwl
--                            (exact-compl-is-exact hasfwl)
--                            (pjcov-of-reg-is-lcov (exact-compl-is-regular hasfwl)
--                                                  (excmpl-embed-is-projective-cover hasfwl))
-- CVexcmpl-is-init-lcov-ex hasfwl = record
--   { univ = λ ex𝔻 lcovG → record
--          { fnct = ↑ex ex𝔻 lcovG
--          ; prop = ↑ex-uqst ex𝔻 lcovG
--          }
--   }
--   where open exact-compl-universal-prop hasfwl
-- -}
