
{-# OPTIONS --without-K #-}

module ecats.exact-completion.CVconstr-is-excompl.finite-limits.fin-limits where

open import ecats.basic-defs.ecat-def&not
open import ecats.finite-limits.defs.collective
open import ecats.finite-limits.props.relations-among-limits using (has-eql+pb⇒has-bw)
open import ecats.exact-completion.CVconstruction
open import ecats.exact-completion.CVconstr-is-excompl.finite-limits.terminal using (exact-compl-has-terminal
                                                                ; exact-compl-qcart-has-terminal) public
open import ecats.exact-completion.CVconstr-is-excompl.finite-limits.bin-product using (exact-compl-has-bin-products
                                                                   ; exact-compl-qcart-has-bin-products) public
open import ecats.exact-completion.CVconstr-is-excompl.finite-limits.equaliser using (exact-compl-has-equalisers
                                                                 ; exact-compl-qcart-has-equalisers) public
open import ecats.exact-completion.CVconstr-is-excompl.finite-limits.pullback using (exact-compl-has-pullbacks
                                                                ; exact-compl-qcart-has-pullbacks) public


--------------------------------------
-- Exact completion has finite limits
--------------------------------------


exact-compl-has-fin-products : {ℂ : ecategory} (hasfwl : has-fin-weak-limits ℂ) → has-fin-products Ex ℂ [ hasfwl ]
exact-compl-has-fin-products hasfwl = !and× (exact-compl-has-terminal hasfwl) (exact-compl-has-bin-products hasfwl)

exact-compl-qcart-has-fin-products : {ℂ : ecategory} (qcart : is-quasi-cartesian ℂ) → has-fin-products Ex ℂ qc[ qcart ]
exact-compl-qcart-has-fin-products qcart = exact-compl-has-fin-products (qcart→has-fwlim qcart)


exact-compl-has-bows : {ℂ : ecategory} (hasfwl : has-fin-weak-limits ℂ) → has-bows Ex ℂ [ hasfwl ]
exact-compl-has-bows hasfwl = has-eql+pb⇒has-bw (exact-compl-has-equalisers hasfwl) (exact-compl-has-pullbacks hasfwl)

exact-compl-qcart-has-bows : {ℂ : ecategory} (qcart : is-quasi-cartesian ℂ) → has-bows Ex ℂ qc[ qcart ]
exact-compl-qcart-has-bows qcart = exact-compl-has-bows (qcart→has-fwlim qcart)
                     

exact-compl-has-fin-limits : {ℂ : ecategory} (hasfwl : has-fin-weak-limits ℂ) → has-fin-limits Ex ℂ [ hasfwl ]
exact-compl-has-fin-limits hasfwl = record { hastrm = hastrm
                                     ; hasprd = hasprd
                                     ; haseql = exact-compl-has-equalisers hasfwl
                                     ; haspb = exact-compl-has-pullbacks hasfwl
                                     ; hasbw = exact-compl-has-bows hasfwl
                                     }
                                     where open has-fin-products (exact-compl-has-fin-products hasfwl)

exact-compl-qcart-has-fin-limits : {ℂ : ecategory} (qcart : is-quasi-cartesian ℂ) → has-fin-limits Ex ℂ qc[ qcart ]
exact-compl-qcart-has-fin-limits qcart = exact-compl-has-fin-limits (qcart→has-fwlim qcart)
