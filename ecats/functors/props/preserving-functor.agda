
{-# OPTIONS --without-K #-}

module ecats.functors.props.preserving-functor where

open import ecats.basic-defs.ecat-def&not
open import ecats.basic-defs.commut-shapes
open import ecats.basic-defs.all-arrows
open import ecats.basic-props.epi&mono
open import ecats.finite-limits.all
open import ecats.functors.defs.efunctor-d&n
open import ecats.functors.defs.basic-defs
open import ecats.functors.defs.preserving-functor



pres-term-cmp : {𝔹 ℂ 𝔻 : ecategory}{F : efunctor 𝔹 ℂ}{G : efunctor ℂ 𝔻}
                   → preserves-terminal F → preserves-terminal G
                     → preserves-terminal (G ○ F)
pres-term-cmp Fprestrm Gprestrm = record
  { pres-!-pf = λ {X} Xistrm → G!pf (F!pf Xistrm)
  }
  where open preserves-terminal Fprestrm renaming (pres-!-pf to F!pf)
        open preserves-terminal Gprestrm renaming (pres-!-pf to G!pf)


pres-bprd-cmp : {𝔹 ℂ 𝔻 : ecategory}{F : efunctor 𝔹 ℂ}{G : efunctor ℂ 𝔻}
                   → preserves-bin-products F → preserves-bin-products G
                     → preserves-bin-products (G ○ F)
pres-bprd-cmp Fpresbprd Gpresbprd = record
  { pres-×-pf = λ {X} Xisbprd → G×pf (F×pf Xisbprd)
  }
  where open preserves-bin-products Fpresbprd renaming (pres-×-pf to F×pf)
        open preserves-bin-products Gpresbprd renaming (pres-×-pf to G×pf)


pres-pb-cmp : {𝔹 ℂ 𝔻 : ecategory}{F : efunctor 𝔹 ℂ}{G : efunctor ℂ 𝔻}
                 → preserves-pullbacks F → preserves-pullbacks G
                   → preserves-pullbacks (G ○ F)
pres-pb-cmp {𝔹} {ℂ} {𝔻} {F = F} {G} Fprespb Gprespb = record
  { pres-ispbof-pf = λ {_} {_} {_} {_} {_} {sq/} ispbof
                       → 𝔻.×/sqpf-irr-of (Gpbpf (Fpbpf ispbof))
                                           (𝔻sq/.sq-pf (G○F.sq/ sq/))
  }
  where open preserves-pullbacks Fprespb renaming (pres-ispbof-pf to Fpbpf)
        open preserves-pullbacks Gprespb renaming (pres-ispbof-pf to Gpbpf)
        module 𝔻sq/ = comm-shapes.square/cosp {𝔻}
        module 𝔻 = pullback-props 𝔻
        module G○F = efunctor-aux (G ○ F)


pres-fl-cmp : {𝔹 ℂ 𝔻 : ecategory}{F : efunctor 𝔹 ℂ}{G : efunctor ℂ 𝔻}
                 → preserves-fin-limits F → preserves-fin-limits G
                   → preserves-fin-limits (G ○ F)
pres-fl-cmp Fpresfl Gpresfl = record
  { prestrm = pres-term-cmp Ffl.prestrm Gfl.prestrm 
  ; presprd = pres-bprd-cmp Ffl.presprd Gfl.presprd
  ; prespb = pres-pb-cmp Ffl.prespb Gfl.prespb
  }
  where module Ffl = preserves-fin-limits Fpresfl
        module Gfl = preserves-fin-limits Gpresfl




pres-repi-cmp : {𝔹 ℂ 𝔻 : ecategory}{F : efunctor 𝔹 ℂ}{G : efunctor ℂ 𝔻}
                   → preserves-regular-epis F → preserves-regular-epis G
                     → preserves-regular-epis (G ○ F)
pres-repi-cmp Fpresrepi Gpresrepi = record
  { pres-repi-pf = λ isrepi → Grepipf (Frepipf isrepi)
  }
  where open preserves-regular-epis Fpresrepi renaming (pres-repi-pf to Frepipf)
        open preserves-regular-epis Gpresrepi renaming (pres-repi-pf to Grepipf)


pres-jm/-cmp : {𝔹 ℂ 𝔻 : ecategory}{F : efunctor 𝔹 ℂ}{G : efunctor ℂ 𝔻}
                   → preserves-jointly-monic/ F → preserves-jointly-monic/ G
                     → preserves-jointly-monic/ (G ○ F)
pres-jm/-cmp Fpresjm/ Gpresjm/ = record
  { pres-jm/-pf = λ isjm → Gjm/pf (Fjm/pf isjm)
  }
  where open preserves-jointly-monic/ Fpresjm/ renaming (pres-jm/-pf to Fjm/pf)
        open preserves-jointly-monic/ Gpresjm/ renaming (pres-jm/-pf to Gjm/pf)



exact-cmp : {𝔹 ℂ 𝔻 : ecategory}{F : efunctor 𝔹 ℂ}{G : efunctor ℂ 𝔻}
               → is-exact-functor F → is-exact-functor G
                 → is-exact-functor (G ○ F)
exact-cmp Fex Gex = record
  { presfl = pres-fl-cmp Fex.presfl Gex.presfl
  ; presrepi = pres-repi-cmp Fex.presrepi Gex.presrepi
  }
  where module Fex = is-exact-functor Fex
        module Gex = is-exact-functor Gex


