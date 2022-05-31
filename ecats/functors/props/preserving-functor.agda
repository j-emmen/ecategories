
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
                     → preserves-terminal (_○_ {𝔻 = ℂ} G F)
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


pres-eql-cmp : {𝔹 ℂ 𝔻 : ecategory}{F : efunctor 𝔹 ℂ}{G : efunctor ℂ 𝔻}
                 → preserves-equalisers F → preserves-equalisers G
                   → preserves-equalisers (G ○ F)
pres-eql-cmp {𝔹} {ℂ} {𝔻} {F = F} {G} Fpreseql Gpreseql = record
  { pres-eql-pf = λ {_} {_} {_} {_} {_} {e} {pfeq} iseql
                    → 𝔻.pfeq-irr (Geqlpf (Feqlpf iseql)) (G○F.∘∘ pfeq)
  }
  where open preserves-equalisers Fpreseql renaming (pres-eql-pf to Feqlpf)
        open preserves-equalisers Gpreseql renaming (pres-eql-pf to Geqlpf)
        module 𝔻 = equaliser-props 𝔻
        module F = efunctor-aux F
        module G = efunctor-aux G
        module G○F = efunctor-aux (G ○ F)


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
  ; preseql = pres-eql-cmp Ffl.preseql Gfl.preseql
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


IdF-pres-fin-limits : {ℂ : ecategory} → preserves-fin-limits (IdF {ℂ})
IdF-pres-fin-limits {ℂ} = record
  { prestrm = record { pres-!-pf = λ istrm → istrm }
  ; presprd = record { pres-×-pf = λ isprd → isprd }
  ; preseql = record { pres-eql-pf = λ {_} {_} {_} {_} {_} {_} {pfeq} iseql
                                   → pfeq-irr iseql (Id.∘∘ pfeq) }
  ; prespb = record { pres-ispbof-pf = λ {_} {_} {_} {_} {_} {sq/} ispbof
                      → pullback-defs.mkis-pb-of (×/sqpf-irr (ispb ispbof) (Id.∘∘ (sq-pf sq/) )) }
  }
  where open equaliser-props ℂ
        open pullback-props ℂ
        module Id = efunctor-aux (IdF {ℂ})
        open comm-shapes.square/cosp {ℂ}
        open pullback-defs.is-pullback-of {ℂ}



IdF-pres-reg-epis : {ℂ : ecategory} → preserves-regular-epis (IdF {ℂ})
IdF-pres-reg-epis {ℂ} = record
  { pres-repi-pf = λ repi → repi
  }


IdF-is-exact : {ℂ : ecategory} → is-exact-functor (IdF {ℂ})
IdF-is-exact {ℂ} = record
  { presfl = IdF-pres-fin-limits {ℂ}
  ; presrepi = IdF-pres-reg-epis {ℂ}
  }
