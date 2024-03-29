
{-# OPTIONS --without-K #-}

module ecats.finite-limits.defs.collective where


open import ecats.basic-defs.ecat-def&not

open import ecats.finite-limits.defs.weak-terminal public
open import ecats.finite-limits.defs.terminal public
open import ecats.finite-limits.defs.terminal-is-weak public

open import ecats.finite-limits.defs.bin-weak-product public
open import ecats.finite-limits.defs.bin-product public
open import ecats.finite-limits.defs.bin-product-is-weak public

open import ecats.finite-limits.defs.weak-equaliser public
open import ecats.finite-limits.defs.equaliser public
open import ecats.finite-limits.defs.equaliser-is-weak public

open import ecats.finite-limits.defs.weak-pullback public
open import ecats.finite-limits.defs.pullback public
open import ecats.finite-limits.defs.pullback-is-weak public

open import ecats.finite-limits.defs.weak-Wlimit public

open import ecats.finite-limits.defs.weak-bow public
open import ecats.finite-limits.defs.bow public
open import ecats.finite-limits.defs.bow-is-weak public


record has-fin-products (ℂ : ecategory) : Set₁ where
  constructor !and×
  field
    hastrm : has-terminal ℂ
    hasprd : has-bin-products ℂ



record has-conn-weak-limits (ℂ : ecategory) : Set₁ where
  field
    hasweql : has-weak-equalisers ℂ
    haswpb : has-weak-pullbacks ℂ
    haswbw : has-weak-bows ℂ
    haswW : has-weak-Wlimits ℂ


record has-fin-weak-limits (ℂ : ecategory) : Set₁ where
  field
    haswtrm : has-weak-terminal ℂ
    haswprd : has-bin-weak-products ℂ
    hasweql : has-weak-equalisers ℂ
    haswpb : has-weak-pullbacks ℂ
    haswbw : has-weak-bows ℂ



record is-quasi-cartesian (ℂ : ecategory) : Set₁ where
  field
    hastrm : has-terminal ℂ
    hasprd : has-bin-products ℂ
    hasweql : has-weak-equalisers ℂ
    haswpb : has-weak-pullbacks ℂ
    haswbw : has-weak-bows ℂ


record has-conn-limits (ℂ : ecategory) : Set₁ where
  field
    haseql : has-equalisers ℂ
    haspb : has-pullbacks ℂ
    hasbw : has-bows ℂ


record has-fin-limits (ℂ : ecategory) : Set₁ where
  field
    hastrm : has-terminal ℂ
    hasprd : has-bin-products ℂ
    haseql : has-equalisers ℂ
    haspb : has-pullbacks ℂ
    hasbw : has-bows ℂ


has-flim→qcart : {ℂ : ecategory} → has-fin-limits ℂ → is-quasi-cartesian ℂ
has-flim→qcart {ℂ} hasfl = record
  { hastrm = hastrm
  ; hasprd = hasprd
  ; hasweql = has-eql⇒has-weql haseql
  ; haswpb = has-pb⇒has-wpb haspb
  ; haswbw = has-bw⇒has-wbw hasbw
  }
  where open has-fin-limits hasfl
        
qcart→has-fwlim : {ℂ : ecategory} → is-quasi-cartesian ℂ → has-fin-weak-limits ℂ
qcart→has-fwlim {ℂ} cart = record
  { haswtrm = has-trm⇒has-wtrm hastrm
  ; haswprd = has-prd⇒has-wprd hasprd
  ; hasweql = hasweql
  ; haswpb = haswpb
  ; haswbw = haswbw
  }
  where open is-quasi-cartesian cart

has-flim→has-fwlim : {ℂ : ecategory} → has-fin-limits ℂ → has-fin-weak-limits ℂ
has-flim→has-fwlim hasfl = record
  { haswtrm = has-trm⇒has-wtrm hastrm
  ; haswprd = has-prd⇒has-wprd hasprd
  ; hasweql = has-eql⇒has-weql haseql
  ; haswpb = has-pb⇒has-wpb haspb
  ; haswbw = has-bw⇒has-wbw hasbw
  }
  where open has-fin-limits hasfl
