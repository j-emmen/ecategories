
{-# OPTIONS --without-K #-}

module ecats.finite-limits.defs.terminal-is-weak where

open import ecats.basic-defs.ecat-def&not
open import ecats.finite-limits.defs.weak-terminal
open import ecats.finite-limits.defs.terminal


module terminal→weak-terminal (ℂ : ecategory) where
  open ecategory-aux ℂ
  open wterminal-defs ℂ
  open terminal-defs ℂ


  is-trm⇒is-wtrm : {T : Obj} → is-terminal T → is-wterminal T
  is-trm⇒is-wtrm is-trm = mkiswtrm !
                         where open is-terminal is-trm

-- end terminal→weak-terminal


has-trm⇒has-wtrm : {ℂ : ecategory} → has-terminal ℂ → has-weak-terminal ℂ
has-trm⇒has-wtrm  {ℂ} has-trm = mkhas-trm (is-trm⇒is-wtrm istrm)
                               where open terminal-defs ℂ
                                     open has-terminal has-trm
                                     open terminal→weak-terminal ℂ
