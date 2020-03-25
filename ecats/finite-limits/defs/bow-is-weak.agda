 
-- disable the K axiom:

{-# OPTIONS --without-K #-}

-- Agda version 2.5.4.1

module ecats.finite-limits.defs.bow-is-weak where

open import ecats.basic-defs.ecat-def&not
open import ecats.basic-defs.commut-shapes
open import ecats.finite-limits.defs.weak-bow
open import ecats.finite-limits.defs.bow



module bow→weak-bow (ℂ : ecategory) where
  open ecategory ℂ
  open comm-shapes ℂ
  open weak-bow-defs ℂ
  open bow-defs ℂ
  open span/


  is-bw→is-wbw : {DL DR : Obj} {sp₁ sp₂ : span/ DL DR} {bow : span/ (O12 sp₁) (O12 sp₂)}
                    {×//sqpf₁ : a1 sp₁ ∘ a1 bow ~ a1 sp₂ ∘ a2 bow} {×//sqpf₂ : a2 sp₁ ∘ a1 bow ~ a2 sp₂ ∘ a2 bow}
                      → is-bow ×//sqpf₁ ×//sqpf₂ → is-wbow ×//sqpf₁ ×//sqpf₂
  is-bw→is-wbw is-bw = record
    { ⟨_,_⟩[_,_] = ⟨_,_⟩[_,_]
    ; tr₁ = tr₁
    ; tr₂ = tr₂
    }
    where open is-bow is-bw


  bw-of→wbw-of : {DL DR : Obj} {sp₁ sp₂ : span/ DL DR} → bow-of sp₁ sp₂ → wbow-of sp₁ sp₂
  bw-of→wbw-of bw-of = record
    { is-wbw = is-bw→is-wbw is-bw
    }
    where open bow-of bw-of

-- end bow→weak-bow



has-bw⇒has-wbw : {ℂ : ecategory} → has-bows ℂ → has-weak-bows ℂ
has-bw⇒has-wbw {ℂ} has-bw = record
  { wbw-of = λ sp₁ sp₂ → bw-of→wbw-of (bw-of sp₁ sp₂)
  }
  where open bow-defs ℂ
        open has-bows has-bw
        open bow→weak-bow ℂ
