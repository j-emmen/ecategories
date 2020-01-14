
-- disable the K axiom:

{-# OPTIONS --without-K #-}

-- Agda version 2.5.4.1

module ecats.basic-defs.kernel-pair where

open import ecats.basic-defs.ecat-def&not
open import ecats.basic-defs.commut-shapes
open import ecats.basic-defs.isomorphism
open import ecats.basic-defs.epi&mono
open import ecats.finite-limits.d&n-weak-pullback
open import ecats.finite-limits.d&n-pullback
open import ecats.finite-limits.defs.weak-bow
open import ecats.finite-limits.defs.bow


-- Weak kernel pairs

module weak-kernel-pairs-defs (ℂ : ecategory) where
  open ecategory-aux ℂ
  --open epis&monos-defs ℂ
  open comm-shapes ℂ
  open wpullback-squares ℂ
  open weak-bow-defs ℂ
  private
    module sp/ = span/
    module w×//of = wbow-of


  record is-wkernel-pair-of {K A B : Obj} (wkp₁ wkp₂ : || Hom K A ||) (f : || Hom A B ||) : Set₁ where
    -- constructor mkiswkpof
    field
      {sqpf} : f ∘ wkp₁  ~ f ∘ wkp₂
      iswpb : is-wpb-square (mksq (mksq/ sqpf))
    open wpullback-sq-not (mkwpb-sq iswpb) public


  record is-wkernel-pair {K A : Obj} (wkp₁ wkp₂ : || Hom K A ||) : Set₁ where
    -- constructor mkwkp-c
    field
      {Ob} : Obj
      {ar} : || Hom A Ob ||
      iswkpof : is-wkernel-pair-of wkp₁ wkp₂ ar
    open is-wkernel-pair-of iswkpof public
      

  mkwkp : {K A B : Obj} {ar : || Hom A B ||} {wkp₁ wkp₂ : || Hom K A ||} {sqpf : ar ∘ wkp₁  ~ ar ∘ wkp₂}
            → is-wpb-square (mksq (mksq/ sqpf)) → is-wkernel-pair wkp₁ wkp₂
  mkwkp {B = B} {ar} {sqpf = sqpf} iswpb = record
    { Ob = B
    ; ar = ar
    ; iswkpof = record { sqpf = sqpf
                       ; iswpb = iswpb
                       }
    }


  record is-wkernel-pair-of-sp/ {O1 O2 K : Obj} (sp/ : span/ O1 O2)
                                (wkp₁ wkp₂ : || Hom K (sp/.O12 sp/) ||) : Set₁
                                where
    -- constructor mkiswkpof
    open span/ sp/
    field
      {sqpf₁} : a1 ∘ wkp₁  ~ a1 ∘ wkp₂
      {sqpf₂} : a2 ∘ wkp₁  ~ a2 ∘ wkp₂
      iswbw : is-wbow sqpf₁ sqpf₂
    open is-wbow iswbw public


  record is-wkernel-pair-sp {A K : Obj} (wkp₁ wkp₂ : || Hom K A ||) : Set₁ where
    -- constructor mkwkp-c
    field
      {O1} {O2} : Obj
      {a1} : || Hom A O1 ||
      {a2} : || Hom A O2 ||
      iswkpofsp/ : is-wkernel-pair-of-sp/ (mkspan/ a1 a2) wkp₁ wkp₂
    open is-wkernel-pair-of-sp/ iswkpofsp/ public
      

  mkwkpsp : {O1 O2 A K : Obj} {sp/ : span/ O1 O2} (wbwof : wbow-of sp/ sp/)
                → is-wkernel-pair-sp (w×//of.wπ//₁ wbwof) (w×//of.wπ//₂ wbwof)
  --{wkp₁ wkp₂ : || Hom K (sp/.O12 sp/) ||} {sqpf : ar ∘ wkp₁  ~ ar ∘ wkp₂}
  mkwkpsp {sp/ = sp/} wbwof = record
    { a1 = a1
    ; a2 = a2
    ; iswkpofsp/ = record
                 { iswbw = w×//of.is-wbw wbwof
                 }
    }
    where open span/ sp/



  module has-wpb→has-wkerpair (haswpb : has-weak-pullbacks ℂ) where
    open has-weak-pullbacks haswpb using (wpb-of)
        
    wkp-of :  {A B : Obj} (f : || Hom A B ||) → wpullback-of f f
    wkp-of f =  wpb-of f f

    private
      module wkp {A B : Obj} (f : || Hom A B ||) = wpullback-of-not (wkp-of f)

    wπ/iswkpof : {A B : Obj} (f : || Hom A B ||) → is-wkernel-pair-of (wkp.wπ/₁ f) (wkp.wπ/₂ f) f
    wπ/iswkpof f = record
      { iswpb = wkp.w×/iswpbsq f }

    wπ/iswkp : {A B : Obj} (f : || Hom A B ||) → is-wkernel-pair (wkp.wπ/₁ f) (wkp.wπ/₂ f)
    wπ/iswkp f = record { iswkpof = wπ/iswkpof f }
  -- end cat-has-wpb→wkerpair-exist


  module has-wbw→has-wkerpairsp (haswbw : has-weak-bows ℂ) where
    open has-weak-bows haswbw using (wbw-of)
        
    wkpsp-of :  {O1 O2 : Obj} (sp/ : span/ O1 O2) → wbow-of sp/ sp/
    wkpsp-of sp/ =  wbw-of sp/ sp/

    private
      module wkpsp {O1 O2 : Obj} (sp/ : span/ O1 O2) = wbow-of (wkpsp-of sp/)

    wπ//iswkpof : {O1 O2 : Obj} (sp/ : span/ O1 O2)
                      → is-wkernel-pair-of-sp/ sp/ (wkpsp.wπ//₁ sp/) (wkpsp.wπ//₂ sp/)
    wπ//iswkpof sp/ = record { iswbw = wkpsp.is-wbw sp/ }

    wπ//iswkp : {O1 O2 : Obj} (sp/ : span/ O1 O2)
                    → is-wkernel-pair-sp (wkpsp.wπ//₁ sp/) (wkpsp.wπ//₂ sp/)
    wπ//iswkp sp/ = record { iswkpofsp/ = wπ//iswkpof sp/ }
  -- end cat-has-wbw→wkerpair-exist
  
-- end weak-kernel-pairs-defs



-- Kernel pairs

module kernel-pairs-defs (ℂ : ecategory) where
  open ecategory-aux ℂ
  open epis&monos-defs ℂ
  open comm-shapes ℂ
  open pullback-squares ℂ
  open bow-defs ℂ
  private
    module sp/ = span/
    module ×//of = bow-of


  record is-kernel-pair-of {K A B : Obj} (kp₁ kp₂ : || Hom K A ||) (f : || Hom A B ||) : Set₁ where
    -- constructor mkiskpof
    field
      {sqpf} : f ∘ kp₁  ~ f ∘ kp₂
      ispb : is-pb-square (mksq (mksq/ sqpf))
    open pullback-sq-not (mkpb-sq ispb) public


  record is-kernel-pair {K A : Obj} (kp₁ kp₂ : || Hom K A ||) : Set₁ where
    -- constructor mkkp-c
    field
      {Ob} : Obj
      {ar} : || Hom A Ob ||
      iskpof : is-kernel-pair-of kp₁ kp₂ ar
    open is-kernel-pair-of iskpof public
      

  mkkp : {K A B : Obj} {ar : || Hom A B ||} {kp₁ kp₂ : || Hom K A ||} {sqpf : ar ∘ kp₁  ~ ar ∘ kp₂}
            → is-pb-square (mksq (mksq/ sqpf)) → is-kernel-pair kp₁ kp₂
  mkkp {B = B} {ar} {sqpf = sqpf} ispb = record
    { Ob = B
    ; ar = ar
    ; iskpof = record { sqpf = sqpf
                      ; ispb = ispb
                      }
    }

  
  record is-exact-seq {R A Q : Obj} (r₁ r₂ : || Hom R A ||) (q : || Hom A Q ||) : Set₁ where
    field
      iscoeq : is-coeq r₁ r₂ q
    open is-coeq iscoeq public
    field
      iskerpair : is-pb-square (mksq (mksq/ eq))
    open pullback-sq-not (mkpb-sq iskerpair) public


  record is-kernel-pair-of-sp/ {O1 O2 K : Obj} (sp/ : span/ O1 O2)
                               (kp₁ kp₂ : || Hom K (sp/.O12 sp/) ||) : Set₁
                               where
    -- constructor mkiswkpof
    open span/ sp/
    field
      {sqpf₁} : a1 ∘ kp₁  ~ a1 ∘ kp₂
      {sqpf₂} : a2 ∘ kp₁  ~ a2 ∘ kp₂
      isbw : is-bow sqpf₁ sqpf₂
    open is-bow isbw public


  record is-kernel-pair-sp {A K : Obj} (kp₁ kp₂ : || Hom K A ||) : Set₁ where
    -- constructor mkkp-c
    field
      {O1} {O2} : Obj
      {a1} : || Hom A O1 ||
      {a2} : || Hom A O2 ||
      iskpofsp/ : is-kernel-pair-of-sp/ (mkspan/ a1 a2) kp₁ kp₂
    open is-kernel-pair-of-sp/ iskpofsp/ public
      

  mkkpsp : {O1 O2 A K : Obj} {sp/ : span/ O1 O2} (bwof : bow-of sp/ sp/)
                → is-kernel-pair-sp (×//of.π//₁ bwof) (×//of.π//₂ bwof)
  --{kp₁ kp₂ : || Hom K (sp/.O12 sp/) ||} {sqpf : ar ∘ kp₁  ~ ar ∘ kp₂}
  mkkpsp {sp/ = sp/} bwof = record
    { a1 = a1
    ; a2 = a2
    ; iskpofsp/ = record
                 { isbw = ×//of.is-bw bwof
                 }
    }
    where open span/ sp/



  module has-pb→has-kerpair (haspb : has-pullbacks ℂ) where
    open has-pullbacks haspb using (pb-of)
    
    kp-of :  {A B : Obj} (f : || Hom A B ||) → pullback-of f f
    kp-of f =  pb-of f f
    
    private
      module kp {A B : Obj} (f : || Hom A B ||) = pullback-of-not (kp-of f)

    π/iskpof : {A B : Obj} (f : || Hom A B ||) → is-kernel-pair-of (kp.π/₁ f) (kp.π/₂ f) f
    π/iskpof f = record { ispb = kp.×/ispbsq f }

    π/iskp : {A B : Obj} (f : || Hom A B ||) → is-kernel-pair (kp.π/₁ f) (kp.π/₂ f)
    π/iskp f = record { iskpof = π/iskpof f }
  -- end cat-has-pb→kerpair-exists


  module has-bw→has-kerpairsp (hasbw : has-bows ℂ) where
    open has-bows hasbw using (bw-of)

    kpsp-of : {O1 O2 : Obj} (sp/ : span/ O1 O2) → bow-of sp/ sp/
    kpsp-of sp/ = bw-of sp/ sp/
    private
      module kpsp/ {O1 O2 : Obj} (sp/ : span/ O1 O2) = bow-of (kpsp-of sp/)

    π//iskpof : {O1 O2 : Obj} (sp/ : span/ O1 O2)
                    → is-kernel-pair-of-sp/ sp/ (kpsp/.π//₁ sp/) (kpsp/.π//₂ sp/)
    π//iskpof sp/ = record { isbw = kpsp/.is-bw sp/ }

    π//iskp : {O1 O2 : Obj} (sp/ : span/ O1 O2) → is-kernel-pair-sp (kpsp/.π//₁ sp/) (kpsp/.π//₂ sp/)
    π//iskp sp/ = record { iskpofsp/ = π//iskpof sp/ }
  -- end cat-has-bw→kerpair-exist
  
-- end kernel-pairs-defs
