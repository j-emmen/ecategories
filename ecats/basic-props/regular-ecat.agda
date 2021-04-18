
{-# OPTIONS --without-K #-}

module ecats.basic-props.regular-ecat where

open import ecats.basic-defs.ecat-def&not
open import ecats.basic-defs.arrows
open import ecats.finite-limits.all
open import ecats.basic-defs.regular-ecat
open import ecats.basic-props.isomorphism
open import ecats.basic-props.epi&mono
open import ecats.basic-props.image-fact
open import ecats.basic-defs.exact-ecat




module regular-cat-props {ℂ : ecategory} (isreg : is-regular ℂ) where
  open ecategory ℂ
  open arrows-defs ℂ
  open iso-props ℂ
  open iso-transports ℂ
  open terminal-defs ℂ
  open binary-products ℂ
  open pullback-squares ℂ
  open pullback-props ℂ
  open epi&mono-props-all ℂ
  open image-fact-props ℂ
  private
    module rℂ where
      open is-regular isreg public
      open has-pullbacks haspb using (pb-of) public
      open has-equalisers haseql using (eql-of) public
      open has-bin-products hasprd using (prd-of) public
      open has-pb→has-kerpair haspb public
      open epi&mono-pullbacks haspb public
    module rmfof = rℂ.rmf-of
    module sp/ = span/
    module sp = span
    module sq/ = square/cosp
    module sq = comm-square
    module ×of = product-of-not
    module pbof = pullback-of-not
    module pbsq = pb-square
    module ker {A B : Obj} (f : || Hom A B ||) = pullback-of-not (rℂ.pb-of f f)
    module eqr = eqrel-over



  -- covers are regular epis
  
  cover-is-regular : {A B : Obj} {c : || Hom A B ||} → is-cover c → is-regular-epi c
  cover-is-regular {c = c} iscov = iso-to-repi-is-repi-cod miso rmfc.tr rmfc.C-is-repi
                                 where module c = is-cover iscov
                                       module rmfc = rmfof c
                                       miso : is-iso rmfc.M
                                       miso = c.cov-pf rmfc.tr rmfc.M-is-monic

  repi-triang : {A B C : Obj} {f : || Hom A B ||} {f' : || Hom C B ||} {h : || Hom A C ||}
                   → f' ∘ h ~ f → is-regular-epi f → is-regular-epi f'
  repi-triang tr repi = cover-is-regular (cover-triang (mktriang tr) (repi-is-cover repi))

  -- strong epis are regular

  strong-epi-is-regular : {A B : Obj} {f : || Hom A B ||} → is-strong-epi f → is-regular-epi f
  strong-epi-is-regular fstr = cover-is-regular (strong-epi-is-cover fstr)


  -- is-regular-epi is ecat congruence

  regular-epi-is-congr : is-ecat-congr ℂ is-regular-epi
  regular-epi-is-congr = mkis-ecat-congr
    (mkis-hom-ext is-regular-epi λ pfeq frepi → strong-epi-is-regular (trnsp pfeq (repi-is-strong frepi)))
    (record { ∘c = λ grepi frepi → strong-epi-is-regular (∘c (repi-is-strong grepi) (repi-is-strong frepi)) })
    where open is-ecat-congr strepi-is-congr

  repi-cmp : {A B C : Obj} {f : || Hom A B ||} {g : || Hom B C ||} {h : || Hom A C ||}
                → is-regular-epi f → is-regular-epi g → g ∘ f ~ h → is-regular-epi h
  repi-cmp repif repig tr = trnsp tr (∘c repig repif)
                          where open is-ecat-congr regular-epi-is-congr


{-
  -- regular epis are iso-transportable
  
  repi-is-transportable : iso-transportable is-regular-epi
  repi-is-transportable = iso-transports.mkiso-transp
    regular-epi-is-congr
    λ f fiso → split-epi-is-repi (iso-is-split-epi fiso)

  module repi-trnsp = iso-transp is-regular-epi repi-is-transportable
-}


  module has-quot-of-ker-pair {A K : Obj} {kp₁ kp₂ : || Hom K A ||} (iskp : is-kernel-pair kp₁ kp₂) where
    open ecategory-aux-only ℂ
    private
      module kp = is-kernel-pair iskp
      module rmfkp = rmfof kp.ar
      module univ-pf {B : Obj} {f : || Hom A B ||} (pf : f ∘ kp₁ ~ f ∘ kp₂) where
        med-ar-pf : kp.ar ∘ rmfkp.C.rel₁ ~ kp.ar ∘ rmfkp.C.rel₂
        med-ar-pf = ∘e r (rmfkp.tr ˢ) ⊙ assˢ ⊙ ∘e rmfkp.C.eq r ⊙ ass ⊙ ∘e r rmfkp.tr
        med-ar : || Hom rmfkp.C.relOb K ||
        med-ar = kp.⟨ rmfkp.C.rel₁ , rmfkp.C.rel₂ ⟩[ med-ar-pf ]
        pfC : f ∘ rmfkp.C.rel₁ ~ f ∘ rmfkp.C.rel₂
        pfC = ~proof f ∘ rmfkp.C.rel₁    ~[ ∘e (kp.×/tr₁ med-ar-pf ˢ) r ] /
                      f ∘ kp₁ ∘ med-ar   ~[ ass ⊙ ∘e r pf ⊙ assˢ ] /
                      f ∘ kp₂ ∘ med-ar   ~[ ∘e (kp.×/tr₂ med-ar-pf) r ]∎
                      f ∘ rmfkp.C.rel₂ ∎
      -- end univ-pf
    -- end private
    coeq : coeq-of kp₁ kp₂
    coeq = record
         { Ob = rmfkp.Ob
         ; ar = rmfkp.C
         ; iscoeq = record
                  { eq = rmfkp.C ∘ kp₁
                       ~[ monic-sub-sq-canpf kp.×/sq rmfkp.tr rmfkp.tr rmfkp.M-is-monic ]
                         rmfkp.C ∘ kp₂
                    -- = rmfkp.Mpf (ass ⊙ ∘e r rmfkp.tr ⊙ kp.sqpf ⊙ ∘e r (rmfkp.tr ˢ) ⊙ assˢ)
                  ; univ = λ f pf → rmfkp.C.univ f (univ-pf.pfC pf)
                  ; univ-eq = λ pf → rmfkp.C.univ-eq (univ-pf.pfC pf)
                  ; uniq = rmfkp.C.uniq
                  }
         }
    private
      module q = coeq-of coeq
    exseq : is-exact-seq kp₁ kp₂ q.ar
    exseq = record
          { iscoeq = q.iscoeq
          ; iskerpair = monic-sub-pb-sq kp.×/pbsq rmfkp.tr rmfkp.tr rmfkp.M-is-monic
          }
  -- end has-quot-of-ker-pair


  -- Regular with effective eq rels is exact

  reg2exact : (eqrel→kp : {A : Obj} (eqr : eqrel-over A) → is-kernel-pair (eqr.r₁ eqr) (eqr.r₂ eqr))
                        → is-exact//has-fin-lim rℂ.hasfl
  reg2exact eqrel→kp = record
    { repi-pbof-stable = rℂ.repi-pbof-stable
    ; eqr-has-coeq = q.coeq
    ; eqr-is-eff = λ eqr → record { ispbsq = exs.iskerpair eqr }
    }
    where module q {A : Obj} (eqr : eqrel-over A) = has-quot-of-ker-pair (eqrel→kp eqr)
          module exs {A : Obj} (eqr : eqrel-over A) = is-exact-seq (q.exseq eqr)



  module pb-of-reg-covers-is-reg-cover-of-pb {I A B : Obj}{a : || Hom A I ||}{b : || Hom B I ||}
                                             (pb : pullback-of a b)
                                             (covA : reg-cover-of A)(covB : reg-cover-of B)
                                             where
    private
      module a×/b = pullback-of-not pb
      module cA = reg-cover-of covA
      module cB = reg-cover-of covB
    open pb-of-reg-covers-is-epi-cover-of-pb rℂ.haspb rℂ.repi-pbof-stable pb covA covB public
    diagl-repi : is-regular-epi diagl
    diagl-repi = ∘c cl-repi cu'-repi
            where open is-ecat-congr regular-epi-is-congr
    diagr-repi : is-regular-epi diagr
    diagr-repi = ∘c cu-repi cl'-repi
            where open is-ecat-congr regular-epi-is-congr
  -- end pb-of-reg-covers-is-reg-cover-of-pb


  module sides-cover-so-pb-covers {I A B : Obj}{a : || Hom A I ||}{b : || Hom B I ||}(inpb : pullback-of a b)
                                  {A' B' : Obj}{a' : || Hom A' I ||}{b' : || Hom B' I ||}(outpb : pullback-of a' b')
                                  {f : || Hom A' A ||}{g : || Hom B' B ||}(ftr : a ∘ f ~ a')(gtr : b ∘ g ~ b')
                                  (frepi : is-regular-epi f) (grepi : is-regular-epi g)
                                  where
    private
      module inpb = pullback-of-not inpb
      module outpb = pullback-of-not outpb
      module f = is-regular-epi frepi
      module g = is-regular-epi grepi
    open decompose-out&in-pbs rℂ.haspb inpb outpb ftr gtr public
    covpb : outpb.ul covers inpb.ul
    covpb = record
          { ar = diag
          ; is-repi = trnsp (ul-trlpf ˢ)
                            (∘c (pres-du lpb frepi)
                                (pres-rl ulpb (pres-rl upb grepi)))
          }
          where open ecategory-aux-only ℂ
                open is-ecat-congr regular-epi-is-congr
                open is-pbof-stable rℂ.repi-pbof-stable
    module covpb = _covers_ covpb 
  -- end sides-cover-so-pb-covers
-- end regular-cat-props
