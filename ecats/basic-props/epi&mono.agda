
-- disable the K axiom:

{-# OPTIONS --without-K #-}

-- Agda version 2.5.4.1

module ecats.basic-props.epi&mono where

open import ecats.basic-defs.ecat-def&not
open import ecats.basic-defs.all-arrows
open import ecats.basic-props.epi&mono-basic
open import ecats.finite-limits.all


-- Some properties of monos and {regular,strong,extremal,...} epis

module epis&monos-props (ℂ : ecategory) where
  open ecategory-aux ℂ
  open arrows-defs ℂ
  open iso-transports ℂ
  open binary-products ℂ
  open wequaliser-defs ℂ
  open equaliser-defs ℂ
  open wpullback-squares ℂ
  open pullback-squares ℂ
  open pullback-props ℂ
  open bow-defs ℂ
  private
    module sp/ = span/
    module sp = span
    module sq/ = square/cosp
    module sq = comm-square
    module pbof = pullback-of
    module pbsq = pb-square
    module ×of = product-of
    module prd = bin-product
    module eqlof = equaliser-of
    module weqlof = wequaliser-of
    module wpbof = wpullback-of
    module bwof = bow-of
    --⟨_,_⟩[_]

  open epis&monos-basic-props ℂ public


  mono-pbof-stb : is-pbof-stable is-monic
  mono-pbof-stb = record
    { pres-rl = mono-pb-stable
    }

  mono-pbsq-stb : is-pbsq-stable is-monic
  mono-pbsq-stb = pbof-stb→pbsq-stb mono-pbof-stb 



  -- regular epis and kernel pairs

  repi-is-coeq-of-ker-pair : {A B : Obj} {f : || Hom A B ||} (frepi : is-regular-epi f)
                             (kpf : pullback-of f f) → is-coeq (pbof.π/₁ kpf) (pbof.π/₂ kpf) f
                              --  → {K : Obj} {kp₁ kp₂ : || Hom K A ||} → {kpcomm : f ∘ kp₁ ~ f ∘ kp₂}
                              --    → is-pb-square (mksq (mksq/ kpcomm)) → is-coeq kp₁ kp₂ f
  repi-is-coeq-of-ker-pair {A} {B} {f} frepi kpf = record
    { eq = ×/sqpf
    ; univ = λ g pf → frepi.univ g (medcmp pf)
    ; univ-eq = λ pf → frepi.univ-eq (medcmp pf)
    ; uniq = frepi.uniq
    }
    where module frepi = is-regular-epi frepi
          open pullback-of kpf
          --open pullback-sq-not (mkpb-sq iskp)
          med : || Hom frepi.relOb ul ||
          med = ⟨ frepi.rel₁ , frepi.rel₂ ⟩[ frepi.eq ]
          medcmp : {C : Obj} {g : || Hom A C ||}
                      → g ∘ π/₁ ~ g ∘ π/₂ → g ∘ frepi.rel₁ ~ g ∘ frepi.rel₂
          medcmp {C} {g} gkp = ~proof g ∘ frepi.rel₁    ~[ ∘e (×/tr₁ frepi.eq ˢ) r ] /
                                      g ∘ (π/₁ ∘ med)   ~[ ass ⊙ ∘e r gkp ⊙ assˢ ] /
                                      g ∘ (π/₂ ∘ med)   ~[ ∘e (×/tr₂ frepi.eq) r ]∎
                                      g ∘ frepi.rel₂ ∎


  kerpair-is-kerpair-of-coeq : {K A : Obj} {kp₁ kp₂ : || Hom K A ||} → is-kernel-pair kp₁ kp₂
                                  → {Q : Obj} {q : || Hom A Q ||} → (iscoeq : is-coeq kp₁ kp₂ q)
                                    → is-pb-square (mksq (mksq/ (is-coeq.eq iscoeq)))
  kerpair-is-kerpair-of-coeq iskp {Q} {q} iscoeq = subsq-of-pb-is-pb kp.×/of coeq.eq tr tr
                                                 where module kp = is-kernel-pair iskp
                                                       module coeq = is-coeq iscoeq
                                                       f : || Hom Q kp.Ob ||
                                                       f = coeq.univ kp.ar kp.×/sqpf
                                                       tr : f ∘ q ~ kp.ar
                                                       tr = coeq.univ-eq kp.×/sqpf


  kerp-of-repi-is-exact : {K A B : Obj} {kp₁ kp₂ : || Hom K A ||} {f : || Hom A B ||}
                          {kpsqpf : f ∘ kp₁ ~ f ∘ kp₂}
                             → is-pb-square (mksq (mksq/ kpsqpf)) → is-regular-epi f → is-exact-seq kp₁ kp₂ f
  kerp-of-repi-is-exact {kp₁ = kp₁} {kp₂} {f} iskp repi = record
    { iscoeq = repi-is-coeq-of-ker-pair repi (mkpb-of iskp)
    ; iskerpair = iskp
    }


  -- Epis & monos & pullbacks

  module epis&monos-pullbacks (haspb : has-pullbacks ℂ) where
    --open pullbacks-aux haspb
    --open eq-rel-defs ℂ
    open has-pullbacks haspb using (pb-of)
    

{-
    mono-pb-stable : {A B C : Obj} → {m : || Hom A B ||} → (f : || Hom C B ||) → is-monic m
                        → is-monic (π/₁ {a = f} {b = m})
    mono-pb-stable {m = m} f pfm = mono-pbsq-stable (mkpb-sq (×/ispbsq {a = f} {b = m})) pfm
-}

    module cover-is-strong {A B : Obj} {c : || Hom A B ||} (iscov : is-cover c)
                           {C D : Obj} {up : || Hom A C ||} {down : || Hom B D ||} {m : || Hom C D ||}
                           (sqpf : down ∘ c ~ m ∘ up) (pfm : is-monic m)
                           where
      private
        module d×/m = pullback-of-not (pb-of down m)
        module c = is-cover iscov
        module m = is-monic pfm
      lift-aux : is-iso d×/m.π/₁
      lift-aux = c.cov-pf (d×/m.×/tr₁ sqpf) (mono-pb-stable d×/m.×/of pfm)
      private
        module d*m = is-iso lift-aux
      com-up-aux : d*m.⁻¹ ∘ c ~ d×/m.⟨ c , up ⟩[ sqpf ]
      com-up-aux = ∘e (d×/m.×/tr₁ sqpf ˢ) r ⊙ ass ⊙ lidgg r d*m.iddom
      lift : || Hom B C ||
      lift = d×/m.π/₂ ∘ d*m.⁻¹
      tr-up : lift ∘ c ~ up
      tr-up = ~proof lift ∘ c                             ~[ assˢ ⊙ ∘e com-up-aux r ] /
                      d×/m.π/₂ ∘ d×/m.⟨ c , up ⟩[ sqpf ]   ~[ d×/m.×/tr₂ sqpf ]∎
                      up ∎
      tr-down : m ∘ lift ~ down
      tr-down = ~proof m ∘ lift                   ~[ ass ⊙ ∘e r (d×/m.×/sqpf ˢ) ⊙ assˢ ] /
                       down ∘ d×/m.π/₁ ∘ d*m.⁻¹    ~[ ridgg r d*m.idcod ]∎
                       down ∎
    -- end cover-is-strong

    cover-is-strong : {A B : Obj} {c : || Hom A B ||} → is-cover c → is-strong-epi c
    cover-is-strong iscov = record
      { lift = lift
      ; tr-up = tr-up
      ; tr-down = tr-down
      }
      where open cover-is-strong iscov

{-
    img-fact-Q-is-strong : {A B : Obj} {f : || Hom A B ||} (imgf : img-fact-of f)
                              → is-strong-epi (img-fact-of.Q imgf)
    img-fact-Q-is-strong {f = f} imgf = cover-is-strong (img-fact-Q-is-cover isimg)
                                      where open img-fact-of imgf
-}

  
    module pb-of-reg-covers-is-epi-cover-of-pb (repi-pbof-stb : is-pbof-stable is-regular-epi)
                                               {I A B : Obj}{a : || Hom A I ||}{b : || Hom B I ||}
                                               (pb : pullback-of a b)
                                               (covA : reg-cover-of A)(covB : reg-cover-of B)
                                               where
      private
        module a×/b = pullback-of-not pb
        module cA = reg-cover-of covA
        module cB = reg-cover-of covB
      open pb-over-pbof haspb pb cA.ar cB.ar public
      open is-pbof-stable repi-pbof-stb
      cl-repi : is-regular-epi lpb.π/₂
      cl-repi = pres-du lpb cA.is-repi
      cu-repi : is-regular-epi upb.π/₁
      cu-repi = pres-rl upb cB.is-repi
      cl'-repi : is-regular-epi ulpb.π/₂
      cl'-repi = pres-du ulpb cl-repi
      cu'-repi : is-regular-epi ulpb.π/₁
      cu'-repi = pres-rl ulpb cu-repi
      --cpb-ar : || Hom ulpb.ul a×/b.ul ||
      --cpb-ar = diagl
      diagl-epi : is-epic diagl
      diagl-epi = epi-cmp (repi-is-epic cl-repi) (repi-is-epic cu'-repi) r
      diagr-epi : is-epic diagr
      diagr-epi = epi-cmp (repi-is-epic cu-repi) (repi-is-epic cl'-repi) r
    -- end pb-of-reg-covers-is-epi-cover-of-pb


    module reg-covers-of-bws→epi-cover-of-bw (repi-pbof-stb : is-pbof-stable is-regular-epi)
                                              {DL U1 DR U2 : Obj} {sp1 sp2 : span/ DL DR} (bwsp : bow-of sp1 sp2)
                                              {q1 : || Hom U1 (span/.O12 sp1) ||} {q2 : || Hom U2 (span/.O12 sp2) ||}
                                              (q1-repi : is-regular-epi q1) (q2-repi : is-regular-epi q2)
                                              where
      module sp1 = span/ sp1
      module sp2 = span/ sp2
      module bwsp = bow-of bwsp
      lsq : pullback-of q1 bwsp.π//₁
      lsq = pb-of q1 bwsp.π//₁
      usq : pullback-of bwsp.π//₂ q2
      usq = pb-of bwsp.π//₂ q2
      module lsq = pullback-of-not lsq
      module usq = pullback-of-not usq
      ulsq : pullback-of lsq.π/₂ usq.π/₁
      ulsq = pb-of lsq.π/₂ usq.π/₁
      module ulsq = pullback-of-not ulsq
      open is-pbof-stable repi-pbof-stb
      ql-repi : is-regular-epi lsq.π/₂
      ql-repi = pres-du lsq q1-repi
      qu-repi : is-regular-epi usq.π/₁
      qu-repi = pres-rl usq q2-repi
      ql'-repi : is-regular-epi ulsq.π/₂
      ql'-repi = pres-du ulsq ql-repi
      qu'-repi : is-regular-epi ulsq.π/₁
      qu'-repi = pres-rl ulsq qu-repi
      ul-diag : || Hom ulsq.ul bwsp.Ob ||
      ul-diag = lsq.π/₂ ∘ ulsq.π/₁
      ul-diag-epi : is-epic ul-diag
      ul-diag-epi = epi-cmp (repi-is-epic ql-repi) (repi-is-epic qu'-repi) r
      outbw-pf₁ : (sp1.a1 ∘ q1) ∘ (lsq.π/₁ ∘ ulsq.π/₁) ~ (sp2.a1 ∘ q2) ∘ (usq.π/₂ ∘ ulsq.π/₂)
      outbw-pf₁ = assˢ ⊙ ∘e (ass ⊙ ∘e r lsq.×/sqpf) r ⊙ ass ⊙ ∘e r (ass ⊙ ∘e r bwsp.sqpf₁ ⊙ assˢ)
                  ⊙ assˢ ⊙ ∘e (assˢ ⊙ ∘e ulsq.×/sqpf r ⊙ ass ⊙ ∘e r usq.×/sqpf ⊙ assˢ) r ⊙ ass
      outbw-pf₂ : (sp1.a2 ∘ q1) ∘ (lsq.π/₁ ∘ ulsq.π/₁) ~ (sp2.a2 ∘ q2) ∘ (usq.π/₂ ∘ ulsq.π/₂)
      outbw-pf₂ = assˢ ⊙ ∘e (ass ⊙ ∘e r lsq.×/sqpf) r ⊙ ass ⊙ ∘e r (ass ⊙ ∘e r bwsp.sqpf₂ ⊙ assˢ)
                  ⊙ assˢ ⊙ ∘e (assˢ ⊙ ∘e ulsq.×/sqpf r ⊙ ass ⊙ ∘e r usq.×/sqpf ⊙ assˢ) r ⊙ ass
      outbw-sp : span/ U1 U2
      outbw-sp = mkspan/ (lsq.π/₁ ∘ ulsq.π/₁) (usq.π/₂ ∘ ulsq.π/₂)
    -- end reg-covers-of-bws→epi-cover-of-bw


{-
    -- regular epis and chosen kernel pairs (rather useless, I believe)

    repi-is-coeq-of-ker-pairᶜ : {A B : Obj} → {f : || Hom A B ||} → is-regular-epi f
                                   → is-coeq (π/₁ {a = f} {b = f}) (π/₂ {a = f} {b = f}) f
    repi-is-coeq-of-ker-pairᶜ {A} {B} {f} frepi = repi-is-coeq-of-ker-pair frepi (mkpb-of ×/ispbsq)
                                                  where open is-regular-epi frepi


    kerpair-is-kerpair-of-coeqᶜ : {A B Q : Obj} → {f : || Hom A B ||} → {q : || Hom A Q ||}
                                    → (iscoeq : is-coeq (π/kp₁ f) (π/kp₂ f) q)
                                      → is-pb-square (mksq (mksq/ (is-coeq.coeq-eq iscoeq)))
    kerpair-is-kerpair-of-coeqᶜ {A} {B} {Q} {f} {q} iscoeq = kerpair-is-kerpair-of-coeq (π/iskp f) iscoeq

    
    π/kp-repi-is-exact : {A B : Obj} {f : || Hom A B ||} (repi : is-regular-epi f) → is-exact-seq (π/kp₁ f) (π/kp₂ f) f
    π/kp-repi-is-exact {f = f} repi = kerp-of-repi-is-exact (π/iskpof f) repi
-}

  -- end epis&monos-pullbacks
  open epis&monos-pullbacks public


  module surjective-props (hastrm : has-terminal ℂ) where
    open has-terminal hastrm
    open surjective-defs hastrm


    module surj-are-pullback-stable {A B : Obj} {e : || Hom A B ||} (issurj : is-surjective e)
                                    {C : Obj} {f : || Hom C B ||} (pbof : pullback-of f e)
                                    where
      private
        module e = is-surjective issurj
        module f×/e = pullback-of-not pbof
      π/₁surj : is-surjective f×/e.π/₁
      π/₁surj = record
              { cntimg = λ c → f×/e.⟨ c , e.cntimg (f ∘ c) ⟩[ e.cntimg-pf ˢ ]
              ; cntimg-pf = λ {c} → f×/e.×/tr₁ (e.cntimg-pf ˢ)
              }
    -- end surj-are-pullback-stable

    surj-pbof-stb : is-pbof-stable is-surjective
    surj-pbof-stb = record
      { pres-rl = λ pbof issurj → surj-are-pullback-stable.π/₁surj issurj pbof }

  -- end surjective-props
-- end epis&monos-props-only
