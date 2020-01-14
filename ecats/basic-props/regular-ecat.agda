
-- disable the K axiom:

{-# OPTIONS --without-K #-}

-- Agda version 2.5.4.1

module ecats.basic-props.regular-ecat where

open import ecats.basic-defs.ecat-def&not
open import ecats.basic-defs.all-arrows
open import ecats.finite-limits.all
open import ecats.basic-defs.regular-ecat
open import ecats.basic-props.epi&mono
open import ecats.basic-props.image-fact
open import ecats.basic-defs.exact-ecat




-- Some properties of regular categories

module regular-cat-props {ℂ : ecategory} (isreg : is-regular ℂ) where
  open ecategory ℂ
  open arrows-defs ℂ
  open iso-transports ℂ
  open terminal-defs ℂ
  open binary-products ℂ
  open pullback-squares ℂ
  open pullback-props ℂ
  open epis&monos-props ℂ
  open image-fact-props ℂ
  private
    module rℂ where
      open is-regular isreg public
      open has-pullbacks haspb using (pb-of) public
      open has-equalisers haseql using (eql-of) public
      open has-bin-products hasprd using (prd-of) public
      open has-pb→has-kerpair haspb public
      open epis&monos-pullbacks haspb public
    module imgof = rℂ.img-of
    module sp/ = span/
    module sp = span
    module sq/ = square/cosp
    module sq = comm-square
    module ×of = product-of-not
    module pbof = pullback-of-not
    module pbsq = pb-square
    module ker {A B : Obj} (f : || Hom A B ||) = pullback-of-not (rℂ.pb-of f f)
    module eqr = eqrel-over




  imgC-is-cov : {A B : Obj} (f : || Hom A B ||) → is-cover (imgof.C f)
  imgC-is-cov f = any-imgC-is-cover (imgof.isimg f)
  private
      module Cc {A B : Obj} (f : || Hom A B ||) = is-cover (imgC-is-cov f)

  -- covers are pullback stable

  module cover-pb-stable {A B : Obj} {c : || Hom A B ||}
                         {C : Obj} {f : || Hom C B ||} (pbof : pullback-of f c) (iscov : is-cover c)
                         where
    open ecategory-aux-only ℂ
    private
      module f×/c = pullback-of-not pbof
      module c = is-cover iscov
      module imgc where
        open img-fact-of (rℂ.img-of c) public --(imgMcov-is-idar iscov)
        Miso : is-iso M
        Miso = c.cov-pf tr M-is-monic
        module M = is-iso Miso
      f×/Mc : pullback-of f imgc.M
      f×/Mc = pbof-iso f imgc.Miso
      module f×/Mc = pullback-of-not f×/Mc
      f*imgc : is-img-fact (lid {f = f×/c.π/₁})
      f*imgc = rℂ.img-pb-stable pbof f×/Mc lid
    f*c-cov : is-cover f×/c.π/₁
    f*c-cov = any-imgC-is-cover f*imgc
  -- end cover-pb-stable

  cover-pbof-stb : is-pbof-stable is-cover
  cover-pbof-stb = record { pres-rl = f*c-cov }
                 where open cover-pb-stable

  cover-pbsq-stb : is-pbsq-stable is-cover
  cover-pbsq-stb = pbof-stb→pbsq-stb cover-pbof-stb


  module ×/ₐ-of-covers-is-epi {I A' B' : Obj} {a' : || Hom A' I ||} {b' : || Hom B' I ||} (inpb : pullback-of a' b')
                                {A B : Obj} {a : || Hom A I ||} {b : || Hom B I ||}(outpb : pullback-of a b)
                                {f : || Hom A A' ||} {g : || Hom B B' ||} (f-tr : a' ∘ f ~ a) (g-tr : b' ∘ g ~ b)
                                (f-cov : is-cover f) (g-cov : is-cover g)
                                where
    private
      module inpb = pullback-of-not inpb
      module outpb = pullback-of-not outpb
    open ×/ₐ-of-pbstb-Prop-is-Prop-aux cover-is-ext cover-pbof-stb inpb outpb f-tr g-tr (rℂ.pb-of a b') f-cov g-cov
    open ×/ₐ-of-pbstb-Prop-is-Prop-aux2 epi-is-congr inpb outpb f-tr g-tr (rℂ.pb-of a b') (cover-is-epi rℂ.haseql f-cov) (cover-is-epi rℂ.haseql g-cov)
    ×/ar-is-epi : {h : || Hom outpb.ul inpb.ul ||}
                    → inpb.π/₁ ∘ h ~ f ∘ outpb.π/₁ → inpb.π/₂ ∘ h ~ g ∘ outpb.π/₂ → is-epic h
    ×/ar-is-epi pf1 pf2 = ×/arProp-cond pf1 pf2 (cover-is-epi rℂ.haseql fstProp) (cover-is-epi rℂ.haseql sndProp)
  -- end ×/ₐ-of-covers-is-epi


  private
    module kerimgC {A B : Obj} (f : || Hom A B ||) = pullback-of-not (imgC-kp (rℂ.pb-of f f) (rℂ.img-of f))
     -- same projections as ker f for the chose image factorisation



  -- for any image factorisation of f, C is the coequaliser of the kernel pair of f

  module any-imgC-is-coequaliser-univ {A B : Obj} {f : || Hom A B ||} (imgf : img-fact-of f)
                                      {C : Obj} (g : || Hom A C ||) (pf : g ∘ ker.π/₁ f ~ g ∘ ker.π/₂ f)
                                      where
    open ecategory-aux-only ℂ
    private
      module imgf where
        open img-fact-of imgf public
        open is-cover (any-imgC-is-cover isimg) renaming (cov-pf to Ccpf) public
      module kerf = ker f
      module kerCf = pullback-of-not (imgC-kp (rℂ.pb-of f f) imgf) -- same projections as kerf
      module I×C = product-of-not (rℂ.prd-of imgf.Ob C)
      p : || Hom A I×C.O12 ||
      p = I×C.< imgf.C , g >
      p-eq : p ∘ kerCf.π/₁ ~ p ∘ kerCf.π/₂
      p-eq = I×C.<>ar~<>ar kerCf.×/sqpf pf
      module imgp = imgof p
      pI : || Hom imgp.Ob imgf.Ob ||
      pI = I×C.π₁ ∘ imgp.M
      module imgpI = imgof pI
      module kerpI = ker pI
      pItr : pI ∘ imgp.C ~ imgf.C
      pItr = assˢ ⊙ ∘e imgp.tr r ⊙ I×C.×tr₁
      pIM-iso : is-iso imgpI.M
      pIM-iso = imgf.Ccpf (ass ⊙ ∘e r imgpI.tr ⊙ pItr) imgpI.M-is-monic
      pI-cov : is-cover pI
      pI-cov = record
             { cov-pf = λ tr ism → imgf.Ccpf (ass ⊙ ∘e r tr ⊙ assˢ ⊙ ∘e imgp.tr r ⊙ I×C.×tr₁) ism
             }
             where module pIM = is-iso pIM-iso
      module pI×pI where
        open ×/ₐ-of-covers-is-epi kerpI.×/of kerCf.×/of pItr pItr (imgC-is-cov p) (imgC-is-cov p)
        epf = pI ∘ imgp.C ∘ kerCf.π/₁ ~[ ass ⊙ ∘e r pItr ⊙ kerCf.×/sqpf ⊙ ∘e r (pItr ˢ) ⊙ assˢ ]
              pI ∘ imgp.C ∘ kerCf.π/₂
        e : || Hom kerCf.ul kerpI.ul ||
        e = kerpI.⟨ imgp.C ∘ kerCf.π/₁ , imgp.C ∘ kerCf.π/₂ ⟩[ epf ]
        open is-epic (×/ar-is-epi {e} (kerpI.×/tr₁ epf) (kerpI.×/tr₂ epf)) public
      pI-mon-aux : kerpI.π/₁ ∘ pI×pI.e ~ kerpI.π/₂ ∘ pI×pI.e
      pI-mon-aux = imgp.Mpf (~proof imgp.M ∘ kerpI.π/₁ ∘ pI×pI.e     ~[ ∘e (kerpI.×/tr₁ pI×pI.epf) r ⊙ ass ] /
                                    (imgp.M ∘ imgp.C) ∘ kerCf.π/₁    ~[ ∘e r imgp.tr ⊙ p-eq ⊙ ∘e r (imgp.tr ˢ) ] /
                                    (imgp.M ∘ imgp.C) ∘ kerCf.π/₂    ~[ assˢ ⊙ ∘e (kerpI.×/tr₂ pI×pI.epf ˢ) r ]∎
                                    imgp.M ∘ kerpI.π/₂ ∘ pI×pI.e ∎)
      pI-mon-pf = kerpI.π/₁ ~[ pI×pI.epi-pf pI-mon-aux ]
                  kerpI.π/₂
      pI-mon : is-monic pI
      pI-mon = π/₁~π/₂→mono (rℂ.pb-of pI pI) pI-mon-pf
      pI-iso : is-iso pI
      pI-iso = monic-cover-is-iso pI-mon pI-cov
      module pI where
        open is-monic pI-mon public
        open is-cover pI-cov public
        open is-iso pI-iso public
      pI⁻¹tr : pI.⁻¹ ∘ imgf.C ~ imgp.C
      pI⁻¹tr = pI.mono-pf (ass ⊙ lidgg (pItr ˢ) pI.idcod)
    -- end private
    un-ar : || Hom imgf.Ob C ||
    un-ar = I×C.π₂ ∘ imgp.M ∘ pI.⁻¹
    un-tr : un-ar ∘ imgf.C ~ g
    un-tr = ~proof (I×C.π₂ ∘ imgp.M ∘ pI.⁻¹) ∘ imgf.C    ~[ assˢ ⊙ ∘e (assˢ ⊙ ∘e pI⁻¹tr r) r ] /
                   I×C.π₂ ∘ imgp.M ∘ imgp.C             ~[ ∘e imgp.tr r ⊙ I×C.×tr₂ ]∎
                   g ∎
  -- end any-imgC-is-coequaliser-univ


  any-imgC-is-coeq : {A B : Obj} {f : || Hom A B ||} (imgf : img-fact-of f)
                    → is-coeq (ker.π/₁ f) (ker.π/₂ f) (img-fact-of.C imgf)
  any-imgC-is-coeq {f = f} imgf = record
    { eq = kerCf.×/sqpf
    ; univ = Ccoeq.un-ar
    ; univ-eq = λ {_} {g} → Ccoeq.un-tr g
    ; uniq = cover-is-epi rℂ.haseql (any-imgC-is-cover imgf.isimg)
    }
    where module kerCf = pullback-of-not (imgC-kp (rℂ.pb-of f f) imgf)
          module imgf = img-fact-of imgf
          module Ccoeq = any-imgC-is-coequaliser-univ imgf
          
  
  any-imgC-is-repi : {A B : Obj} {f : || Hom A B ||} (imgf : img-fact-of f)
                    → is-regular-epi (img-fact-of.C imgf)
  any-imgC-is-repi imgf = record { coeq = any-imgC-is-coeq imgf }

  
  imgC-is-repi : {A B : Obj} (f : || Hom A B ||) → is-regular-epi (imgof.C f)
  imgC-is-repi f = any-imgC-is-repi (rℂ.img-of f)



  -- covers are regular epi
  
  cover-is-regular : {A B : Obj} {c : || Hom A B ||} → is-cover c → is-regular-epi c
  cover-is-regular {c = c} iscov = any-imgC-is-repi (record { isimg = imgMcov-is-idar iscov })


  -- strong epis are regular

  strong-epi-is-regular : {A B : Obj} {f : || Hom A B ||} → is-strong-epi f → is-regular-epi f
  strong-epi-is-regular fstr = cover-is-regular (strong-epi-is-cover fstr)


  -- regular epis are ecat-congruence

  regular-epi-is-congr : is-ecat-congr ℂ is-regular-epi
  regular-epi-is-congr = mkis-ecat-congr
    (mkis-hom-ext is-regular-epi λ pfeq frepi → strong-epi-is-regular (trnsp pfeq (repi-is-strong frepi)))
    (record { ∘c = λ grepi frepi → strong-epi-is-regular (∘c (repi-is-strong grepi) (repi-is-strong frepi)) })
    where open is-ecat-congr strepi-is-congr


  -- regular epis are iso-transportable
  
  repi-is-transportable : iso-transportable is-regular-epi
  repi-is-transportable = iso-transports.mkiso-transp
    regular-epi-is-congr
    λ f fiso → split-epi-is-repi (iso-is-split-epi fiso)

  module repi-trnsp = iso-transp is-regular-epi repi-is-transportable


  -- Regular epis are pullback stable  
  repi-pbof-stb : is-pbof-stable is-regular-epi
  repi-pbof-stb = record
                { pres-rl = λ pbof repi → cover-is-regular (pres-rl pbof (repi-is-cover repi))
                }
                where open is-pbof-stable cover-pbof-stb

  repi-pbsq-stb : is-pbsq-stable is-regular-epi
  repi-pbsq-stb = pbof-stb→pbsq-stb repi-pbof-stb
  


  -- Every image factorisation is pullback stable
  
  any-img-fact-is-pb-stb : {I A B : Obj} {f : || Hom A I ||} (imgf : img-fact-of f) {g : || Hom B I ||}
                           (g×/f : pullback-of g f) (g×/Mf : pullback-of g (img-fact-of.M imgf))
                           {pbC : || Hom (pbof.ul g×/f) (pbof.ul g×/Mf) ||} (pbtr : pbof.π/₁ g×/Mf ∘ pbC ~ pbof.π/₁ g×/f)
                              → img-fact-is-pb-stable imgf g×/f g×/Mf {pbC} pbtr
  any-img-fact-is-pb-stb {I} {A} {B} {f} imgf {g} g×/f g×/Mf {pbC} pbtr = record
    { img-pb-stable = repi-mono-is-img-fact pbtr
                                            (repi-pbstb.pres-rl (upper-pbof imgf.tr pbtr upsqpf)
                                                                (any-imgC-is-repi imgf))
                                            (mono-pb-stable g×/Mf imgf.M-is-monic)
    }
    where open ecategory-aux-only ℂ
          module g×/f = pullback-of g×/f
          module g×/Mf = pullback-of g×/Mf
          module repi-pbstb = is-pbof-stable repi-pbof-stb
          module imgf = img-fact-of imgf
          open lower-and-outer-so-upper g×/Mf g×/f
          upsqpf = g×/Mf.π/₂ ∘ pbC ~[ imgf.Mpf (ass ⊙ ∘e r (g×/Mf.×/sqpf ˢ) ⊙ assˢ ⊙ ∘e pbtr r
                                               ⊙ g×/f.×/sqpf ⊙ ∘e r (imgf.tr ˢ) ⊙ assˢ) ]
                   imgf.C ∘ g×/f.π/₂
          

  module ×/ₐ-of-repis-is-repi {I A' B' : Obj} {a' : || Hom A' I ||} {b' : || Hom B' I ||} (inpb : pullback-of a' b')
                              {A B : Obj} {a : || Hom A I ||} {b : || Hom B I ||}(outpb : pullback-of a b)
                              {f : || Hom A A' ||} {g : || Hom B B' ||} (f-tr : a' ∘ f ~ a) (g-tr : b' ∘ g ~ b)
                              (f-repi : is-regular-epi f) (g-repi : is-regular-epi g)
                              = ×/ₐ-of-pbstb-Prop-is-Prop regular-epi-is-congr
                                                          repi-pbof-stb
                                                          inpb
                                                          outpb
                                                          f-tr
                                                          g-tr
                                                          (rℂ.pb-of a b')
                                                          f-repi
                                                          g-repi


  module ×ₐ-of-repi-is-repi {T : Obj} (is! : is-terminal T)
                            {A' B' : Obj} (prd' : product-of A' B') {A B : Obj} (prd : product-of A B)
                            {f : || Hom A A' ||} {g : || Hom B B' ||}
                            (f-is-repi : is-regular-epi f) (g-is-repi : is-regular-epi g)
                            where                            
    open is-terminal is!
    open relations-among-limit-diagrams ℂ
    private      
      module A×B = product-of-not prd
      module A'×B' = product-of-not prd'
      module ×/ₐrepi = ×/ₐ-of-repis-is-repi {I = T} (mkpb-of (×is-pb-on! is! A'×B'.×isprd))
                                            (mkpb-of (×is-pb-on! is! A×B.×isprd))
                                            !uqg !uqg f-is-repi g-is-repi
    ×/arcan : || Hom A×B.O12 A'×B'.O12 ||
    ×/arcan = ×/ₐrepi.×/arcan --f ×ₐ g
    ×/ar-is-repi : {h : || Hom A×B.O12 A'×B'.O12 ||}
                  → A'×B'.π₁ ∘ h ~ f ∘ A×B.π₁ → A'×B'.π₂ ∘ h ~ g ∘ A×B.π₂ → is-regular-epi h
    ×/ar-is-repi = ×/ₐrepi.×/arProp
    ×/arcan-repi : is-regular-epi ×/arcan
    ×/arcan-repi = ×/ₐrepi.×/arcanProp
  -- end ×ₐ-of-repi-is-repi


  -- If every equivalence relation is kernel pair, then ℂ is exact
  
  module effeqrel→exact-quot (eqrel→kp : {A : Obj} (eqr : eqrel-over A)
                                              → is-kernel-pair (eqr.r₁ eqr) (eqr.r₂ eqr))
                              where
         module kp = is-kernel-pair
         open eqrel-over

         kpar : {A : Obj} (eqr : eqrel-over A) → || Hom A (kp.Ob (eqrel→kp eqr)) ||
         kpar eqr = kp.ar (eqrel→kp eqr) 
         kpar-eq : {A : Obj} (eqr : eqrel-over A) → kpar eqr ∘ (r₁ eqr) ~ kpar eqr ∘ (r₂ eqr)
         kpar-eq eqr = kp.×/sqpf (eqrel→kp eqr)

         quot-eqrOb : {A : Obj} (eqr : eqrel-over A) → Obj
         quot-eqrOb eqr = imgof.Ob (kpar eqr)
         quot-eqrQ : {A : Obj} (eqr : eqrel-over A) → || Hom A (quot-eqrOb eqr) ||
         quot-eqrQ eqr = imgof.C (kpar eqr)
         
         -- Equivalence relations are effective
         eqrel-is-eff : {A : Obj} (eqr : eqrel-over A) → is-exact-seq (r₁ eqr) (r₂ eqr) (quot-eqrQ eqr)
         eqrel-is-eff eqr = record
           { iscoeq = repi-is-coeq-of-ker-pair (imgC-is-repi (kpar eqr)) (mkpb-of ispb)
           ; iskerpair = ispb
           }
           where open ecategory-aux-only ℂ
                 open is-monic (imgof.M-is-monic (kpar eqr))
                 ssq-pf : quot-eqrQ eqr ∘ (r₁ eqr) ~ quot-eqrQ eqr ∘ (r₂ eqr)
                 ssq-pf = mono-pf (ass ⊙ ∘e r (imgof.tr (kpar eqr)) ⊙ kpar-eq eqr
                                  ⊙ ∘e r (imgof.tr (kpar eqr) ˢ) ⊙ assˢ )
                 ssq = mksq (mksq/ ssq-pf)
                 ispb : is-pb-square ssq
                 ispb = monic-sub-pb-sq (mkpb-sq (kp.ispb (eqrel→kp eqr)) )
                                        (imgof.tr (kpar eqr))
                                        (imgof.tr (kpar eqr))
                                        (imgof.M-is-monic (kpar eqr))
  -- end  effeqrel→exact-quot


  -- Regular with effective eq rels is exact

  reg2exact : (eqrel→kp : {A : Obj} (eqr : eqrel-over A) → is-kernel-pair (eqr.r₁ eqr) (eqr.r₂ eqr))
                        → is-exact//has-finlim rℂ.hasfl
  reg2exact eqrel→kp = record
    { repi-pbof-stable = repi-pbof-stb
    ; eqr-has-coeq = λ eqr → record
                   { ar = quot-eqrQ eqr
                   ; iscoeq = exs.iscoeq eqr
                   }
    ; eqr-is-eff = λ eqr → record
                 { Ob = quot-eqrOb eqr
                 ; ar = quot-eqrQ eqr
                 ; iskpof = record { sqpf = exs.eq eqr
                                   ; ispb = exs.iskerpair eqr
                                   }
                 }
    }
    where open effeqrel→exact-quot eqrel→kp
          module exs {A : Obj} (eqr : eqrel-over A) = is-exact-seq (eqrel-is-eff eqr)

-- end regular-cat-props



module regular-cat-d&p {ℂ : ecategory} (reg : is-regular ℂ) where
  open is-regular reg public
  open regular-cat-props reg public
-- end regular-cat-d&p

