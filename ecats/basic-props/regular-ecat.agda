
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
                        → is-exact//has-finlim rℂ.hasfl
  reg2exact eqrel→kp = record
    { repi-pbof-stable = rℂ.repi-pbof-stable
    ; eqr-has-coeq = q.coeq
    ; eqr-is-eff = λ eqr → record { ispbsq = exs.iskerpair eqr }
    }
    where module q  {A : Obj} (eqr : eqrel-over A) = has-quot-of-ker-pair (eqrel→kp eqr)
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



module regular-cat-d&p {ℂ : ecategory} (reg : is-regular ℂ) where
  open is-regular reg public
  open regular-cat-props reg public
-- end regular-cat-d&p




-- -- OLD STUFF

-- -- Some properties of regular categories

-- module regular-cat-img-props {ℂ : ecategory} (isreg : is-regular-img ℂ) where
--   open ecategory ℂ
--   open arrows-defs ℂ
--   open iso-transports ℂ
--   open terminal-defs ℂ
--   open binary-products ℂ
--   open pullback-squares ℂ
--   open pullback-props ℂ
--   open epis&monos-props ℂ
--   open image-fact-props ℂ
--   private
--     module rℂ where
--       open is-regular-img isreg public
--       open has-pullbacks haspb using (pb-of) public
--       open has-equalisers haseql using (eql-of) public
--       open has-bin-products hasprd using (prd-of) public
--       open has-pb→has-kerpair haspb public
--       open epis&monos-pullbacks haspb public
--     module imgof = rℂ.img-of
--     module sp/ = span/
--     module sp = span
--     module sq/ = square/cosp
--     module sq = comm-square
--     module ×of = product-of-not
--     module pbof = pullback-of-not
--     module pbsq = pb-square
--     module ker {A B : Obj} (f : || Hom A B ||) = pullback-of-not (rℂ.pb-of f f)
--     module eqr = eqrel-over




--   imgC-is-cov : {A B : Obj} (f : || Hom A B ||) → is-cover (imgof.C f)
--   imgC-is-cov f = any-imgC-is-cover (imgof.isimg f)
--   private
--       module Cc {A B : Obj} (f : || Hom A B ||) = is-cover (imgC-is-cov f)

--   -- covers are pullback stable

--   module cover-pb-stable {A B : Obj} {c : || Hom A B ||}
--                          {C : Obj} {f : || Hom C B ||} (pbof : pullback-of f c) (iscov : is-cover c)
--                          where
--     open ecategory-aux-only ℂ
--     private
--       module f×/c = pullback-of-not pbof
--       module c = is-cover iscov
--       module imgc where
--         open img-fact-of (rℂ.img-of c) public --(imgMcov-is-idar iscov)
--         Miso : is-iso M
--         Miso = c.cov-pf tr M-is-monic
--         module M = is-iso Miso
--       f×/Mc : pullback-of f imgc.M
--       f×/Mc = pbof-iso f imgc.Miso
--       module f×/Mc = pullback-of-not f×/Mc
--       f*imgc : is-img-fact (lid {f = f×/c.π/₁})
--       f*imgc = rℂ.img-pb-stable c pbof f×/Mc lid
--     f*c-cov : is-cover f×/c.π/₁
--     f*c-cov = any-imgC-is-cover f*imgc
--   -- end cover-pb-stable

--   cover-pbof-stb : is-pbof-stable is-cover
--   cover-pbof-stb = record { pres-rl = f*c-cov }
--                  where open cover-pb-stable

--   cover-pbsq-stb : is-pbsq-stable is-cover
--   cover-pbsq-stb = pbof-stb→pbsq-stb cover-pbof-stb



-- -- *** NB the following can be reformulated to prove a weaker, but sufficiently strong, statement. ***

--   module ×/ₐ-of-covers-is-epi {I A' B' : Obj} {a' : || Hom A' I ||} {b' : || Hom B' I ||} (inpb : pullback-of a' b')
--                               {A B : Obj} {a : || Hom A I ||} {b : || Hom B I ||}(outpb : pullback-of a b)
--                               {f : || Hom A A' ||} {g : || Hom B B' ||} (f-tr : a' ∘ f ~ a) (g-tr : b' ∘ g ~ b)
--                               (f-cov : is-cover f) (g-cov : is-cover g)
--                               where
--     private
--       module inpb = pullback-of-not inpb
--       module outpb = pullback-of-not outpb
--       module f = is-cover f-cov
--       module g = is-cover g-cov
--     open ecategory-aux-only ℂ
--     open is-pbof-stable cover-pbof-stb
--     open decompose-out&in-pbs rℂ.haspb inpb outpb f-tr g-tr public
--     diag-is-epi : is-epic diag
--     diag-is-epi = epi-cmp (cover-is-epi rℂ.haseql (pres-du lpb f-cov))
--                           (cover-is-epi rℂ.haseql (pres-rl ulpb (pres-rl upb g-cov)))
--                           (ul-trlpf ˢ)
-- -- *** NB the term epi-pf is HUGE! ***


-- {-    check : {C : Obj} {h : || Hom C lpb.ul ||} {h' : || Hom ulpb.ul C ||}
--                → h ∘ h' ~ ulpb.π/₁ → is-monic h → Obj
--     check {C} {h} {h'} pf pfm = {!cov-pf {C} {h'} {h} pf pfm  !}
--                           where open is-epic diag-is-epi
--                                 open is-cover (pres-rl ulpb (pres-rl upb g-cov)) -}


-- {-
--     open ecategory-aux-only ℂ
--     private
--       module inpb = pullback-of-not inpb
--       module outpb = pullback-of-not outpb
--     --open ×/ₐ-of-pbstb-Prop-is-Prop-aux cover-is-ext cover-pbof-stb inpb outpb f-tr g-tr (rℂ.pb-of a b') f-cov g-cov
--     --open ×/ₐ-of-pbstb-Prop-is-Prop-aux2 epi-is-congr inpb outpb f-tr g-tr (rℂ.pb-of a b') (cover-is-epi rℂ.haseql f-cov) (cover-is-epi rℂ.haseql g-cov)
--       module a×/b' =  pullback-of-not (rℂ.pb-of a b')
--       snd-pf = outpb.×/sqpf ⊙ ∘e r (g-tr ˢ) ⊙ assˢ
--       snd : || Hom outpb.ul a×/b'.ul ||
--       snd = a×/b'.⟨ outpb.π/₁ , g ∘ outpb.π/₂ ⟩[ snd-pf ]
--       fst-pf : a' ∘ f ∘ a×/b'.π/₁ ~ b' ∘ a×/b'.π/₂
--       fst-pf = ass ⊙ ∘e r f-tr ⊙ a×/b'.×/sqpf
--       fst : || Hom a×/b'.ul inpb.ul ||
--       fst = inpb.⟨ f ∘ a×/b'.π/₁ , a×/b'.π/₂ ⟩[ fst-pf ]
--     fst-cov : is-cover fst
--     fst-cov = pres-du (mkpb-of fst-pbsq) f-cov
--            where open is-pbof-stable cover-pbof-stb
--                  fst-sq : f ∘ a×/b'.π/₁ ~ inpb.π/₁ ∘ fst
--                  fst-sq = inpb.×/tr₁ fst-pf ˢ
--                  fst-pbsq : is-pb-square (mksq (mksq/ fst-sq))
--                  fst-pbsq = left-is-pbsq {f} {fst} f-tr (inpb.×/tr₂ fst-pf) fst-sq
--                         where open right-and-outer-so-left inpb (rℂ.pb-of a b')
--     snd-cov : is-cover snd
--     snd-cov = pres-rl (mkpb-of snd-pbsq) g-cov
--                  where open is-pbof-stable cover-pbof-stb
--                        snd-sq : a×/b'.π/₂ ∘ snd ~ g ∘ outpb.π/₂
--                        snd-sq = a×/b'.×/tr₂ snd-pf
--                        snd-pbsq : is-pb-square (mksq (mksq/ snd-sq))
--                        snd-pbsq = upper-is-pbsq {g} {snd} g-tr (a×/b'.×/tr₁ snd-pf) snd-sq
--                                  where open lower-and-outer-so-upper (rℂ.pb-of a b') outpb
    
--     --×/arcan : || Hom outpb.ul inpb.ul ||
--     --×/arcan = f ×/ₐ g [ f-tr , g-tr ]
--       --      where open ×/ₐdef inpb outpb
--     ×/ar-tr : {h : || Hom outpb.ul inpb.ul ||}
--                  → inpb.π/₁ ∘ h ~ f ∘ outpb.π/₁ → inpb.π/₂ ∘ h ~ g ∘ outpb.π/₂
--                    → fst ∘ snd ~ h
--     ×/ar-tr {h} pf1 pf2 = inpb.×/uq
--       (~proof inpb.π/₁ ∘ fst ∘ snd   ~[ ass ⊙ ∘e r (inpb.×/tr₁ fst-pf) ⊙ assˢ ] /
--               f ∘ a×/b'.π/₁ ∘ snd      ~[ ∘e (a×/b'.×/tr₁ snd-pf) r ] /
--               f ∘ outpb.π/₁              ~[ pf1 ˢ ]∎
--               inpb.π/₁ ∘ h ∎)
--       (~proof inpb.π/₂ ∘ fst ∘ snd   ~[ ass ⊙ ∘e r (inpb.×/tr₂ fst-pf) ] /
--               a×/b'.π/₂ ∘ snd          ~[ a×/b'.×/tr₂ snd-pf ] /
--               g ∘ outpb.π/₂              ~[ pf2 ˢ ]∎
--               inpb.π/₂ ∘ h ∎)                      
--     ×/ar-is-epi : {h : || Hom outpb.ul inpb.ul ||}
--                     → inpb.π/₁ ∘ h ~ f ∘ outpb.π/₁ → inpb.π/₂ ∘ h ~ g ∘ outpb.π/₂ → is-epic h
--     ×/ar-is-epi pf1 pf2 = epi-cmp (cover-is-epi rℂ.haseql fst-cov)
--                                   (cover-is-epi rℂ.haseql snd-cov)
--                                   (×/ar-tr pf1 pf2)
--     -- The term is-epi.epi-pf (×/ar-is-epi pf1 pf2) is VERY big
-- {-
--     check : {h : || Hom outpb.ul inpb.ul ||}
--                     → inpb.π/₁ ∘ h ~ f ∘ outpb.π/₁ → inpb.π/₂ ∘ h ~ g ∘ outpb.π/₂
--                     → {C : Obj} {k : || Hom inpb.ul C ||} {k' : || Hom inpb.ul C ||} → k ∘ fst ~ k' ∘ fst
--                     --→ {C : Obj} {p : || Hom a×/b'.ul C ||} {m : || Hom C inpb.ul ||} → m ∘ p ~ fst → is-monic m
--                       → Obj
--     check {h} pf1 pf2 pf = {!epi-pf pf!}
--                       where open is-epic (cover-is-epi rℂ.haseql fst-cov)
--                             --(×/ar-is-epi pf1 pf2)
--                             --open is-cover fst-cov
-- -}
--   -- end ×/ₐ-of-covers-is-epi
-- -}


--   private
--     module kerimgC {A B : Obj} (f : || Hom A B ||) = pullback-of-not (imgC-kp (rℂ.pb-of f f) (rℂ.img-of f))
--      -- same projections as ker f for the chosen image factorisation
--      -- imgC-kp kerf imgf is the proof that kerf is also a pullback of imgf.C



--   -- for any image factorisation of f, C is the coequaliser of the kernel pair of f

--   module any-imgC-is-coequaliser-univ {A B : Obj} {f : || Hom A B ||} (imgf : img-fact-of f)
--                                       {C : Obj} (g : || Hom A C ||) (pf : g ∘ ker.π/₁ f ~ g ∘ ker.π/₂ f)
--                                       where
--     open ecategory-aux-only ℂ
--     private
--       module imgf where
--         open img-fact-of imgf public
--         open is-cover (any-imgC-is-cover isimg) renaming (cov-pf to Ccpf) public
--       module kerf = ker f
--       module kerCf = pullback-of-not (imgC-kp (rℂ.pb-of f f) imgf) -- same projections as kerf
--       module I×C = product-of-not (rℂ.prd-of imgf.Ob C)
--     p : || Hom A I×C.O12 ||
--     p = I×C.< imgf.C , g >
--     p-eq : p ∘ kerCf.π/₁ ~ p ∘ kerCf.π/₂
--     p-eq = I×C.<>ar~<>ar kerCf.×/sqpf pf
--     module imgp = imgof p
--     pI : || Hom imgp.Ob imgf.Ob ||
--     pI = I×C.π₁ ∘ imgp.M
--     module imgpI = imgof pI
--     module kerpI = ker pI
--     pItr : pI ∘ imgp.C ~ imgf.C
--     pItr = assˢ ⊙ ∘e imgp.tr r ⊙ I×C.×tr₁
--     pIM-iso : is-iso imgpI.M
--     pIM-iso = imgf.Ccpf (ass ⊙ ∘e r imgpI.tr ⊙ pItr) imgpI.M-is-monic
--     pI-cov : is-cover pI
--     pI-cov = record
--            { cov-pf = λ tr ism → imgf.Ccpf (ass ⊙ ∘e r tr ⊙ assˢ ⊙ ∘e imgp.tr r ⊙ I×C.×tr₁) ism
--            }
--            where module pIM = is-iso pIM-iso
--     --epf = pI ∘ imgp.C ∘ kerCf.π/₁ ~[ ass ⊙ ∘e r pItr ⊙ kerCf.×/sqpf ⊙ ∘e r (pItr ˢ) ⊙ assˢ ]
--       --    pI ∘ imgp.C ∘ kerCf.π/₂
--     --e : || Hom kerCf.ul kerpI.ul ||
--     --e = kerpI.⟨ imgp.C ∘ kerCf.π/₁ , imgp.C ∘ kerCf.π/₂ ⟩[ epf ]
--     module C×C where
--       open ×/ₐ-of-covers-is-epi kerpI.×/of kerCf.×/of pItr pItr (imgC-is-cov p) (imgC-is-cov p) public
--       open is-epic diag-is-epi public --(×/ar-is-epi {e} (kerpI.×/tr₁ epf) (kerpI.×/tr₂ epf)) public
--     -- C×C.epi-pf is HUGE
--     pI-mon-aux : kerpI.π/₁ ∘ C×C.diag ~ kerpI.π/₂ ∘ C×C.diag
--     pI-mon-aux = imgp.Mpf (~proof imgp.M ∘ kerpI.π/₁ ∘ C×C.diag     ~[ ∘e (kerpI.×/tr₁ C×C.diag-pf) r ⊙ ass ] /
--                                   (imgp.M ∘ imgp.C) ∘ kerCf.π/₁    ~[ ∘e r imgp.tr ⊙ p-eq ⊙ ∘e r (imgp.tr ˢ) ] /
--                                   (imgp.M ∘ imgp.C) ∘ kerCf.π/₂    ~[ assˢ ⊙ ∘e (kerpI.×/tr₂ C×C.diag-pf ˢ) r ]∎
--                                   imgp.M ∘ kerpI.π/₂ ∘ C×C.diag ∎)
--     pI-mon-pf : kerpI.π/₁ ~ kerpI.π/₂
--     pI-mon-pf = C×C.epi-pf pI-mon-aux
--     pI-mon : is-monic pI
--     pI-mon = π/₁~π/₂→mono (rℂ.pb-of pI pI) pI-mon-pf
--     pI-iso : is-iso pI
--     pI-iso = monic-cover-is-iso pI-mon pI-cov
--     module pI where
--       open is-monic pI-mon public
--       open is-cover pI-cov public
--       open is-iso pI-iso public
--     pI⁻¹tr : pI.⁻¹ ∘ imgf.C ~ imgp.C
--     pI⁻¹tr = pI.mono-pf (ass ⊙ lidgg (pItr ˢ) pI.idcod)
--     un-ar : || Hom imgf.Ob C ||
--     un-ar = I×C.π₂ ∘ imgp.M ∘ pI.⁻¹
--     un-tr : un-ar ∘ imgf.C ~ g
--     un-tr = ~proof (I×C.π₂ ∘ imgp.M ∘ pI.⁻¹) ∘ imgf.C    ~[ assˢ ⊙ ∘e (assˢ ⊙ ∘e pI⁻¹tr r) r ] /
--                    I×C.π₂ ∘ imgp.M ∘ imgp.C             ~[ ∘e imgp.tr r ⊙ I×C.×tr₂ ]∎
--                    g ∎
--   -- end any-imgC-is-coequaliser-univ


--   any-imgC-is-coeq : {A B : Obj} {f : || Hom A B ||} (imgf : img-fact-of f)
--                     → is-coeq (ker.π/₁ f) (ker.π/₂ f) (img-fact-of.C imgf)
--   any-imgC-is-coeq {A} {B} {f = f} imgf = record
--     { eq = kerCf.×/sqpf
--     ; univ = Ccoeq.un-ar
--     ; univ-eq = λ {_} {g} pf → Ccoeq.un-tr g pf
--     ; uniq = cover-is-epi rℂ.haseql (any-imgC-is-cover imgf.isimg)
--     }
--     where module kerCf = pullback-of-not (imgC-kp (rℂ.pb-of f f) imgf)
--           module imgf = img-fact-of imgf
--           module Ccoeq = any-imgC-is-coequaliser-univ imgf
--           {-check : {C : Obj} (g : || Hom A C ||) (pf : g ∘ ker.π/₁ f ~ g ∘ ker.π/₂ f)
--                   {D : Obj} {k k' : || Hom (Ccoeq.kerpI.ul g pf) D ||}→ k ∘ Ccoeq.e g pf ~ k' ∘ Ccoeq.e g pf
--                     → Obj
--           check g pfg pfe = {!Ccoeq.C×C.epi-pf g pfg pfe!}-}

  
--   any-imgC-is-repi : {A B : Obj} {f : || Hom A B ||} (imgf : img-fact-of f)
--                     → is-regular-epi (img-fact-of.C imgf)
--   any-imgC-is-repi imgf = record { coeq = any-imgC-is-coeq imgf }

  
--   imgC-is-repi : {A B : Obj} (f : || Hom A B ||) → is-regular-epi (imgof.C f)
--   imgC-is-repi f = any-imgC-is-repi (rℂ.img-of f)



--   -- covers are regular epis
  
--   cover-is-regular : {A B : Obj} {c : || Hom A B ||} → is-cover c → is-regular-epi c
--   cover-is-regular {c = c} iscov = any-imgC-is-repi (record { isimg = imgMcov-is-idar iscov })


--   -- strong epis are regular

--   strong-epi-is-regular : {A B : Obj} {f : || Hom A B ||} → is-strong-epi f → is-regular-epi f
--   strong-epi-is-regular fstr = cover-is-regular (strong-epi-is-cover fstr)


--   -- is-regular-epi is ecat congruence

--   regular-epi-is-congr : is-ecat-congr ℂ is-regular-epi
--   regular-epi-is-congr = mkis-ecat-congr
--     (mkis-hom-ext is-regular-epi λ pfeq frepi → strong-epi-is-regular (trnsp pfeq (repi-is-strong frepi)))
--     (record { ∘c = λ grepi frepi → strong-epi-is-regular (∘c (repi-is-strong grepi) (repi-is-strong frepi)) })
--     where open is-ecat-congr strepi-is-congr


--   -- regular epis are iso-transportable
  
--   repi-is-transportable : iso-transportable is-regular-epi
--   repi-is-transportable = iso-transports.mkiso-transp
--     regular-epi-is-congr
--     λ f fiso → split-epi-is-repi (iso-is-split-epi fiso)

--   module repi-trnsp = iso-transp is-regular-epi repi-is-transportable


--   -- Regular epis are pullback stable  
--   repi-pbof-stb : is-pbof-stable is-regular-epi
--   repi-pbof-stb = record
--                 { pres-rl = λ pbof repi → cover-is-regular (pres-rl pbof (repi-is-cover repi))
--                 }
--                 where open is-pbof-stable cover-pbof-stb

--   repi-pbsq-stb : is-pbsq-stable is-regular-epi
--   repi-pbsq-stb = pbof-stb→pbsq-stb repi-pbof-stb
  


--   -- Every image factorisation is pullback stable

--   module any-img-fact-is-pb-stb {I A : Obj} {f : || Hom A I ||} (imgf : img-fact-of f)
--                                 {B : Obj} {g : || Hom B I ||}
--                                 (g×/f : pullback-of g f) (g×/Mf : pullback-of g (img-fact-of.M imgf))
--                                 {pbC : || Hom (pbof.ul g×/f) (pbof.ul g×/Mf) ||} (pbtr : pbof.π/₁ g×/Mf ∘ pbC ~ pbof.π/₁ g×/f)
--                                 where
--     open ecategory-aux-only ℂ
--     module g×/f = pullback-of g×/f
--     module g×/Mf = pullback-of g×/Mf
--     module repi-pbstb = is-pbof-stable repi-pbof-stb
--     module imgf = img-fact-of imgf
--     open lower-and-outer-so-upper g×/Mf g×/f
--     upsqpf = g×/Mf.π/₂ ∘ pbC ~[ imgf.Mpf (ass ⊙ ∘e r (g×/Mf.×/sqpf ˢ) ⊙ assˢ ⊙ ∘e pbtr r
--                                          ⊙ g×/f.×/sqpf ⊙ ∘e r (imgf.tr ˢ) ⊙ assˢ) ]
--              imgf.C ∘ g×/f.π/₂
--     pbimg-is-img : is-img-fact pbtr
--     pbimg-is-img = repi-mono-is-img-fact pbtr
--                                          (repi-pbstb.pres-rl (upper-pbof imgf.tr pbtr upsqpf)
--                                                              (any-imgC-is-repi imgf))
--                                          (mono-pb-stable g×/Mf imgf.M-is-monic)
--   -- end any-img-fact-is-pb-stb
  

--   any-img-fact-is-pb-stb : {I A B : Obj} {f : || Hom A I ||} (imgf : img-fact-of f)
--                               → img-fact-is-pb-stable imgf
--   any-img-fact-is-pb-stb {I} {A} {B} {f} imgf = record
--     { img-pb-stable = pbimg-is-img
--     }
--     where open any-img-fact-is-pb-stb imgf


--   module pb-of-reg-covers-is-reg-cover-of-pb {I A B : Obj}{a : || Hom A I ||}{b : || Hom B I ||}
--                                              (pb : pullback-of a b)
--                                              (covA : reg-cover-of A)(covB : reg-cover-of B)
--                                              where
--     private module a×/b = pullback-of-not pb
--     module cA = reg-cover-of covA
--     module cB = reg-cover-of covB
--     open pb-over-pbof rℂ.haspb pb cA.ar cB.ar public
--     {-cApb : pullback-of cA.ar a×/b.π/₁
--     cApb = rℂ.pb-of cA.ar a×/b.π/₁
--     cBpb : pullback-of a×/b.π/₂ cB.ar
--     cBpb = rℂ.pb-of a×/b.π/₂ cB.ar
--     module cApb = pullback-of-not cApb
--     module cBpb = pullback-of-not cBpb
--     ulsq : pullback-of cApb.π/₂ cBpb.π/₁
--     ulsq = rℂ.pb-of cApb.π/₂ cBpb.π/₁
--     module ulsq = pullback-of-not ulsq-}
--     open is-pbof-stable repi-pbof-stb
--     cl-repi : is-regular-epi lpb.π/₂
--     cl-repi = pres-du lpb cA.is-repi
--     cu-repi : is-regular-epi upb.π/₁
--     cu-repi = pres-rl upb cB.is-repi
--     cl'-repi : is-regular-epi ulpb.π/₂
--     cl'-repi = pres-du ulpb cl-repi
--     cu'-repi : is-regular-epi ulpb.π/₁
--     cu'-repi = pres-rl ulpb cu-repi
--     cpb-ar : || Hom ulpb.ul a×/b.ul ||
--     cpb-ar = diagl --lpb.π/₂ ∘ ulpb.π/₁
--     cpb-repi : is-regular-epi cpb-ar
--     cpb-repi = ∘c cl-repi cu'-repi
--             where open is-ecat-congr regular-epi-is-congr
--     {-outsq-pf : (a ∘ cA.ar) ∘ (lpb.π/₁ ∘ ulpb.π/₁) ~ (b ∘ cB.ar) ∘ (upb.π/₂ ∘ ulpb.π/₂)
--     outsq-pf = assˢ ⊙ ∘e (ass ⊙ ∘e r lpb.×/sqpf) r ⊙ ass ⊙ ∘e r (ass ⊙ ∘e r a×/b.×/sqpf ⊙ assˢ)
--                ⊙ assˢ ⊙ ∘e (assˢ ⊙ ∘e ulpb.×/sqpf r ⊙ ass ⊙ ∘e r upb.×/sqpf ⊙ assˢ) r ⊙ ass
--              where open ecategory-aux-only ℂ
--     outsq-pb : is-pb-square (mksq (mksq/ outsq-pf))
--     outsq-pb = du.any-outer-is-pbsq r outsq-pf
--              where open ecategory-aux-only ℂ
--                    module d-rl = right-and-left-so-outer a×/b.×/ispbsq lpb
--                    module u-rl = right-and-left-so-outer upb.×/ispbsq ulpb
--                    module du = lower-and-upper-so-outer (d-rl.outer-is-pbsq r) (u-rl.outer-pbof r)
--     module outpb = pullback-of-not (mkpb-of outsq-pb)-}
--   -- end pb-of-covers-is-cover-of-pb


--   module sides-cover-so-pb-covers {I A B : Obj}{a : || Hom A I ||}{b : || Hom B I ||}(inpb : pullback-of a b)
--                                   {A' B' : Obj}{a' : || Hom A' I ||}{b' : || Hom B' I ||}(outpb : pullback-of a' b')
--                                   {f : || Hom A' A ||}{g : || Hom B' B ||}(ftr : a ∘ f ~ a')(gtr : b ∘ g ~ b')
--                                   (frepi : is-regular-epi f) (grepi : is-regular-epi g)
--                                   where
--     private
--       module inpb = pullback-of-not inpb
--       module outpb = pullback-of-not outpb
--       module f = is-regular-epi frepi
--       module g = is-regular-epi grepi
--     open decompose-out&in-pbs rℂ.haspb inpb outpb ftr gtr public
--     covpb : outpb.ul covers inpb.ul
--     covpb = record
--           { ar = diag
--           ; is-repi = trnsp (ul-trlpf ˢ)
--                             (∘c (pres-du lpb frepi)
--                                 (pres-rl ulpb (pres-rl upb grepi)))
--           }
--           where open ecategory-aux-only ℂ
--                 open is-ecat-congr regular-epi-is-congr
--                 open is-pbof-stable repi-pbof-stb
--     module covpb = _covers_ covpb 
--   -- end sides-cover-so-pb-covers
  
-- {-
--   module ×/ₐ-of-repis-is-repi {I A' B' : Obj} {a' : || Hom A' I ||} {b' : || Hom B' I ||} (inpb : pullback-of a' b')
--                               {A B : Obj} {a : || Hom A I ||} {b : || Hom B I ||}(outpb : pullback-of a b)
--                               {f : || Hom A A' ||} {g : || Hom B B' ||} (f-tr : a' ∘ f ~ a) (g-tr : b' ∘ g ~ b)
--                               (f-repi : is-regular-epi f) (g-repi : is-regular-epi g)
--                               = ×/ₐ-of-pbstb-Prop-is-Prop regular-epi-is-congr
--                                                           repi-pbof-stb
--                                                           inpb
--                                                           outpb
--                                                           f-tr
--                                                           g-tr
--                                                           (rℂ.pb-of a b')
--                                                           f-repi
--                                                           g-repi


--   module ×ₐ-of-repi-is-repi {T : Obj} (is! : is-terminal T)
--                             {A' B' : Obj} (prd' : product-of A' B') {A B : Obj} (prd : product-of A B)
--                             {f : || Hom A A' ||} {g : || Hom B B' ||}
--                             (f-is-repi : is-regular-epi f) (g-is-repi : is-regular-epi g)
--                             where                            
--     open is-terminal is!
--     open relations-among-limit-diagrams ℂ
--     private      
--       module A×B = product-of-not prd
--       module A'×B' = product-of-not prd'
--       module ×/ₐrepi = ×/ₐ-of-repis-is-repi {I = T} (mkpb-of (×is-pb-on! is! A'×B'.×isprd))
--                                             (mkpb-of (×is-pb-on! is! A×B.×isprd))
--                                             !uqg !uqg f-is-repi g-is-repi
--     ×/arcan : || Hom A×B.O12 A'×B'.O12 ||
--     ×/arcan = ×/ₐrepi.×/arcan --f ×ₐ g
--     ×/ar-is-repi : {h : || Hom A×B.O12 A'×B'.O12 ||}
--                   → A'×B'.π₁ ∘ h ~ f ∘ A×B.π₁ → A'×B'.π₂ ∘ h ~ g ∘ A×B.π₂ → is-regular-epi h
--     ×/ar-is-repi = ×/ₐrepi.×/arProp
--     ×/arcan-repi : is-regular-epi ×/arcan
--     ×/arcan-repi = ×/ₐrepi.×/arcanProp
--   -- end ×ₐ-of-repi-is-repi
-- -}

--   -- If every equivalence relation is kernel pair, then ℂ is exact
  
--   module effeqrel→exact-quot (eqrel→kp : {A : Obj} (eqr : eqrel-over A)
--                                               → is-kernel-pair (eqr.r₁ eqr) (eqr.r₂ eqr))
--                               where
--          module kp = is-kernel-pair
--          open eqrel-over

--          kpar : {A : Obj} (eqr : eqrel-over A) → || Hom A (kp.Ob (eqrel→kp eqr)) ||
--          kpar eqr = kp.ar (eqrel→kp eqr) 
--          kpar-eq : {A : Obj} (eqr : eqrel-over A) → kpar eqr ∘ (r₁ eqr) ~ kpar eqr ∘ (r₂ eqr)
--          kpar-eq eqr = kp.×/sqpf (eqrel→kp eqr)

--          quot-eqrOb : {A : Obj} (eqr : eqrel-over A) → Obj
--          quot-eqrOb eqr = imgof.Ob (kpar eqr)
--          quot-eqrQ : {A : Obj} (eqr : eqrel-over A) → || Hom A (quot-eqrOb eqr) ||
--          quot-eqrQ eqr = imgof.C (kpar eqr)
         
--          -- Equivalence relations are effective
--          eqrel-is-eff : {A : Obj} (eqr : eqrel-over A) → is-exact-seq (r₁ eqr) (r₂ eqr) (quot-eqrQ eqr)
--          eqrel-is-eff eqr = record
--            { iscoeq = repi-is-coeq-of-ker-pair (imgC-is-repi (kpar eqr)) (mkpb-of ispb)
--            ; iskerpair = ispb
--            }
--            where open ecategory-aux-only ℂ
--                  open is-monic (imgof.M-is-monic (kpar eqr))
--                  ssq-pf : quot-eqrQ eqr ∘ (r₁ eqr) ~ quot-eqrQ eqr ∘ (r₂ eqr)
--                  ssq-pf = mono-pf (ass ⊙ ∘e r (imgof.tr (kpar eqr)) ⊙ kpar-eq eqr
--                                   ⊙ ∘e r (imgof.tr (kpar eqr) ˢ) ⊙ assˢ )
--                  ssq = mksq (mksq/ ssq-pf)
--                  ispb : is-pb-square ssq
--                  ispb = monic-sub-pb-sq (mkpb-sq (kp.ispb (eqrel→kp eqr)) )
--                                         (imgof.tr (kpar eqr))
--                                         (imgof.tr (kpar eqr))
--                                         (imgof.M-is-monic (kpar eqr))
--   -- end  effeqrel→exact-quot


--   -- Regular with effective eq rels is exact

--   reg2exact : (eqrel→kp : {A : Obj} (eqr : eqrel-over A) → is-kernel-pair (eqr.r₁ eqr) (eqr.r₂ eqr))
--                         → is-exact//has-finlim rℂ.hasfl
--   reg2exact eqrel→kp = record
--     { repi-pbof-stable = repi-pbof-stb
--     ; eqr-has-coeq = λ eqr → record
--                    { ar = quot-eqrQ eqr
--                    ; iscoeq = exs.iscoeq eqr
--                    }
--     ; eqr-is-eff = λ eqr → record
--                  { Ob = quot-eqrOb eqr
--                  ; ar = quot-eqrQ eqr
--                  ; iskpof = record { sqpf = exs.eq eqr
--                                    ; ispb = exs.iskerpair eqr
--                                    }
--                  }
--     }
--     where open effeqrel→exact-quot eqrel→kp
--           module exs {A : Obj} (eqr : eqrel-over A) = is-exact-seq (eqrel-is-eff eqr)

-- -- end regular-cat-img-props



-- module regular-cat-img-d&p {ℂ : ecategory} (reg : is-regular-img ℂ) where
--   open is-regular-img reg public
--   open regular-cat-img-props reg public
-- -- end regular-cat-img-d&p

