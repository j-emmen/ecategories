
-- disable the K axiom:

{-# OPTIONS --without-K #-}

-- Agda version 2.5.4.1

module ecats.basic-props.exact-ecat where

open import ecats.basic-defs.ecat-def&not
open import ecats.basic-defs.all-arrows
open import ecats.finite-limits.all
open import ecats.basic-defs.regular-ecat
open import ecats.basic-defs.exact-ecat
open import ecats.basic-props.epi&mono
open import ecats.basic-props.image-fact
open import ecats.basic-props.regular-ecat



-- Some properties of exact categories

module exact-cat-props-only {𝔼 : ecategory} (isex : is-exact 𝔼) where
  open ecategory 𝔼
  open arrows-defs 𝔼
  open epis&monos-props 𝔼
  open image-fact-props 𝔼
  open binary-products 𝔼
  open pullback-squares 𝔼
  open pullback-props 𝔼
  private
    module ex𝔼 where
      open is-exact isex public
      open has-pullbacks haspb using (pb-of) public
      open has-equalisers haseql using (eql-of) public
      open has-bin-products hasprd using (prd-of) public
      open has-pb→has-kerpair haspb public
      open epis&monos-pullbacks haspb public
    module Q {A : Obj} (eqr : eqrel-over A) = coeq-of (ex𝔼.eqr-has-coeq eqr)
    module sp/ = span/
    module sp = span
    module sq/ = square/cosp
    module sq = comm-square
    module pbof = pullback-of
    module pbsq = pb-square
    module ×of = product-of
    module prd = bin-product
    module eqr/ = eqrel-over
    module ker {A B : Obj} (f : || Hom A B ||) = pullback-of-not (ex𝔼.pb-of f f)


  -- Any coequaliser diagram of an equivalence relation is an exact diagram
  
  coeq-of-eqrel-is-eff : {A Q : Obj} {q : || Hom A Q ||} (eqr : eqrel-over A)
                → is-coeq (eqr/.r₁ eqr) (eqr/.r₂ eqr) q
                  → is-exact-seq (eqr/.r₁ eqr) (eqr/.r₂ eqr) q
  coeq-of-eqrel-is-eff eqr coeq = record
    { iscoeq = coeq
    ; iskerpair = kerpair-is-kerpair-of-coeq (record { iskpof = record
                { ispb = kerpair-is-kerpair-of-coeq (ex𝔼.eqr-is-eff eqr) coeq } })
                                             coeq
    }
    where module eqrQ = coeq-of (ex𝔼.eqr-has-coeq eqr)
    

  -- The chosen quotients of equivalence relations are effective.
  
  ex-seq : {A : Obj} (eqr : eqrel-over A)
                → is-exact-seq (eqr/.r₁ eqr) (eqr/.r₂ eqr) (Q.ar eqr)
  ex-seq eqr = coeq-of-eqrel-is-eff eqr (Q.iscoeq eqr)



  module ×/ₐ-of-repis-is-epi {I A B A' B' : Obj}
                             {a : || Hom A I ||} {b : || Hom B I ||} {a' : || Hom A' I ||} {b' : || Hom B' I ||}
                             (pbof : pullback-of a b) (pbof' : pullback-of a' b')
                             {qa : || Hom A A' ||} {qb : || Hom B B' ||} (a-tr : a' ∘ qa ~ a) (b-tr : b' ∘ qb ~ b)
                             (qa-is-repi : is-regular-epi qa) (qb-is-repi : is-regular-epi qb)
                             where
    private
      a×/b = pbof
      a'×/b' = pbof'
      a×/b' : pullback-of a b'
      a×/b' = ex𝔼.pb-of a b'
      module qa = is-regular-epi qa-is-repi
      module qb = is-regular-epi qb-is-repi
      module a×/b = pullback-of-not a×/b
      module a'×/b' = pullback-of-not a'×/b'
      module a×/b' =  pullback-of-not a×/b'
      module ×/ar  {I A₁ B₁ : Obj} {a₁ : || Hom A₁ I ||} {b₁ : || Hom B₁ I ||}
                   {A₂ B₂ : Obj} {a₂ : || Hom A₂ I ||} {b₂ : || Hom B₂ I ||}
                   (pbsq₁ : pullback-of a₁ b₁) (pbsq₂ : pullback-of a₂ b₂)
                   where
        open ×/ₐdef pbsq₁ pbsq₂ public
        open ×/ₐnot-only pbsq₁ pbsq₂ public
    open ×/ₐ-of-pbstb-Prop-is-Prop-aux regular-epi-is-ext
                                       ex𝔼.repi-pbof-stable
                                       pbof'
                                       pbof
                                       a-tr
                                       b-tr
                                       a×/b'
                                       qa-is-repi
                                       qb-is-repi
    open ×/ₐ-of-pbstb-Prop-is-Prop-aux2 epi-is-congr pbof' pbof a-tr b-tr a×/b' qa.uniq qb.uniq
    private
      module fst = is-regular-epi fstProp
      module snd = is-regular-epi sndProp
    ×/ar-is-epic : {h : || Hom a×/b.ul a'×/b'.ul ||}
                           → a'×/b'.π/₁ ∘ h ~ qa ∘ a×/b.π/₁ → a'×/b'.π/₂ ∘ h ~ qb ∘ a×/b.π/₂ → is-epic h
    ×/ar-is-epic pf1 pf2 = ×/arProp-cond pf1 pf2 fst.uniq snd.uniq
    ×/ar-pf = ×/ₐcanpf a-tr b-tr
             where open ×/ₐdef a'×/b' a×/b using (×/ₐcanpf)
    ×/ar-can : || Hom a×/b.ul a'×/b'.ul ||
    ×/ar-can = qa ×/ₐ qb [ a-tr , b-tr ]
          where open ×/ₐdef a'×/b' a×/b using (_×/ₐ_[_,_])
    ×/ar-can-epic : is-epic ×/ar-can
    ×/ar-can-epic = ×/ar-is-epic (a'×/b'.×/tr₁ ×/ar-pf) (a'×/b'.×/tr₂ ×/ar-pf)
  -- end ×/ₐ-of-repis-is-epi



  module exact-has-pbstable-image-fact {A B : Obj} (f : || Hom A B ||) where
    open has-pb→ker-are-eqr ex𝔼.haspb
    open has-pb→has-kerpair ex𝔼.haspb
    private
      module f×/f = is-kernel-pair (π/iskp f)
      module kerf = eqrel-over (π/kp-eqr/ f)    
    imgObf = Q.Ob (π/kp-eqr/ f)
    imgCf : || Hom A imgObf ||
    imgCf = Q.ar (π/kp-eqr/ f)    
    imgCf-is-repi : is-regular-epi imgCf
    imgCf-is-repi = record { rel-obj = kerf.relOb
                           ; rel₁ = kerf.r₁
                           ; rel₂ = kerf.r₂
                           ; coeq = iscoeq
                           }
                           where open is-exact-seq (ex-seq (π/kp-eqr/ f))
                                 open is-coeq iscoeq    
    imgMf : || Hom imgObf B ||
    imgMf = univ f f×/f.×/sqpf
          where open is-exact-seq (ex-seq (π/kp-eqr/ f))    
    imgTrf : imgMf ∘ imgCf ~ f
    imgTrf = univ-eq f×/f.×/sqpf
           where open is-exact-seq (ex-seq (π/kp-eqr/ f))
    imgMf-is-monic : is-monic imgMf
    imgMf-is-monic = π/₁~π/₂→mono (ex𝔼.pb-of imgMf imgMf) eqπ/
                   where module exf = is-exact-seq (ex-seq (π/kp-eqr/ f))
                         module kerMf = pullback-of-not (ex𝔼.pb-of imgMf imgMf)
                         open ×/ₐ-of-repis-is-epi f×/f.×/of (ex𝔼.pb-of imgMf imgMf)
                                                  imgTrf imgTrf imgCf-is-repi imgCf-is-repi
                                                  using (×/ar-can-epic)
                                                  renaming (×/ar-pf to qf×qf-pf)
                         module qf×qf = is-epic ×/ar-can-epic
                         open ecategory-aux-only 𝔼
                         eqπ/ : kerMf.π/₁ ~ kerMf.π/₂
                         eqπ/ = qf×qf.epi-pf (kerMf.×/tr₁ qf×qf-pf ⊙ exf.eq ⊙ kerMf.×/tr₂ qf×qf-pf ˢ)

    imgf-is-imgfact : is-img-fact imgTrf
    imgf-is-imgfact = repi-mono-is-img-fact imgTrf  imgCf-is-repi imgMf-is-monic

    imgf-data : img-fact-of f
    imgf-data = record
      { Ob = imgObf
      ; M = imgMf
      ; C = imgCf
      ; isimg = imgf-is-imgfact
      }

    imgf-is-pbstable : {C : Obj} {g : || Hom C B ||} (g×/f : pullback-of g f) (g×/mf : pullback-of g imgMf)
                       {pbQ : || Hom (pbof.ul g×/f) (pbof.ul g×/mf) ||} (pbtr : pbof.π/₁ g×/mf ∘ pbQ ~ pbof.π/₁ g×/f)
                         → img-fact-is-pb-stable imgf-data g×/f g×/mf pbtr
    imgf-is-pbstable {g = g} g×/f g×/mf {pbQ} pbtr = record
      { img-pb-stable = repi-mono-is-img-fact pbtr pbQ-is-repi g*imgMf-is-monic
      }
      where module g×/f = pullback-of-not g×/f
            module g×/mf = pullback-of-not g×/mf
            module Mf = is-monic imgMf-is-monic
            open ecategory-aux-only 𝔼
            pbQpf₂ = ~proof imgMf ∘ g×/mf.π/₂ ∘ pbQ        ~[ ass ⊙ ∘e r (g×/mf.×/sqpf ˢ) ⊙ assˢ ] /
                            g ∘  g×/mf.π/₁ ∘ pbQ           ~[ ∘e pbtr r ] /
                            g ∘ pbof.π/₁ g×/f              ~[ g×/f.×/sqpf ⊙ ∘e r (imgTrf ˢ) ⊙ assˢ ]∎
                            imgMf ∘ imgCf ∘ g×/f.π/₂ ∎
            pbQ-is-repi : is-regular-epi pbQ
            pbQ-is-repi = pres-rl (mkpb-sq (upper-is-pbsq imgTrf pbtr (Mf.mono-pf pbQpf₂)))
                                  imgCf-is-repi
                        where open is-pbsq-stable ex𝔼.repi-pbsq-stable
                              open lower-and-outer-so-upper g×/mf g×/f
            g*imgMf-is-monic : is-monic g×/mf.π/₁
            g*imgMf-is-monic = mono-pb-stable g×/mf imgMf-is-monic

  -- end exact-has-pbstable-image-fact
  

  -----------------------------------------------------
  -- Exact cat has pullback stable image factorisation
  -----------------------------------------------------

  exact-has-pbstb-img-fact : has-pb-stable-img-fact 𝔼
  exact-has-pbstb-img-fact = record
    { imgfact = record { img-of = imgf-data }
    ; pb-stb = λ pbsq-g*f pbsq-g*mf pbtr → imgf-is-pbstable _ pbsq-g*f pbsq-g*mf pbtr
    }
    where open exact-has-pbstable-image-fact

  -- Hence exact categories are regular...

  exact-is-regular//has-fl : is-regular//has-finlim ex𝔼.hasfl
  exact-is-regular//has-fl = record
    { pb-stb-imgfact = exact-has-pbstb-img-fact
    }
    where open exact-has-pbstable-image-fact
  
  exact-is-regular : is-regular 𝔼
  exact-is-regular = record
    { hasfl = ex𝔼.hasfl
    ; isreg/fl = exact-is-regular//has-fl
    }
      
  -- ... and enjoys the same properties.

  private
    module r𝔼 = is-regular//has-finlim exact-is-regular//has-fl
  open regular-cat-props exact-is-regular --public


  -- Exact cats have quotients of pseudo equivalence relations

  module exact-has-quot-peq-rel (peqR : Peq) where
    open Peq&prods ex𝔼.hasprd
    open ecategory-aux-only 𝔼
    private
      module R = Peq-aux peqR
    imgR : img-fact-of R.%01
    imgR = r𝔼.img-of R.%01
    private
      Lo×Lo : product-of R.Lo R.Lo
      Lo×Lo = ex𝔼.prd-of R.Lo R.Lo
      module Lo×Lo = product-of-not Lo×Lo
      module imgR = img-fact-of imgR
      imgCR-is-repi : is-regular-epi imgR.C
      imgCR-is-repi = imgC-is-repi R.%01
      module CR = is-regular-epi imgCR-is-repi
    r₁ r₂ : || Hom imgR.Ob R.Lo ||
    r₁ = Lo×Lo.π₁ ∘ imgR.M
    r₂ = Lo×Lo.π₂ ∘ imgR.M
    r-is-jm/ : is-jointly-monic/ (mkspan/ r₁ r₂)
    r-is-jm/ = <>monic→isjm/ Lo×Lo r r imgR.M-is-monic
    tr₁ = ~proof r₁ ∘ imgR.C    ~[ assˢ ⊙ ∘e imgR.tr r  ] /
                     Lo×Lo.π₁ ∘ R.%01    ~[ Lo×Lo.×tr₁ ]∎
                     R.%0 ∎
    tr₂ = ~proof r₂ ∘ imgR.C    ~[ assˢ ⊙ ∘e imgR.tr r  ] /
                     Lo×Lo.π₂ ∘ R.%01    ~[ Lo×Lo.×tr₂ ]∎
                     R.%1 ∎
    iseqr : is-eq-rel r₁ r₂
    iseqr = record
      { isjm/ = r-is-jm/
      ; isρ = record
            { ρ = imgR.C ∘ R.ρ
            ; ρ-ax₀ = ass ⊙ ∘e r tr₁ ⊙ R.ρ-ax₀
            ; ρ-ax₁ = ass ⊙ ∘e r tr₂ ⊙ R.ρ-ax₁
            }
      ; isσ = record
            { σ = σrel
            ; σ-ax₀ = ∘e r (Lo×Lo.×tr₂ {f = r₂} ˢ) ⊙ assˢ ⊙ ∘e (imgR.univ-tr σrel-monic σrel-comm) r
            ; σ-ax₁ = ∘e r (Lo×Lo.×tr₁ {g = r₁} ˢ) ⊙ assˢ ⊙ ∘e (imgR.univ-tr σrel-monic σrel-comm) r
            }
      ; τpb = ex𝔼.pb-of r₂ r₁
      ; isτ = record
            { τ = τrel
            ; τ-ax₀ = τrel-ax₀
            ; τ-ax₁ = τrel-ax₁
            }
      }
      where open Lo×Lo
            σrel-monic : is-monic Lo×Lo.< r₂ , r₁ >
            σrel-monic = isjm/→<>monic (jointly-monic-sym r-is-jm/) Lo×Lo
            σrel-comm = ~proof < r₂ , r₁ > ∘ imgR.C ∘ R.σ        ~[ ∘e r (Lo×Lo.<>ar~<>ˢ r r) ⊙ assˢ ] /
                               < π₂ , π₁ > ∘ imgR.M ∘ imgR.C ∘ R.σ  ~[ ∘e (ass ⊙ ∘e r imgR.tr ⊙ R.σ-ax) r ] /
                               < π₂ , π₁ > ∘ < R.%1 , R.%0 >     ~[ Lo×Lo.<>ar~<> ×tr₂ ×tr₁ ]∎
                               R.%01 ∎
            σrel = imgR.univ σrel-monic σrel-comm

            open wpullback-squares 𝔼
            module Rτpb = pullback-of-not (ex𝔼.pb-of R.%1 R.%0)
            module Rτwpb = wpullback-of-not R.τwpb
            module rτpb = pullback-of-not (ex𝔼.pb-of r₂ r₁)
            module CR×CR where
              open ×/ₐ-of-repis-is-repi (ex𝔼.pb-of r₂ r₁) (ex𝔼.pb-of R.%1 R.%0)
                                        tr₂ tr₁
                                        imgCR-is-repi imgCR-is-repi
                                        public
              open ×/ₐdef (ex𝔼.pb-of r₂ r₁) (ex𝔼.pb-of R.%1 R.%0) --public
              ×/arcan-pf = ×/ₐcanpf tr₂ tr₁
              open is-regular-epi ×/arcanProp public
            CR×CR : || Hom Rτpb.ul rτpb.ul ||
            CR×CR = CR×CR.×/arcan
            medτ : || Hom Rτpb.ul Rτwpb.ul ||
            medτ = Rτwpb.w⟨ Rτpb.π/₁ , Rτpb.π/₂ ⟩[ Rτpb.×/sqpf ]
            medτ₀ = R.%0 ∘ R.τ ∘  medτ ~[ ass ⊙ ∘e r R.τ-ax₀ ⊙ assˢ ⊙ ∘e (Rτwpb.w×/tr₁ Rτpb.×/sqpf) r
                    ] R.%0 ∘ Rτpb.π/₁
            medτ₁ = R.%1 ∘ R.τ ∘  medτ ~[ ass ⊙ ∘e r R.τ-ax₁ ⊙ assˢ ⊙ ∘e (Rτwpb.w×/tr₂ Rτpb.×/sqpf) r
                    ] R.%1 ∘ Rτpb.π/₂
            medτ₀₁ = R.%01 ∘ R.τ ∘  medτ ~[ Lo×Lo.<>ar~<> medτ₀ medτ₁ ]
                     < R.%0 ∘ Rτpb.π/₁ , R.%1 ∘ Rτpb.π/₂ >

            τrel-aux₁ = ~proof (r₁ ∘ rτpb.π/₁) ∘ CR×CR     ~[ assˢ ⊙ ∘e (rτpb.×/tr₁ CR×CR.×/arcan-pf) r ] /
                               r₁ ∘ imgR.C ∘ Rτpb.π/₁      ~[ ass ⊙ ∘e r tr₁ ]∎
                               R.%0 ∘ Rτpb.π/₁ ∎
            τrel-aux₂ = ~proof (r₂ ∘ rτpb.π/₂) ∘ CR×CR     ~[ assˢ ⊙ ∘e (rτpb.×/tr₂ CR×CR.×/arcan-pf) r ] /
                               r₂ ∘ imgR.C ∘ Rτpb.π/₂      ~[ ass ⊙ ∘e r tr₂ ]∎
                               R.%1 ∘ Rτpb.π/₂ ∎
            τrel-pf = imgR.Mpf (~proof
              imgR.M ∘ (imgR.C ∘ R.τ ∘  medτ) ∘ CR×CR.rel₁            ~[ ass ⊙ ∘e r (ass ⊙ ∘e r imgR.tr) ] /
              (R.%01 ∘ R.τ ∘  medτ) ∘ CR×CR.rel₁                     ~[ ∘e r medτ₀₁ ] /
              < R.%0 ∘ Rτpb.π/₁ , R.%1 ∘ Rτpb.π/₂ > ∘ CR×CR.rel₁     ~[ ∘e r (Lo×Lo.<>ar~<>ˢ τrel-aux₁ τrel-aux₂) ⊙ assˢ ] /
              < r₁ ∘ rτpb.π/₁ , r₂ ∘ rτpb.π/₂ > ∘ CR×CR ∘ CR×CR.rel₁  ~[ ∘e CR×CR.eq r ] /
              < r₁ ∘ rτpb.π/₁ , r₂ ∘ rτpb.π/₂ > ∘ CR×CR ∘ CR×CR.rel₂  ~[ ass ⊙ ∘e r (Lo×Lo.<>ar~<> τrel-aux₁ τrel-aux₂) ] /
              < R.%0 ∘ Rτpb.π/₁ , R.%1 ∘ Rτpb.π/₂ > ∘ CR×CR.rel₂      ~[ ∘e r (medτ₀₁ ˢ) ] /
              (R.%01 ∘ R.τ ∘  medτ) ∘ CR×CR.rel₂                      ~[ ∘e r (∘e r (imgR.tr ˢ) ⊙ assˢ) ⊙ assˢ ]∎
              imgR.M ∘ (imgR.C ∘ R.τ ∘ medτ) ∘ CR×CR.rel₂ ∎)

            τrel : || Hom rτpb.ul imgR.Ob ||
            τrel = CR×CR.univ (imgR.C ∘ R.τ ∘ medτ) τrel-pf
            τrel-ax₀ = CR×CR.epi-pf (~proof
              (r₁ ∘ τrel) ∘ CR×CR          ~[ assˢ ⊙ ∘e (CR×CR.univ-eq τrel-pf) r ⊙ ass ⊙ ∘e r tr₁ ] /
              R.%0 ∘ R.τ ∘ medτ          ~[ medτ₀ ⊙ ∘e r (tr₁ ˢ) ⊙ assˢ ] /
              r₁ ∘ imgR.C ∘ Rτpb.π/₁          ~[ ∘e (rτpb.×/tr₁ CR×CR.×/arcan-pf ˢ) r ⊙ ass ]∎
              (r₁ ∘ rτpb.π/₁) ∘ CR×CR ∎)            
            τrel-ax₁ = CR×CR.epi-pf (~proof
              (r₂ ∘ τrel) ∘ CR×CR           ~[ assˢ ⊙ ∘e (CR×CR.univ-eq τrel-pf) r ⊙ ass ⊙ ∘e r tr₂ ] /
              R.%1 ∘ R.τ ∘ medτ           ~[ medτ₁ ⊙ ∘e r (tr₂ ˢ) ⊙ assˢ ] /
              r₂ ∘ imgR.C ∘ Rτpb.π/₂           ~[ ∘e (rτpb.×/tr₂ CR×CR.×/arcan-pf ˢ) r ⊙ ass ]∎
              (r₂ ∘ rτpb.π/₂) ∘ CR×CR ∎)

    eqr/ : eqrel-over R.Lo
    eqr/ = record
      { relOb = imgR.Ob
      ; r₁ = r₁
      ; r₂ = r₂
      ; iseqrel = iseqr
      }

    QR = Q.Ob eqr/
    qR : || Hom R.Lo QR ||
    qR = Q.ar eqr/
    
    qR-iscoeq-rel : is-coeq r₁ r₂ qR
    qR-iscoeq-rel = iscoeq
                  where open is-exact-seq (ex-seq eqr/)
    private
      module qR = is-coeq qR-iscoeq-rel


    qR-iscoeq-psrel : is-coeq R.%0 R.%1 qR
    qR-iscoeq-psrel = record
      { eq = qR-coeq-psrel
      ; univ = λ f pf → qR.univ f (qR-univ-aux pf)
      ; univ-eq = λ pf → qR.univ-eq (qR-univ-aux pf)
      ; uniq = qR.uniq
      }
      where qR-coeq-psrel = ~proof qR ∘ R.%0            ~[ ∘e (tr₁ ˢ) r  ] /
                                   qR ∘ r₁ ∘ imgR.C     ~[ ass ⊙ ∘e r qR.eq ⊙ assˢ ] /
                                   qR ∘ r₂ ∘ imgR.C     ~[ ∘e tr₂ r ]∎
                                   qR ∘ R.%1 ∎
            qR-univ-aux : {B : Obj} {f : || Hom R.Lo B ||}
                             → f ∘ R.%0 ~ f ∘ R.%1 → f ∘ r₁ ~ f ∘ r₂
            qR-univ-aux {f = f} pf = CR.epi-pf (~proof
              (f ∘ r₁) ∘ imgR.C          ~[ assˢ ⊙ ∘e tr₁ r ] /
              f ∘ R.%0                   ~[ pf ] /
              f ∘ R.%1                   ~[ ∘e (tr₂ ˢ) r ⊙ ass ]∎
              (f ∘ r₂) ∘ imgR.C ∎)

    rel-is-eff : is-pb-square (mksq (mksq/ qR.eq))
    rel-is-eff = iskerpair
               where open is-exact-seq (ex-seq eqr/)
    
  -- end exact-has-quot-peq-rel


  -------------------------------------------------------------------
  -- Exact categories have quotients of pseudo equivlaence relations
  -------------------------------------------------------------------

  quot-peq-ob : Peq → Obj
  quot-peq-ob R = QR
                where open exact-has-quot-peq-rel R

  quot-peq-ar : (R : Peq) → || Hom (Peq.Lo R) (quot-peq-ob R) ||
  quot-peq-ar R = qR
                where open exact-has-quot-peq-rel R

  quot-peq-coeq : (R : Peq) → is-coeq (Peq.%0 R) (Peq.%1 R) (quot-peq-ar R)
  quot-peq-coeq R = qR-iscoeq-psrel
                  where open exact-has-quot-peq-rel R


  -- Morphisms of peq's induce arrows btw their quotients
  
  module peq-mor-to-quot-arr --(prdE : has-bin-products 𝔼)
                             {peqR peqS : Peq} (ff : Peq-mor peqR peqS)
                             where
    open has-bin-products ex𝔼.hasprd using (prd-of)
    open Peq&prods ex𝔼.hasprd
    private
      module R = Peq-aux peqR
      module S = Peq-aux peqS
      module ff = Peq-mor-aux ff

    QR QS : Obj
    QR = quot-peq-ob peqR
    QS = quot-peq-ob peqS
    qR : || Hom R.Lo QR ||
    qR = quot-peq-ar peqR
    qS : || Hom S.Lo QS ||
    qS = quot-peq-ar peqS
    private
      module qR = is-coeq (quot-peq-coeq peqR)
      module qS = is-coeq (quot-peq-coeq peqS)

    qf : || Hom QR QS ||
    qf = qR.univ (qS ∘ ff.lo) qf-pf
       where open ecategory-aux-only 𝔼
             qf-pf = ~proof (qS ∘ ff.lo) ∘ R.%0         ~[ assˢ ⊙ ∘e (ff.cmptb₀ ˢ) r ] /
                            qS ∘ S.%0 ∘ ff.hi           ~[ ass ⊙ ∘e r qS.eq ⊙ assˢ ] /
                            qS ∘ S.%1 ∘ ff.hi           ~[ ∘e ff.cmptb₁ r ⊙ ass ]∎
                            (qS ∘ ff.lo) ∘ R.%1 ∎

  -- end peq-mor-to-quot-arr


  quot-peq-morph : {R S : Peq} (ff : Peq-mor R S)
                      → || Hom (quot-peq-ob R) (quot-peq-ob S) ||
  quot-peq-morph ff = qf
                    where open peq-mor-to-quot-arr ff

-- end exact-cat-props-only


module exact-cat-props {𝔼 : ecategory} (ex : is-exact 𝔼) where
  open exact-cat-props-only ex public
  open regular-cat-props exact-is-regular public
-- end exact-cat-prop


module exact-cat-d&p {𝔼 : ecategory} (ex : is-exact 𝔼) where
  open is-exact ex public
  open exact-cat-props ex public
--end exact-cat-d&p


--------------------------------
-- Exact categories are regular
--------------------------------

exact2reg : {𝔼 : ecategory} → is-exact 𝔼 → is-regular 𝔼
exact2reg excat = exact-is-regular
                where open exact-cat-props excat

