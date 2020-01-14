
-- disable the K axiom:

{-# OPTIONS --without-K #-}

-- Agda version 2.5.4.1

module ecats.basic-props.epi&mono where

open import ecats.basic-defs.ecat-def&not
open import ecats.basic-defs.all-arrows
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


  mono-is-congr : is-ecat-congr ℂ is-monic
  mono-is-congr = mkis-ecat-congr
    (mkis-hom-ext is-monic λ pfeq pfm → record { mono-pf = λ pf → mono-pf pfm (∘e r pfeq ⊙ pf ⊙ ∘e r (pfeq ˢ)) })
    (record { ∘c = λ gm fm → record { mono-pf = λ pf → mono-pf fm (mono-pf gm (ass ⊙ pf ⊙ assˢ)) } })
    where open is-monic

{-
  mono-ext : {A B : Obj} {m m' : || Hom A B ||} → m ~ m' → is-monic m → is-monic m'
  mono-ext pfeq pfm = record
    { mono-pf = λ pf → mono-pf (∘e r pfeq ⊙ pf ⊙ ∘e r (pfeq ˢ))
    }
    where open is-monic pfm


  mono-cmp : {A B C : Obj} {m : || Hom A B ||} {m' : || Hom B C ||} {m'' : || Hom A C ||}
                → m' ∘ m ~ m'' → is-monic m → is-monic m' → is-monic m''
  mono-cmp pftr pfm pfm' = record
    { mono-pf = λ pf → mono-pfm (mono-pfm' (ass ⊙ ∘e r pftr ⊙ pf ⊙ ∘e r (pftr ˢ) ⊙ assˢ))
    }
    where open is-monic pfm renaming (mono-pf to mono-pfm)
          open is-monic pfm' renaming (mono-pf to mono-pfm')
-}


  mono-tr : {A B C : Obj} {m : || Hom A B ||} {m' : || Hom B C ||} {m'' : || Hom A C ||}
                → m' ∘ m ~ m'' → is-monic m'' → is-monic m
  mono-tr {A} {m = m} {m'} {m''} pftr pfm'' = record
    { mono-pf = λ {_} {g} {g'} pf → mono-pf (~proof m'' ∘ g       ~[ ∘e r (pftr ˢ) ⊙ assˢ ] /
                                                     m' ∘ m ∘ g    ~[ ∘e pf r ] /
                                                     m' ∘ m ∘ g'   ~[ ass ⊙ ∘e r pftr ]∎
                                                     m'' ∘ g' ∎)
    }
    where open is-monic pfm''
          m''eq : {C' : Obj} {g g' : || Hom C' A ||} → m ∘ g ~ m ∘ g' → m'' ∘ g ~ m'' ∘ g'
          m''eq {g = g} {g'} pf = ~proof m'' ∘ g       ~[ ∘e r (pftr ˢ) ⊙ assˢ ] /
                                         m' ∘ m ∘ g    ~[ ∘e pf r ] /
                                         m' ∘ m ∘ g'   ~[ ass ⊙ ∘e r pftr ]∎
                                         m'' ∘ g' ∎
                
  
  mono-pb-stable : {A B C : Obj} {m : || Hom A B ||} {f : || Hom C B ||} (pbof : pullback-of f m)
                      → is-monic m → is-monic (pbof.π/₁ pbof)
  mono-pb-stable pbof pfm = record
    { mono-pf = λ {D} {g} {g'} pfc → ×/uq pfc (mono-pf (ass ⊙ ∘e r (×/sqpf ˢ) ⊙ assˢ
                                                         ⊙ ∘e pfc r ⊙ ass ⊙ ∘e r ×/sqpf ⊙ assˢ))
    }
    where open pullback-of pbof
          open is-monic pfm

  mono-pbof-stb : is-pbof-stable is-monic
  mono-pbof-stb = record
    { pres-rl = mono-pb-stable
    }

  mono-pbsq-stb : is-pbsq-stable is-monic
  mono-pbsq-stb = pbof-stb→pbsq-stb mono-pbof-stb 



  jointly-monic-sym : {O1 O2 : Obj} {jmsp : span/ O1 O2}
                          → is-jointly-monic/ jmsp → is-jointly-monic/ (jmsp ²¹)
  jointly-monic-sym {jmsp = jmsp} isjm = record
    { jm-pf = λ pf₂ pf₁ → jm-pf pf₁ pf₂
    }
    where open span/ jmsp
          open is-jointly-monic/ isjm


  jointly-monic-tr : {O1 O2 : Obj} {jmsp sp : span/ O1 O2} {f : || Hom (sp/.O12 jmsp) (sp/.O12 sp) ||}
  --{O1 O2 O12 A : Obj} {f : || Hom A O12 ||} {a1 : || Hom O12 O1 ||} {a2 : || Hom O12 O2 ||}
    --                 {m1 : || Hom A O1 ||} {m2 : || Hom A O2 ||}
                       → sp/.a1 sp ∘ f ~ sp/.a1 jmsp → sp/.a2 sp ∘ f ~ sp/.a2 jmsp → is-jointly-monic/ jmsp --(mkspan m1 m2)
                         → is-monic f
  jointly-monic-tr tr1 tr2 isjm/ = record
    { mono-pf = λ pf → jm-pf (∘e r (tr1 ˢ) ⊙ assˢ ⊙ ∘e pf r ⊙ ass ⊙ ∘e r tr1)
                                                          (∘e r (tr2 ˢ) ⊙ assˢ ⊙ ∘e pf r ⊙ ass ⊙ ∘e r tr2)
    }
    where open is-jointly-monic/ isjm/


  monos∘jm-is-jm : {O1 O2 O1' O2' : Obj} {sp : span/ O1' O2'} {jm₁ : || Hom (sp/.O12 sp) O1 ||} {jm₂ : || Hom (sp/.O12 sp) O2 ||}
                   {m₁ : || Hom O1 O1' ||} {m₂ : || Hom O2 O2' ||}
                       → is-jointly-monic/ (mkspan/ jm₁ jm₂) → is-monic m₁ → is-monic m₂
                         → m₁ ∘ jm₁ ~ sp/.a1 sp → m₂ ∘ jm₂ ~ sp/.a2 sp
                           → is-jointly-monic/ sp
  monos∘jm-is-jm {sp = sp} {jm₁} {jm₂} {m₁} {m₂} jmsp m₁m m₂m tr₁ tr₂ = record
    { jm-pf = λ pf₁ pf₂ → jm-pf (m₁pf (ass ⊙ ∘e r tr₁ ⊙ pf₁ ⊙ ∘e r (tr₁ ˢ) ⊙ assˢ))
                                 (m₂pf (ass ⊙ ∘e r tr₂ ⊙ pf₂ ⊙ ∘e r (tr₂ ˢ) ⊙ assˢ))
    }
    where open is-jointly-monic/ jmsp
          open is-monic m₁m renaming (mono-pf to m₁pf)
          open is-monic m₂m renaming (mono-pf to m₂pf)
                                    

  split-mono-is-monic : {A B : Obj} {f : || Hom A B ||} {linv : || Hom B A ||}
                           → linv ∘ f ~ idar A → is-monic f
  split-mono-is-monic {f = f} {linv} linv-pf = record
    { mono-pf = λ {C} {g} {g'} pf → ~proof g              ~[ lidggˢ r linv-pf ⊙ assˢ ] /
                                            linv ∘ f ∘ g    ~[ ∘e pf r ] /
                                            linv ∘ f ∘ g'   ~[ ass ⊙ lidgg r linv-pf ]∎
                                            g' ∎
    }


    
  isjm/→<>monic : {O1 O2 : Obj} {jmsp : span/ O1 O2} (isjm/ : is-jointly-monic/ jmsp) (×sp : product-of O1 O2)
                      → is-monic (×of.<_,_> ×sp (sp/.a1 jmsp) (sp/.a2 jmsp))
                      --< sp/.a1 jmsp , sp/.a2 jmsp >[ mk× (×of.×isprd ×sp) ]
--                  {×sp : span/ O1 O2} (is× : is-product (mkspan-c ×sp))
  isjm/→<>monic {jmsp = jmsp} isjm ×sp = record
    { mono-pf = λ {A} {g} {g'} pf<> → jm-pf (~proof jm.a1 ∘ g                     ~[ ∘e r (×tr₁ˢ {g = jm.a2}) ⊙ assˢ ] /
                                                     π₁ ∘ < jm.a1 , jm.a2 > ∘ g    ~[ ∘e pf<> r ] /
                                                     π₁ ∘ < jm.a1 , jm.a2 > ∘ g'   ~[ ass ⊙ ∘e r ×tr₁ ]∎
                                                     jm.a1 ∘ g' ∎)
                                             (~proof jm.a2 ∘ g                     ~[ ∘e r (×tr₂ˢ {f = jm.a1}) ⊙ assˢ ] /
                                                     π₂ ∘ < jm.a1 , jm.a2 > ∘ g    ~[ ∘e pf<> r ] /
                                                     π₂ ∘ < jm.a1 , jm.a2 > ∘ g'   ~[ ass ⊙ ∘e r ×tr₂ ]∎
                                                     jm.a2 ∘ g' ∎)
    }
    where open is-jointly-monic/ isjm
          open product-of-not ×sp
          module jm = span/ jmsp
    

  <>monic→isjm/-sp : {O1 O2 : Obj} {sp/ : span/ O1 O2} (×sp : product-of O1 O2)
                         → is-monic (×of.<_,_> ×sp (sp/.a1 sp/) (sp/.a2 sp/)) → is-jointly-monic/ sp/
  <>monic→isjm/-sp {sp/ = spjm} ×sp ism = record
    { jm-pf = λ {C} {h} {h'} pf1 pf2 → mono-pf (<>ar~<> pf1 pf2 ⊙ <>distˢ h')
    }
    where open is-monic ism
          open product-of-not ×sp


  <>monic→isjm/-ar : {O1 O2 : Obj} (×sp : product-of O1 O2)
                      {A : Obj} {f : || Hom A (×of.O12 ×sp) ||}
                         → is-monic f → is-jointly-monic/ (mkspan/ (×of.π₁ ×sp ∘ f) (×of.π₂ ×sp ∘ f))
  <>monic→isjm/-ar ×sp {f = f} ism = record
    { jm-pf = λ {C} {h} {h'} pf1 pf2 → ism.mono-pf (×sp.×uq (ass ⊙ pf1 ⊙ assˢ) (ass ⊙ pf2 ⊙ assˢ))
    }
    where module ×sp = product-of-not ×sp
          module ism = is-monic ism


  <>monic→isjm/ : {O1 O2 : Obj} {sp/ : span/ O1 O2} (×sp : product-of O1 O2)
                   {f : || Hom (sp/.O12 sp/) (×of.O12 ×sp) ||}
                     → ×of.π₁ ×sp ∘ f ~ sp/.a1 sp/ → ×of.π₂ ×sp ∘ f ~ sp/.a2 sp/ → is-monic f
                       → is-jointly-monic/ sp/
  <>monic→isjm/ {sp/ = spjm} ×sp {f} tr1 tr2 ism = record
    { jm-pf = λ {C} {h} {h'} pf1 pf2 → mono-pf (×uq (ass ⊙ ∘e r tr1 ⊙ pf1 ⊙ ∘e r (tr1 ˢ) ⊙ assˢ)
                                                     (ass ⊙ ∘e r tr2 ⊙ pf2 ⊙ ∘e r (tr2 ˢ) ⊙ assˢ))
    }
    where open is-monic ism
          open product-of-not ×sp


  πs-are-jointly-monic/ : (prdsp : bin-product) → is-jointly-monic/ (mkspan/ (prd.π₁ prdsp) (prd.π₂ prdsp))
  πs-are-jointly-monic/ prdsp = record
    { jm-pf = ×uq
    }
    where open bin-product prdsp    


  π/s-are-jointly-monic/ : (pbsq : pb-square) → is-jointly-monic/ (mkspan/ (pbsq.π/₁ pbsq) (pbsq.π/₂ pbsq))
  π/s-are-jointly-monic/ pbsq = record
    { jm-pf = ×/uq
    }
    where open pb-square pbsq


  <π/s>-is-monic : (pbsq : pb-square) (×sp : product-of (pbsq.dl pbsq) (pbsq.ur pbsq))
                         → is-monic (×of.<_,_> ×sp (pbsq.π/₁ pbsq) (pbsq.π/₂ pbsq))
  <π/s>-is-monic pbsq ×sp = isjm/→<>monic (π/s-are-jointly-monic/ pbsq) ×sp


  π/₁~π/₂→mono : {A B : Obj} {f : || Hom A B ||} (pb : pullback-of f f)
  --{span : square/cosp f f} → is-pb-square (mksq span)
                        → pbof.π/₁ pb ~ pbof.π/₂ pb → is-monic f
  π/₁~π/₂→mono {A} {B} {f} pb pfeq = record
    { mono-pf = λ {_} {g} {g'} pf → ~proof g                         ~[ ×/tr₁ pf ˢ ] /
                                            π/₁ ∘ ⟨ g , g' ⟩[ pf ]   ~[ ∘e r pfeq ] /
                                            π/₂ ∘ ⟨ g , g' ⟩[ pf ]   ~[ ×/tr₂ pf ]∎
                                            g' ∎
    }
    where open pullback-of pb


  π//₁~π//₂→jm/ :  {O1 O2 : Obj} {sp : span/ O1 O2} (bwofsp : bow-of sp sp)
                      → bwof.π//₁ bwofsp ~ bwof.π//₂ bwofsp → is-jointly-monic/ sp
  π//₁~π//₂→jm/ {sp = sp} bwofsp π//₁~π//₂ = record
    { jm-pf = λ {_} {h} {h'} pf1 pf2 → 
            ~proof h                                 ~[ tr₁ pf1 pf2 ˢ ] /
                   π//₁ ∘ ⟨ h , h' ⟩[ pf1 , pf2 ]     ~[ ∘e r π//₁~π//₂ ] /
                   π//₂ ∘ ⟨ h , h' ⟩[ pf1 , pf2 ]     ~[ tr₂ pf1 pf2 ]∎
                   h' ∎
    }
    where open bow-of bwofsp


  -- same as above but with pb and eql instead
  jm/-via-pb+eq : {O1 O2 : Obj} {sp : span/ O1 O2} (kpO1 : pullback-of (sp/.a1 sp) (sp/.a1 sp))
                  (eqlO2 : equaliser-of (sp/.a2 sp ∘ pbof.π/₁ kpO1) (sp/.a2 sp ∘ pbof.π/₂ kpO1))
                    → pbof.π/₁ kpO1 ∘ eqlof.eqlar eqlO2 ~ pbof.π/₂ kpO1 ∘ eqlof.eqlar eqlO2
                      → is-jointly-monic/ sp
  jm/-via-pb+eq {sp = sp} kpO1 eqlO2 pf = record
    { jm-pf = λ {_} {h} {h'} pf1 pf2 → 
            ~proof h                                                         ~[ ×/tr₁ pf1 ˢ ⊙ ∘e (eqltr (|eql-pf pf1 pf2) ˢ) r ] /
                   π/₁ ∘ eqlar ∘ ⟨ h , h' ⟩[ pf1 ] |eql[ |eql-pf pf1 pf2 ]    ~[ ass ⊙ ∘e r pf ⊙ assˢ ] /
                   π/₂ ∘ eqlar ∘ ⟨ h , h' ⟩[ pf1 ] |eql[ |eql-pf pf1 pf2 ]    ~[ ∘e (eqltr (|eql-pf pf1 pf2)) r ⊙ ×/tr₂ pf1 ]∎
                   h' ∎
    }
    where open span/ sp
          open equaliser-of eqlO2
          open pullback-of-not kpO1
          |eql-pf : {A : Obj} {h h' : || Hom A O12 ||} (pf1 : a1 ∘ h ~ a1 ∘ h')
                       → a2 ∘ h ~ a2 ∘ h' → (a2 ∘ π/₁) ∘ ⟨ h , h' ⟩[ pf1 ] ~ (a2 ∘ π/₂) ∘ ⟨ h , h' ⟩[ pf1 ]
          |eql-pf pf1 pf2 = assˢ ⊙ ∘e (×/tr₁ pf1) r ⊙ pf2 ⊙ ∘e (×/tr₂ pf1 ˢ) r ⊙ ass

{-
  -- the following two terms are pointless: one only needs commutativities, no universal property

  jm/-via-pb+eq-conv : {O1 O2 : Obj} {sp : span/ O1 O2} (kpO1 : pullback-of (sp/.a1 sp) (sp/.a1 sp))
                       (eqlO2 : equaliser-of (sp/.a2 sp ∘ pbof.π/₁ kpO1) (sp/.a2 sp ∘ pbof.π/₂ kpO1))
                         → is-jointly-monic/ sp
                           → pbof.π/₁ kpO1 ∘ eqlof.eqlar eqlO2 ~ pbof.π/₂ kpO1 ∘ eqlof.eqlar eqlO2
  jm/-via-pb+eq-conv kpO1 eqlO2 isjm = jm-pf (ass ⊙ ∘e r ×/sqpf ⊙ assˢ ) (ass ⊙ eqleq ⊙ assˢ)
                                     where open equaliser-of eqlO2
                                           open pullback-of-not kpO1
                                           open is-jointly-monic/ isjm


  jm/-via-wpb+weq-conv : {O1 O2 : Obj} {sp : span/ O1 O2} (wkpO1 : wpullback-of (sp/.a1 sp) (sp/.a1 sp))
                         (weqlO2 : wequaliser-of (sp/.a2 sp ∘ wpbof.wπ/₁ wkpO1) (sp/.a2 sp ∘ wpbof.wπ/₂ wkpO1))
                           → is-jointly-monic/ sp
                             → wpbof.wπ/₁ wkpO1 ∘ weqlof.weqlar weqlO2 ~ wpbof.wπ/₂ wkpO1 ∘ weqlof.weqlar weqlO2
  jm/-via-wpb+weq-conv wkpO1 weqlO2 isjm = jm-pf (ass ⊙ ∘e r w×/sqpf ⊙ assˢ ) (ass ⊙ weqleq ⊙ assˢ)
                                         where open wequaliser-of weqlO2
                                               open wpullback-of wkpO1
                                               open is-jointly-monic/ isjm
-}

  idiskp→mono : {A B : Obj} {m : || Hom A B ||}
                 {idkp₁ idkp₂ : || Hom A A ||} {kpeq : m ∘ idkp₁ ~ m ∘ idkp₂}
                   → is-pb-square (mksq (mksq/ kpeq)) → idkp₁ ~ idar A → idkp₂ ~ idar A
                     → is-monic m
  idiskp→mono ispb id1 id2 = π/₁~π/₂→mono (mkpb-of ispb) (id1 ⊙ id2 ˢ)
  


  mono→idiskp : {A B : Obj} {m : || Hom A B ||} → is-monic m
                   → is-pb-square (mksq (mksq/ (rid {f = m} ⊙ ridˢ {f = m})))
  mono→idiskp ism = record
    { ⟨_,_⟩[_] = λ h k pf → h
    ; ×/tr₁ = λ {_} {h} pf → lid
    ; ×/tr₂ = λ pf → lidgen (mono-pf pf)
    ; ×/uq = λ {_} {h} {h'} pf₁ pf₂ → lidˢ ⊙ pf₁ ⊙ lid
    }
    where open is-monic ism    


  idiskpsp→jm/ : {O1 O2 : Obj} {sp/ : span/ O1 O2}
                  {kpsp₁ kpsp₂ : || Hom (sp/.O12 sp/) (sp/.O12 sp/) ||}
                  {sqpf₁ : sp/.a1 sp/ ∘ kpsp₁ ~ sp/.a1 sp/ ∘ kpsp₂} {sqpf₂ : sp/.a2 sp/ ∘ kpsp₁ ~ sp/.a2 sp/ ∘ kpsp₂}
                        → is-bow sqpf₁ sqpf₂ → kpsp₁ ~ idar (sp/.O12 sp/) → kpsp₂ ~ idar (sp/.O12 sp/)
                          → is-jointly-monic/ sp/
  idiskpsp→jm/ {sp/ = sp/} isbw pf₁ pf₂ = π//₁~π//₂→jm/ (record { is-bw = isbw }) (pf₁ ⊙ pf₂ ˢ)


  jm/→idiskpsp/ : {O1 O2 : Obj} {sp/ : span/ O1 O2}
                      → is-jointly-monic/ sp/ → is-bow (ridgen (ridˢ {f = sp/.a1 sp/}))
                                                         (ridgen (ridˢ {f = sp/.a2 sp/}))
  jm/→idiskpsp/ {sp/ = sp/} isjm/ = record
    { ⟨_,_⟩[_,_] = λ f₁ f₂ _ _ → f₁
    ; tr₁ = λ {f₁} {f₂} _ _ → lid
    ; tr₂ = λ pf₁ pf₂ → lidgen (jm-pf pf₁ pf₂)
    ; uq = λ {_} {h} {h'} pf₁ pf₂ → lidˢ ⊙ pf₁ ⊙ lid
    }
    where open is-jointly-monic/ isjm/




  idar-is-iso : (A : Obj) → is-iso (idar A)
  idar-is-iso A = mkis-iso (mkis-iso-pair (lid {f = idar A}) (rid {f = idar A}))
  
  
  iso-is-monic : {A B : Obj} {f : || Hom A B ||} → is-iso f → is-monic f
  iso-is-monic fiso = record { mono-pf = λ pfeq → lidggˢ r iddom ⊙ assˢ ⊙ ∘e pfeq r ⊙ ass ⊙ lidgg r iddom }
                    where open is-iso fiso


  monic-cover-is-iso : {A B : Obj} {f : || Hom A B ||} → is-monic f
                          → is-cover f → is-iso f
  monic-cover-is-iso {f = f} mon cov = cov-pf rid mon
                                     where open is-cover cov


  

  epi-is-congr : is-ecat-congr ℂ is-epic
  epi-is-congr = mkis-ecat-congr
    (mkis-hom-ext is-epic λ pfeq fepi → record
                     { epi-pf = λ pfm → epi-pf fepi (∘e pfeq r ⊙ pfm ⊙ ∘e (pfeq ˢ) r ) })
    (record { ∘c = λ gepi fepi → record
                 { epi-pf = λ pfeq → epi-pf gepi (epi-pf fepi (assˢ ⊙ pfeq ⊙ ass))
                 } })
    where open is-epic

  epi-is-transportable : iso-transportable is-epic
  epi-is-transportable = record
    { congr = epi-is-congr
    ; on-iso = λ f fiso → record
             { epi-pf = λ pfeq → ridggˢ r (idcod fiso) ⊙ ass ⊙ ∘e r pfeq
                                 ⊙ assˢ ⊙ ridgg r (idcod fiso)
             }
    }
    where open is-epic
          open is-iso


  strepi-is-congr : is-ecat-congr ℂ is-strong-epi
  strepi-is-congr = mkis-ecat-congr
    (mkis-hom-ext is-strong-epi λ {f} {f'} eq fstr → record
                     { lift = λ pfc pfm → lift fstr (∘e eq r ⊙ pfc) pfm 
                     ; tr-up = λ pfc pfm → ∘e (eq ˢ) r ⊙ tr-up fstr (∘e eq r ⊙ pfc) pfm
                     ; tr-down = λ pfc pfm → tr-down fstr (∘e eq r ⊙ pfc) pfm
                     })
    (record { ∘c = λ gstr fstr → record
                 { lift = lift-cmp gstr fstr
                 ; tr-up = λ pfc pfm → ass ⊙ ∘e r (tr-up gstr (tr-down fstr (assˢ ⊙ pfc) pfm ˢ) pfm)
                                       ⊙ tr-up fstr (assˢ ⊙ pfc) pfm
                 ; tr-down = λ pfc pfm → tr-down gstr (tr-down fstr (assˢ ⊙ pfc) pfm ˢ) pfm
                 } })
    where open is-strong-epi
          lift-cmp : {A B C D D' : Obj} {g : || Hom B C ||} {f : || Hom A B ||} → is-strong-epi g → is-strong-epi f
                        → {up : || Hom A D ||} {down : || Hom C D' ||} {m : || Hom D D' ||}
                          → down ∘ g ∘ f ~ m ∘ up → is-monic m → || Hom C D ||
          lift-cmp gstr fstr pfc pfm = lift gstr {up = lift fstr (assˢ ⊙ pfc) pfm} (tr-down fstr (assˢ ⊙ pfc) pfm ˢ) pfm


  regular-epi-is-ext : is-hom-ext ℂ is-regular-epi
  regular-epi-is-ext = mkis-hom-ext is-regular-epi λ eq repi → record
                     { rel₁ = re.rel₁ repi
                     ; rel₂ = re.rel₂ repi
                     ; coeq = record
                       { eq = ∘e r (eq ˢ) ⊙ re.eq repi ⊙ ∘e r eq
                       ; univ = re.univ repi
                       ; univ-eq = λ pf → ∘e (eq ˢ) r ⊙ re.univ-eq repi pf
                       ; uniq = epicng.trnsp eq (re.uniq repi)
                       }
                     }
                     where module re = is-regular-epi
                           module epicng where
                             open is-ecat-congr epi-is-congr
                             open is-hom-ext ext hiding (isext) public


  cover-is-ext : is-hom-ext ℂ is-cover
  cover-is-ext = mkis-hom-ext is-cover λ eq fc → record
               { cov-pf = λ tr pfm → cov-pf fc (tr ⊙ eq ˢ) pfm
               }
               where open is-cover


  cover-triang : (tr : comm-triang) → is-cover (comm-triang.a13 tr) → is-cover (comm-triang.a23 tr)
  cover-triang tr a13-cov = record
    { cov-pf = λ {C} {p} {m} tr-pf m-pf → cov-pf {p = p ∘ a12}
                                                  (ass ⊙ ∘e r tr-pf ⊙ pftr)
                                                  m-pf
    }
    where open is-cover a13-cov
          open comm-triang tr


  strong-epi-is-cover : {A B : Obj} {f : || Hom A B ||} → is-strong-epi f → is-cover f
  strong-epi-is-cover {A} {B} {f} strepi = record
    { cov-pf = λ {C} {p} {m} com mon → record
             { invf = lift (lid  ⊙ com ˢ) mon
             ; isisopair = record
                     { iddom = mono-pf mon (ass ⊙ ∘e r (tr-down (lid  ⊙ com ˢ) mon)
                                          ⊙ lid ⊙ ridˢ)
                     ; idcod = tr-down (lid ⊙ com ˢ) mon
                     }
             }
    }
    where open is-strong-epi strepi
          open is-monic


  repi-is-epic : {A B : Obj} {f : || Hom A B ||} → is-regular-epi f → is-epic f
  repi-is-epic repi = uniq
                    where open is-regular-epi repi


  repi-is-strong : {A B : Obj} {f : || Hom A B ||} → is-regular-epi f → is-strong-epi f
  repi-is-strong {A} {B} {f} frepi = record
    { lift = λ {C} {D} {up} {down} {m} pfc pfm → frepi.univ up (l-pf pfc pfm)
    ; tr-up = λ pfc pfm → frepi.univ-eq (l-pf pfc pfm)
    ; tr-down = λ pfc pfm → frepi.epi-pf (assˢ ⊙ ∘e (frepi.univ-eq (l-pf pfc pfm)) r ⊙ pfc ˢ)
    }
    where module frepi = is-regular-epi frepi
          open is-monic
          l-pf : {C D : Obj} {up : || Hom A C ||} {down : || Hom B D ||} {m : || Hom C D ||}
                      (pfc : down ∘ f ~ m ∘ up) (pfm : is-monic m)
                        → up ∘ frepi.rel₁ ~ up ∘ frepi.rel₂
          l-pf pfc pfm = mono-pf pfm (ass ⊙ ∘e r (pfc ˢ) ⊙ assˢ ⊙ ∘e frepi.eq r ⊙ ass ⊙ ∘e r pfc ⊙ assˢ)


  repi-is-cover : {A B : Obj} {f : || Hom A B ||} → is-regular-epi f → is-cover f
  repi-is-cover {A} {B} {f = f} repi = record
    { cov-pf = λ {C} {p} {m} com mon → record
             { invf = repi.univ p (p-coeq com mon)
             ; isisopair = record
                     { iddom = mono-pf mon (ass ⊙ ∘e r (idB com mon) ⊙ lidgen ridˢ )
                     ; idcod = idB com mon
                     }
             }
    }
    where module repi = is-regular-epi repi
          open is-monic
          p-coeq : {C : Obj} → {p : || Hom A C ||} → {m : || Hom C B ||} → m ∘ p ~ f
                      → is-monic m → p ∘ repi.rel₁ ~ p ∘ repi.rel₂
          p-coeq {C} {p} {m} com mon = mono-pf mon (ass ⊙ ∘e r com ⊙ repi.eq ⊙ ∘e r (com ˢ) ⊙ assˢ)
          idB :  {C : Obj} → {p : || Hom A C ||} → {m : || Hom C B ||}
                    → (com : m ∘ p ~ f) → (mon : is-monic m)
                      → m ∘ repi.univ p (p-coeq com mon) ~ idar B
          idB com mon = repi.epi-pf (assˢ ⊙ ∘e (repi.univ-eq (p-coeq com mon)) r ⊙ lidgenˢ com)


  split-epi-is-epic : {A B : Obj} {f : || Hom A B ||} → is-split-epi f → is-epic f
  split-epi-is-epic {A} {B} {f = f} sepi = record
    { epi-pf = λ pfeq → ridggˢ r rinv-ax ⊙ ass ⊙ ∘e r pfeq ⊙ assˢ ⊙ ridgg r rinv-ax
    }
    where open is-split-epi sepi


  split-epi-is-strong : {A B : Obj} {f : || Hom A B ||} → is-split-epi f → is-strong-epi f
  split-epi-is-strong {A} {B} {f = f} fsepi = record
    { lift = l
    ; tr-up = λ pfc pfm → mono-pf pfm (ass ⊙ ∘e r (ass ⊙ ∘e r (pfc ˢ) ⊙ assˢ ⊙ ridgg r rinv-ax)
                                             ⊙ pfc )
    ; tr-down = λ pfc pfm → ass ⊙ ∘e r (pfc ˢ) ⊙ assˢ ⊙ ridgg r rinv-ax
    }
    where open is-split-epi fsepi
          open is-monic
          l : {C D : Obj} {up : || Hom A C ||} {down : || Hom B D ||} {m : || Hom C D ||}
                 → down ∘ f ~ m ∘ up → is-monic m → || Hom B C ||
          l {up = up} pfc pfm = up ∘ rinv


  split-epi-is-repi : {A B : Obj} {f : || Hom A B ||} → is-split-epi f → is-regular-epi f
  split-epi-is-repi {A} {B} {f = f} sepi = record
    { rel-obj = A
    ; rel₁ = rinv ∘ f
    ; rel₂ = idar A
    ; coeq = record
               { eq = ass ⊙ lidgg ridˢ rinv-ax
               ; univ = λ g _ → g ∘ rinv
               ; univ-eq = λ pf → assˢ ⊙ pf ⊙ rid
               ; uniq = split-epi-is-epic sepi
               }
    }
    where open is-split-epi sepi
  

  split-epi-is-cover : {A B : Obj} {f : || Hom A B ||}
                     → is-split-epi f → is-cover f
  split-epi-is-cover {A} {B} {f = f} sepi = record
    { cov-pf = λ {C} {p} {m} pfc pfm → record
             { invf = p ∘ rinv
             ; isisopair = record
                         { iddom = mono-pf pfm (ass ⊙ lidgg r (ass ⊙ ∘e r pfc ⊙ rinv-ax) ⊙ ridˢ)
                         ; idcod = ass ⊙ ∘e r pfc ⊙ rinv-ax
                         }
             }
    }
    where open is-split-epi sepi
          open is-monic

  iso-is-split-epi : {A B : Obj} {f : || Hom A B ||} → is-iso f → is-split-epi f
  iso-is-split-epi f⁻¹ = record
    { rinv = invf
    ; rinv-ax = idcod
    }
    where open is-iso f⁻¹


  iso-is-epic : {A B : Obj} {f : || Hom A B ||} → is-iso f → is-epic f
  iso-is-epic isof = split-epi-is-epic (iso-is-split-epi isof)


  monic-sepi-is-iso : {A B : Obj} {f : || Hom A B ||} → is-monic f
                         → is-split-epi f → is-iso f
  monic-sepi-is-iso {A} {B} {f = f} mon sepi = monic-cover-is-iso mon (split-epi-is-cover sepi)


  cover-is-epi : has-equalisers ℂ → {A B : Obj} → {cov : || Hom A B ||} → is-cover cov → is-epic cov
  cover-is-epi hasEql {A} {B} {cov} is-cov = record
    { epi-pf = λ pf → ridggˢ r (idcod (eqlar-is-iso pf)) ⊙ ass ⊙ ∘e r eqleq ⊙ assˢ
                       ⊙ ridgg r (idcod (eqlar-is-iso pf)) 
    }
    where open is-cover is-cov
          open has-equalisers hasEql
          open is-iso
          eqlar-is-iso : {C : Obj} {g g' : || Hom B C ||}
                           → g ∘ cov ~ g' ∘ cov → is-iso (eqlar {f = g} {g'})
          eqlar-is-iso pf = cov-pf (eqltr pf) (record { mono-pf = eqluq })


  strong-epi-is-epi : has-equalisers ℂ → {A B : Obj} → {f : || Hom A B ||} → is-strong-epi f → is-epic f
  strong-epi-is-epi hasEql fstr = cover-is-epi hasEql (strong-epi-is-cover fstr)


  strepi-is-transportable : iso-transportable is-strong-epi
  strepi-is-transportable = iso-transports.mkiso-transp
    strepi-is-congr
    (λ f fiso → split-epi-is-strong (iso-is-split-epi fiso))


  -- covering a coeq with epi yields a coeq

  epi/coeq-so-coeq : {R A Q : Obj} {r₁ r₂ : || Hom R A ||} {q : || Hom A Q ||}
                     {R' : Obj} {e : || Hom R' R ||} {r'₁ r'₂ : || Hom R' A ||}
                       → is-epic e → r₁ ∘ e ~ r'₁ → r₂ ∘ e ~ r'₂ → is-coeq r₁ r₂ q
                         → is-coeq r'₁ r'₂ q
  epi/coeq-so-coeq {R} {A} {Q} {r₁} {r₂} {q} {R'} {e} {r'₁} {r'₂} epi tr1 tr2 coeq = record
    { eq = q-eq'
    ; univ = λ f pf → q.univ f (epi-eq pf)
    ; univ-eq = λ pf → q.univ-eq (epi-eq pf)
    ; uniq = q.uniq
    }
    where module q = is-coeq coeq
          module e = is-epic epi
          q-eq' = ~proof q ∘ r'₁      ~[ ∘e (tr1 ˢ) r ] /
                         q ∘ r₁ ∘ e   ~[ ass ⊙ ∘e r q.eq ⊙ assˢ ] /
                         q ∘ r₂ ∘ e   ~[ ∘e tr2 r ]∎
                         q ∘ r'₂ ∎
          epi-eq : {B : Obj} {f : || Hom A B ||} → f ∘ r'₁ ~ f ∘ r'₂ → f ∘ r₁ ~ f ∘ r₂
          epi-eq pf = e.epi-pf (assˢ ⊙ ∘e tr1 r ⊙ pf ⊙ ∘e (tr2 ˢ) r ⊙ ass)


  -- conversely, factoring a coeq through an epi yields a coeq

  coeq/epi-so-coeq : {R' A Q : Obj} {r'₁ r'₂ : || Hom R' A ||} {q : || Hom A Q ||}
                     {R : Obj} {e : || Hom R' R ||} {r₁ r₂ : || Hom R A ||}
                       → is-epic e → r₁ ∘ e ~ r'₁ → r₂ ∘ e ~ r'₂ → is-coeq r'₁ r'₂ q → is-coeq r₁ r₂ q
  coeq/epi-so-coeq {R'} {A} {Q} {r'₁} {r'₂} {q} {R} {e} {r₁} {r₂} epi tr1 tr2 coeq' = record
    { eq = coeq-eq
    ; univ = λ f pf → coeq'.univ f (epi-eq pf)
    ; univ-eq = λ pf → coeq'.univ-eq (epi-eq pf)
    ; uniq = coeq'.uniq
    }
    where module coeq' = is-coeq coeq'
          module e = is-epic epi
          epi-eq : {B : Obj} {f : || Hom A B ||}
                      → f ∘ r₁ ~ f ∘ r₂ → f ∘ r'₁ ~ f ∘ r'₂
          epi-eq {f = f} pf = ~proof f ∘ r'₁      ~[  ∘e (tr1 ˢ) r ] /
                                     f ∘ r₁ ∘ e   ~[ ass ⊙ ∘e r pf ⊙ assˢ ] /
                                     f ∘ r₂ ∘ e   ~[ ∘e tr2 r ]∎
                                     f ∘ r'₂ ∎
          coeq-eq : q ∘ r₁ ~ q ∘ r₂
          coeq-eq = e.epi-pf (~proof (q ∘ r₁) ∘ e     ~[ assˢ ⊙ ∘e tr1 r ] /
                                     q ∘ r'₁          ~[ coeq'.eq ] /
                                     q ∘ r'₂          ~[ ∘e (tr2 ˢ) r ⊙ ass ]∎
                                     (q ∘ r₂) ∘ e ∎)


  -- uniqueness of coequalisers

  module uniq-of-coequalisers {R A : Obj} {r₁ r₂ : || Hom R A ||} {Q : Obj} {q : || Hom A Q ||}
                              (coeq : is-coeq r₁ r₂ q)
                              where
    private
      module q = is-coeq coeq

    uq-of-coeq-ar : {Q' : Obj} {q' : || Hom A Q' ||} (coeq' : is-coeq r₁ r₂ q') → || Hom Q Q' ||
    uq-of-coeq-ar {q' = q'} coeq' = q.univ q' q'.eq
                                 where module q' = is-coeq coeq'
    
    uq-of-coeq-ar-iso : {Q' : Obj} {q' : || Hom A Q' ||} (coeq' : is-coeq r₁ r₂ q') → is-iso (uq-of-coeq-ar coeq')
    uq-of-coeq-ar-iso coeq' = record
      { invf = q'.univ q q.eq
      ; isisopair = record
                  { iddom = q.epi-pf (assˢ ⊙ ∘e (q.univ-eq q'.eq) r ⊙ lidgenˢ (q'.univ-eq q.eq))
                  ; idcod = q'.epi-pf (assˢ ⊙ ∘e (q'.univ-eq q.eq) r ⊙ lidgenˢ (q.univ-eq q'.eq))
                  }
      }
      where module q' = is-coeq coeq'


    iso-rel-so-iso-coeq-pf : {R' A' Q' : Obj} {r'₁ r'₂ : || Hom R' A' ||} {q' : || Hom A' Q' ||} (coeq' : is-coeq r'₁ r'₂ q')
                             {rel : || Hom R R' ||} (rel-iso : is-iso rel) {base : || Hom A A' ||} (base-iso : is-iso base)
                             (iso-com₁ : base ∘ r₁ ~ r'₁ ∘ rel) (iso-com₂ : base ∘ r₂ ~ r'₂ ∘ rel)
                               → (q' ∘ base) ∘ r₁ ~ (q' ∘ base) ∘ r₂
    iso-rel-so-iso-coeq-pf {r'₁ = r'₁} {r'₂} {q'} coeq' {rel} rel-iso {base} base-iso iso-com₁ iso-com₂ =
      ~proof (q' ∘ base) ∘ r₁    ~[ assˢ ⊙ ∘e iso-com₁ r ] /
             q' ∘ r'₁ ∘ rel      ~[ ass ⊙ ∘e r coeq-eq' ⊙ assˢ ] /
             q' ∘ r'₂ ∘ rel      ~[ ∘e (iso-com₂ ˢ) r ⊙ ass ]∎
             (q' ∘ base) ∘ r₂ ∎
                              where open is-coeq coeq' renaming (eq to coeq-eq')


    iso-rel-so-iso-coeq-ar : {R' A' Q' : Obj} {r'₁ r'₂ : || Hom R' A' ||} {q' : || Hom A' Q' ||} (coeq' : is-coeq r'₁ r'₂ q')
                             {rel : || Hom R R' ||} (rel-iso : is-iso rel) {base : || Hom A A' ||} (base-iso : is-iso base)
                             (iso-com₁ : base ∘ r₁ ~ r'₁ ∘ rel) (iso-com₂ : base ∘ r₂ ~ r'₂ ∘ rel)
                               → || Hom Q Q' ||
    iso-rel-so-iso-coeq-ar {q' = q'} coeq' rel-iso {base = base} base-iso iso-com₁ iso-com₂ =
      q.univ (q' ∘ base) (iso-rel-so-iso-coeq-pf coeq' rel-iso base-iso iso-com₁ iso-com₂)


    iso-rel-so-iso-coeq-iso : {R' A' Q' : Obj} {r'₁ r'₂ : || Hom R' A' ||} {q' : || Hom A' Q' ||} (coeq' : is-coeq r'₁ r'₂ q')
                             {rel : || Hom R R' ||} (rel-iso : is-iso rel) {base : || Hom A A' ||} (base-iso : is-iso base)
                             (iso-com₁ : base ∘ r₁ ~ r'₁ ∘ rel) (iso-com₂ : base ∘ r₂ ~ r'₂ ∘ rel)
                               → is-iso (iso-rel-so-iso-coeq-ar coeq' rel-iso base-iso iso-com₁ iso-com₂)
    iso-rel-so-iso-coeq-iso {r'₁ = r'₁} {r'₂} {q'} coeq' rel-iso {base = base} base-iso iso-com₁ iso-com₂ = record
      { invf = q'.univ (q ∘ Lo≅.⁻¹) invf-pf
      ; isisopair = record
        { iddom = q.epi-pf ((assˢ ⊙ ∘e (q.univ-eq (iso-rel-so-iso-coeq-pf coeq' rel-iso base-iso iso-com₁ iso-com₂)) r
                           ⊙ lidgenˢ (ass ⊙ ∘e r (q'.univ-eq invf-pf) ⊙ assˢ ⊙ ridgg r Lo≅.iddom)))
        ; idcod = q'.epi-pf
                (assˢ ⊙ ∘e (q'.univ-eq invf-pf) r
                ⊙ lidgenˢ (ass ⊙ ∘e r (q.univ-eq (iso-rel-so-iso-coeq-pf coeq' rel-iso base-iso iso-com₁ iso-com₂))
                          ⊙ assˢ ⊙ ridgg r Lo≅.idcod))
                       }
      }
      where module q' = is-coeq coeq'
            module Lo≅ = is-iso base-iso
            module Hi≅ = is-iso rel-iso
            invf-pf = ~proof (q ∘ Lo≅.⁻¹) ∘ r'₁   ~[ assˢ ⊙ ∘e (invIsNat Hi≅.isisopair Lo≅.isisopair iso-com₁) r ] /
                             q ∘ r₁ ∘ Hi≅.⁻¹       ~[ ass ⊙ ∘e r q.eq ⊙ assˢ ] /
                             q ∘ r₂ ∘ Hi≅.⁻¹       ~[ ∘e (invIsNat Hi≅.isisopair Lo≅.isisopair iso-com₂ ˢ) r ⊙ ass ]∎
                             (q ∘ Lo≅.⁻¹) ∘ r'₂ ∎



  -- end uniq-of-coequalisers
  

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
          med : || Hom frepi.rel-obj ul ||
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
  kerpair-is-kerpair-of-coeq iskp {Q} {q} iscoeq = sub-pb-sq coeq.eq tr tr kp.ispb
                                                 where module kp = is-kernel-pair iskp
                                                       module coeq = is-coeq iscoeq
                                                       f : || Hom Q kp.Ob ||
                                                       f = coeq.univ kp.ar kp.×/sqpf
                                                       tr : f ∘ q ~ kp.ar
                                                       tr = coeq.univ-eq kp.×/sqpf


  kerp-of-repi-is-exact : {K A B : Obj} {kp₁ kp₂ : || Hom K A ||} {f : || Hom A B ||}
                             → is-kernel-pair-of kp₁ kp₂ f → is-regular-epi f → is-exact-seq kp₁ kp₂ f
  kerp-of-repi-is-exact {kp₁ = kp₁} {kp₂} {f} iskp repi = record
    { iscoeq = repi-is-coeq-of-ker-pair repi (mkpb-of ispb)
    ; iskerpair = ispb
    }
    where open is-kernel-pair-of iskp


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

-- end epis&monos-props-only