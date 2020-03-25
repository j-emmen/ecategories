 
-- disable the K axiom:

{-# OPTIONS --without-K #-}

-- Agda version 2.5.4.1

module ecats.basic-defs.image-fact where

open import ecats.basic-defs.ecat-def&not
open import ecats.basic-defs.commut-shapes
open import ecats.basic-defs.isomorphism
open import ecats.basic-defs.epi&mono
open import ecats.finite-limits.d&n-pullback
open import ecats.finite-limits.defs.weak-Wlimit


-- Image factorisation

module image-fact-defs (ℂ : ecategory) where
  open ecategory ℂ
  open comm-shapes ℂ
  open iso-defs ℂ
  open epis&monos-defs ℂ
  open pullback-defs ℂ
  open wWlim-defs ℂ
  private
    module sp = span/
    module ×/of = pullback-of

  record is-img-fact {A I B : Obj} {f : || Hom A B ||} {c : || Hom A I ||} {m : || Hom I B ||}
                     (tr : m ∘ c ~ f) : Set₁
                     where
    field
      M-is-monic : is-monic m
      univ : {C : Obj} {m' : || Hom C B ||} {c' : || Hom A C ||}
                   → is-monic m' → m' ∘ c' ~ f → || Hom I C ||
      univ-tr : {C : Obj} {m' : || Hom C B ||} {c' : || Hom A C ||}
                  (mon : is-monic m') (com : m' ∘ c' ~ f)
                     → m' ∘ univ mon com ~ m
    open is-monic M-is-monic renaming (mono-pf to Mpf) public

  
  record img-fact-of {A B : Obj} (f : || Hom A B ||) : Set₁ where
    field
      {Ob} : Obj
      {M} : || Hom Ob B ||
      {C} : || Hom A Ob ||
      {tr} : M ∘ C ~ f
      isimg : is-img-fact {A} {Ob} {B} {f} {C} {M} tr
    open is-img-fact isimg public


  record img-fact-is-pb-stable {A B : Obj} {f : || Hom A B ||} (imgf : img-fact-of f) : Set₁
                               where
    open pullback-of
    private
      module imgf = img-fact-of imgf
    field
      img-pb-stable : {C : Obj} {g : || Hom C B ||} (g×/f : pullback-of g f) (g×/mf : pullback-of g imgf.M)
                      {pbC : || Hom (ul g×/f) (ul g×/mf) ||} (pbtr : π/₁ g×/mf ∘ pbC ~ π/₁ g×/f)
                        → is-img-fact {ul g×/f} {ul g×/mf} {C} {π/₁ g×/f} {pbC} {π/₁ g×/mf} pbtr



  record is-repi-mono-fact {A I B : Obj} {f : || Hom A B ||} {c : || Hom A I ||} {m : || Hom I B ||}
                           (tr : m ∘ c ~ f) : Set₁
                           where
    field
      M-is-monic : is-monic m
      C-is-repi : is-regular-epi c
    open is-monic M-is-monic public -- renaming (mono-pf to Mpf)
    --open is-regular-epi C-is-repi renaming (mono-pf to Cpf) public
    module C = is-regular-epi C-is-repi

  
  record repi-mono-fact-of {A B : Obj} (f : || Hom A B ||) : Set₁ where
    field
      {Ob} : Obj
      {M} : || Hom Ob B ||
      {C} : || Hom A Ob ||
      {tr} : M ∘ C ~ f
      isrem : is-repi-mono-fact {A} {Ob} {B} {f} {C} {M} tr
    open is-repi-mono-fact isrem public



  -- image factorisation of a binary span

  record is-img-fact₂ {O1 O2 : Obj} {sp/ msp/ : span/ O1 O2} (cov-data : span/-mor sp/ msp/) : Set₁ where
    private
      module sp/ = span/ sp/
      module msp/ = span/ msp/
    open span/-mor cov-data renaming (ar to c)
    field
      M-is-jm/ : is-jointly-monic/ msp/
      univ : {msp/' : span/ O1 O2} (c'-data : span/-mor sp/ msp/')
                → is-jointly-monic/ msp/' → || Hom msp/.O12 (sp.O12 msp/') ||
      univ-tr₁ : {msp/' : span/ O1 O2} (c'-data : span/-mor sp/ msp/') (isjm : is-jointly-monic/ msp/')
                        → sp.a1 msp/' ∘ univ c'-data isjm ~ msp/.a1
      univ-tr₂ : {msp/' : span/ O1 O2} (c'-data : span/-mor sp/ msp/') (isjm : is-jointly-monic/ msp/')
                        → sp.a2 msp/' ∘ univ c'-data isjm ~ msp/.a2
    open is-jointly-monic/ M-is-jm/ public
  

  record img-fact-of₂ {O1 O2 : Obj} (sp/ : span/ O1 O2) : Set₁ where
    field
      msp/ : span/ O1 O2
      cov-data : span/-mor sp/ msp/
      isimg₂ : is-img-fact₂ cov-data
    open span/ msp/ renaming (O12 to I; a1 to m₁; a2 to m₂) public
    open span/-mor cov-data renaming (ar to c) public
    open is-img-fact₂ isimg₂ public


  record img-fact-is-pb-stable₂ {O1 O2 : Obj} {sp/ : span/ O1 O2} (imgsp : img-fact-of₂ sp/)
                                {A1 : Obj} {f1 : || Hom A1 O1 ||} {A2 : Obj} {f2 : || Hom A2 O2 ||}
                                (wWsp : wWlim-of f1 sp/ f2) (wWmsp : wWlim-of f1 (img-fact-of₂.msp/ imgsp) f2) : Set₁
                                where
    private
      module sp/ = span/ sp/
      module wWsp = wWlim-of wWsp
      module wWmsp = wWlim-of wWmsp
      module img = img-fact-of₂ imgsp
      f*sp : span/ A1 A2
      f*sp = mkspan/ wWsp.πl wWsp.πr
      f*msp : span/ A1 A2
      f*msp = mkspan/ wWmsp.πl wWmsp.πr
    field
      pbcov : span/-mor f*sp f*msp
      img-pb-stable₂ : is-img-fact₂ pbcov
    private
      module f*c = span/-mor pbcov
    pbc-sqpf : wWmsp.πc ∘ f*c.ar ~ img.c ∘ wWsp.πc
    pbc-sqpf = img.jm-pf (~proof img.m₁ ∘ wWmsp.πc ∘ f*c.ar   ~[ ass ⊙ ∘e r (wWmsp.sqpfl ˢ) ⊙ assˢ ] /
                                 f1 ∘ wWmsp.πl ∘ f*c.ar       ~[ ∘e f*c.tr₁ r ] /
                                 f1 ∘ wWsp.πl                 ~[ wWsp.sqpfl ] /
                                 sp/.a1 ∘ wWsp.πc             ~[ ∘e r (img.tr₁ ˢ) ⊙ assˢ ]∎
                                 img.m₁ ∘ img.c ∘ wWsp.πc ∎)
                         (~proof img.m₂ ∘ wWmsp.πc ∘ f*c.ar   ~[ ass ⊙ ∘e r (wWmsp.sqpfr ˢ) ⊙ assˢ ] /
                                 f2 ∘ wWmsp.πr ∘ f*c.ar       ~[ ∘e f*c.tr₂ r ] /
                                 f2 ∘ wWsp.πr                 ~[ wWsp.sqpfr ] /
                                 sp/.a2 ∘ wWsp.πc             ~[ ∘e r (img.tr₂ ˢ) ⊙ assˢ ]∎
                                 img.m₂ ∘ img.c ∘ wWsp.πc ∎)
             where open ecategory-aux-only ℂ


  record is-repi-mono-fact₂ {O1 O2 : Obj} {sp/ msp/ : span/ O1 O2}
                            (cov-data : span/-mor sp/ msp/) : Set₁
                            where
    private
      module sp/ = span/ sp/
      module msp/ = span/ msp/
    open span/-mor cov-data renaming (ar to c)
    field
      M-is-jm/ : is-jointly-monic/ msp/
      C-is-repi : is-regular-epi c
    open is-jointly-monic/ M-is-jm/ public
    module C = is-regular-epi C-is-repi
  

  record repi-mono-fact-of₂ {O1 O2 : Obj} (sp/ : span/ O1 O2) : Set₁ where
    field
      msp/ : span/ O1 O2
      cov-data : span/-mor sp/ msp/
      isrem₂ : is-repi-mono-fact₂ cov-data
    open span/ msp/ renaming (O12 to I; a1 to m₁; a2 to m₂) public
    open span/-mor cov-data renaming (ar to c) public
    open is-repi-mono-fact₂ isrem₂ public

-- end image-fact-defs







-- Definitions of category with (pullback-stable) image factorisation

  
record has-repi-mono-fact (ℂ : ecategory) : Set₁ where
  open ecategory ℂ
  open image-fact-defs ℂ
  field
    rmf-of : {A B : Obj} (f : || Hom A B ||) → repi-mono-fact-of f
  module rmf-of {A B : Obj} (f : || Hom A B ||) = repi-mono-fact-of (rmf-of f)

record has-img-fact (ℂ : ecategory) : Set₁ where
  -- constructor mkhas-imgf
  open ecategory ℂ
  open image-fact-defs ℂ
  field
    img-of : {A B : Obj} (f : || Hom A B ||) → img-fact-of f
  module img-of {A B : Obj} (f : || Hom A B ||) = img-fact-of (img-of f)


record has-pb-stable-img-fact (ℂ : ecategory) : Set₁ where
  open ecategory ℂ
  open epis&monos-defs ℂ
  open image-fact-defs ℂ
  open comm-shapes ℂ
  open pullback-defs ℂ
  open pullback-of
  field
    imgfact : has-img-fact ℂ
  open has-img-fact imgfact public    
  field
    pb-stb : {A B : Obj} (f : || Hom A B ||) → img-fact-is-pb-stable (img-of f)
  module img-pb-stb {A B : Obj} (f : || Hom A B ||) = img-fact-is-pb-stable (pb-stb f)
  open img-pb-stb public

{-
record has-pb-stable-img-fact (ℂ : ecategory) : Set₁ where
  open ecategory ℂ
  open epis&monos-defs ℂ
  open image-fact-defs ℂ
  open comm-shapes ℂ
  open pullback-defs ℂ
  open pullback-of
  field
    imgfact : has-img-fact ℂ
  open has-img-fact imgfact public    
  field
    pb-stb : {I A B : Obj} {f : || Hom A I ||} {g : || Hom B I ||}
             (g×/f : pullback-of g f) (g×/mf : pullback-of g (img-of.M f))
             {pbC : || Hom (ul g×/f) (ul g×/mf) ||} (pbtr : π/₁ g×/mf ∘ pbC ~ π/₁ g×/f)
               → img-fact-is-pb-stable (img-of f) g×/f g×/mf pbtr
  module img-pb-stb {I A B : Obj} {f : || Hom A I ||} {g : || Hom B I ||}
                    (g×/f : pullback-of g f) (g×/mf : pullback-of g (img-of.M f))
                    {pbC : || Hom (ul g×/f) (ul g×/mf) ||} (pbtr : π/₁ g×/mf ∘ pbC ~ π/₁ g×/f)
                    = img-fact-is-pb-stable (pb-stb g×/f g×/mf pbtr)
  open img-pb-stb public
-}

record has-img-fact₂ (ℂ : ecategory) : Set₁ where
  -- constructor mkhas-imgf
  open ecategory ℂ
  open comm-shapes ℂ
  open image-fact-defs ℂ
  field
    img-of₂ : {O1 O2 : Obj} (sp/ : span/ O1 O2) → img-fact-of₂ sp/
  module img-of₂ {O1 O2 : Obj} (sp/ : span/ O1 O2) = img-fact-of₂ (img-of₂ sp/)
  

record has-pb-stable-img-fact₂ (ℂ : ecategory) : Set₁ where
  open ecategory ℂ
  open epis&monos-defs ℂ
  open image-fact-defs ℂ
  open comm-shapes ℂ
  open pullback-defs ℂ
  open wWlim-defs ℂ
  field
    imgfact₂ : has-img-fact₂ ℂ
  open has-img-fact₂ imgfact₂ public    
  field
    pb-stb₂ : {O1 O2 : Obj} {sp/ : span/ O1 O2}
              {A1 : Obj} {f1 : || Hom A1 O1 ||} {A2 : Obj} {f2 : || Hom A2 O2 ||}
              (wWsp : wWlim-of f1 sp/ f2) (wWmsp : wWlim-of f1 (img-of₂.msp/ sp/) f2)
                → img-fact-is-pb-stable₂ (img-of₂ sp/) wWsp wWmsp
  module img-pb-stb₂ {O1 O2 : Obj} {sp/ : span/ O1 O2}
                     {A1 : Obj} {f1 : || Hom A1 O1 ||} {A2 : Obj} {f2 : || Hom A2 O2 ||}
                     (wWsp : wWlim-of f1 sp/ f2) (wWmsp : wWlim-of f1 (img-of₂.msp/ sp/) f2)
                     = img-fact-is-pb-stable₂ (pb-stb₂ wWsp wWmsp)
  open img-pb-stb₂ public
