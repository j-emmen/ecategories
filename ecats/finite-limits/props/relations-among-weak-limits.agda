
-- disable the K axiom:

{-# OPTIONS --without-K #-}

-- Agda version 2.5.4.1

module ecats.finite-limits.props.relations-among-weak-limits where

open import ecats.basic-defs.ecat-def&not
open import ecats.basic-defs.commut-shapes
open import ecats.finite-limits.defs&not




module relations-among-weak-limit-diagrams (ℂ : ecategory) where
  open ecategory-aux ℂ
  open comm-shapes ℂ
  open binary-products ℂ
  open finite-weak-limits ℂ
  private
    module sp = span/
    module w×/of = wpullback-of-not
    module ×of = product-of-not
    module ×sp = bin-product
    <>pf = ×of.<_,_>
    Δpf = prod-Δ.Δ
    syntax <>pf prdof f g = < f , g >[ prdof ]


  module square-is-wpullback↔subprod-is-wequaliser {A B : Obj} (A×B : product-of A B)
                                                    {C : Obj} {f : || Hom A C ||} {g : || Hom B C ||}
                                                    (cone : square/cosp f g)
                                                    where
    open product-of-not A×B
    open square/cosp cone

    weqlar : || Hom ul O12 ||
    weqlar = < left , up >
    weqleq : (f ∘ π₁) ∘ weqlar ~ (g ∘ π₂) ∘ weqlar
    weqleq = assˢ ⊙ ∘e ×tr₁ r ⊙ sq-pf ⊙ ∘e (×tr₂ˢ {f = left}) r ⊙ ass

    is-wpb→is-weql : is-wpb-square (mksq cone) → is-wequaliser weqleq
    is-wpb→is-weql iswpb = record
      { _|weql[_] = λ h pf → w⟨ π₁ ∘ h , π₂ ∘ h ⟩[ ass ⊙ pf ⊙ assˢ ]
      ; weqltr = λ pf → <>ar~ar (w×/tr₁ (ass ⊙ pf ⊙ assˢ) ˢ) (w×/tr₂ (ass ⊙ pf ⊙ assˢ) ˢ)
      }
      where open wpullback-sq-not (mkwpb-sq iswpb)      
  -- end square-is-pullback↔subprod-is-equaliser
    

  wpbof→weqlof : {A B : Obj} (A×B : product-of A B) {I : Obj} {f : || Hom A I ||} {g : || Hom B I ||} 
                    → wpullback-of f g → wequaliser-of (f ∘ ×of.π₁ A×B) (g ∘ ×of.π₂ A×B)
  wpbof→weqlof A×B wpbof = record
    { wEql = ul
    ; weqlar = < wπ/₁ , wπ/₂ >
    ; weqleq = weqleq
    ; isweql = is-wpb→is-weql w×/iswpbsq
    }
    where open wpullback-of-not wpbof
          open ×of A×B
          open square-is-wpullback↔subprod-is-wequaliser A×B  w×/sq/



  module wequaliser↔wpullback-of-diag {B : Obj} (B×B : product-of B B)
                                       {A E : Obj} {f f' : || Hom A B ||} {e : || Hom E A ||}
                                       (pf : f ∘ e ~ f' ∘ e)                                     
                                       where
    open product-of-not B×B
    open prod-Δ B×B

    up : || Hom E B ||
    up = f ∘ e
    sqpf : < f , f' > ∘ e ~ Δ ∘ up
    sqpf = <>ar~<>ar lidˢ (lidgenˢ (pf ˢ))

    is-weql→is-wpb : is-wequaliser pf → is-wpb-square (mksq (mksq/ sqpf))
    is-weql→is-wpb isweql = record
      { w⟨_,_⟩[_] = λ h k pf → h |weql[ sq2eql pf ]
      ; w×/tr₁ = λ pf → weqltr (sq2eql pf)
      ; w×/tr₂ = λ pf → assˢ ⊙ ∘e (weqltr (sq2eql pf)) r ⊙ aux₁ pf
      }
      where open is-wequaliser isweql
            aux₁ : {C : Obj} {h : || Hom C A ||} {k : || Hom C B ||}
                      → < f , f' > ∘ h ~ Δ ∘ k → f ∘ h ~ k
            aux₁ {C} {h} {k} pf =
                         ~proof f ∘ h                    ~[ ∘e r (×tr₁ˢ {g = f'}) ⊙ assˢ ] /
                                π₁ ∘ < f , f' > ∘ h      ~[ ∘e pf r ⊙ ass ⊙ lidgg r ×tr₁ ]∎
                                k ∎
                                
            aux₂ : {C : Obj} {h : || Hom C A ||} {k : || Hom C B ||}
                      → < f , f' > ∘ h ~ Δ ∘ k → f' ∘ h ~ k
            aux₂ {C} {h} {k} pf =
                         ~proof f' ∘ h                    ~[ ∘e r (×tr₂ˢ {f = f}) ⊙ assˢ ] /
                                π₂ ∘ < f , f' > ∘ h       ~[ ∘e pf r ⊙ ass ⊙ lidgg r ×tr₂ ]∎
                                k ∎
            
            sq2eql : {C : Obj} {h : || Hom C A ||} {k : || Hom C B ||}
                        → < f , f' > ∘ h ~ Δ ∘ k → f ∘ h ~ f' ∘ h
            sq2eql {C} {h} {k} pf = aux₁ pf ⊙ aux₂ pf ˢ
  -- end wequaliser↔wpullback-of-diag


  weqlof2wpbof : {B : Obj} (B×B : product-of B B) {A : Obj} {f f' : || Hom A B ||}
                    → wequaliser-of f f' → wpullback-of < f , f' >[ B×B ] (Δpf B×B)
  weqlof2wpbof B×B weqlof = record
    { w×/iswpbsq = is-weql→is-wpb isweql
    }
    where open wequaliser-of weqlof
          open wequaliser↔wpullback-of-diag B×B weqleq



  module wpullback→wWlimit {DL DR UL UR : Obj} (al : || Hom UL DL ||) (spc : span/ DL DR) (ar : || Hom UR DR ||)
                            (wpbl : wpullback-of al (sp.a1 spc)) (wpbr : wpullback-of ar (sp.a2 spc))
                            (wpbc : wpullback-of (w×/of.wπ/₂ wpbl) (w×/of.wπ/₂ wpbr))
                            where
    private
      module wpbl = wpullback-of wpbl
      module wpbc = wpullback-of wpbc
      module wpbr = wpullback-of wpbr
    open span/ spc renaming (O12 to UC; a1 to acl; a2 to acr)
    wWOb : Obj
    wWOb = wpbc.ul
    πl : || Hom wWOb UL ||
    πl = wpbl.wπ/₁ ∘ wpbc.wπ/₁
    πc : || Hom wWOb UC ||
    πc = wpbl.wπ/₂ ∘ wpbc.wπ/₁ -- ~ wpbr.wπ/₂ ∘ wpbc.wπ/₂
    πr : || Hom wWOb UR ||
    πr = wpbr.wπ/₁ ∘ wpbc.wπ/₂
    sqpfl : al ∘ πl ~ acl ∘ πc
    sqpfl = ass ⊙ ∘e r wpbl.w×/sqpf ⊙ assˢ
    sqpfr : ar ∘ πr ~ acr ∘ πc
    sqpfr = ass ⊙ ∘e r wpbr.w×/sqpf ⊙ assˢ ⊙ ∘e (wpbc.w×/sqpf ˢ) r 

    module wWuniv {X : Obj} {gl : || Hom X UL ||} {gc : || Hom X UC ||} {gr : || Hom X UR ||}
                  (pfl : al ∘ gl ~ acl ∘ gc) (pfr : ar ∘ gr ~ acr ∘ gc)
                  where
      wWunar-pf = wpbl.w×/tr₂ pfl ⊙ wpbr.w×/tr₂ pfr ˢ
      wWunar : || Hom X wWOb ||
      wWunar = wpbc.w⟨ wpbl.w⟨ gl , gc ⟩[ pfl ]
                     , wpbr.w⟨ gr , gc ⟩[ pfr ]
                     ⟩[ wWunar-pf ]
      wWuntrl : πl ∘ wWunar ~ gl
      wWuntrl = assˢ ⊙ ∘e (wpbc.w×/tr₁ wWunar-pf) r ⊙ wpbl.w×/tr₁ pfl
      wWuntrc : πc ∘ wWunar ~ gc
      wWuntrc = assˢ ⊙ ∘e (wpbc.w×/tr₁ wWunar-pf) r ⊙ wpbl.w×/tr₂ pfl
      wWuntrr : πr ∘ wWunar ~ gr
      wWuntrr = assˢ ⊙ ∘e (wpbc.w×/tr₂ wWunar-pf) r ⊙ wpbr.w×/tr₁ pfr
    -- end wWuniv
    
    iswW : is-wWlim sqpfl sqpfr
    iswW = record
         { ⟨_,_,_⟩[_,_] = λ gl gc gr → wWunar {_} {gl} {gc} {gr}
         ; trl = wWuntrl
         ; trc = wWuntrc
         ; trr = wWuntrr
         }
         where open wWuniv
  -- end wpullback→wWlimit


  wpbof→wWlimof : {DL DR UL UR : Obj} {al : || Hom UL DL ||} {spc : span/ DL DR} {ar : || Hom UR DR ||}
                   (wpbl : wpullback-of al (sp.a1 spc)) (wpbr : wpullback-of ar (sp.a2 spc))
                   (wpbc : wpullback-of (w×/of.wπ/₂ wpbl) (w×/of.wπ/₂ wpbr))
                     → wWlim-of al spc ar
  wpbof→wWlimof {al = al} {spc} {ar} wpbl wpbr wpc = record
    { wWOb = wWOb
    ; πl = πl
    ; πc = πc
    ; πr = πr
    ; sqpfl = sqpfl
    ; sqpfr = sqpfr
    ; iswWlim = iswW
    }
    where open wpullback→wWlimit al spc ar wpbl wpbr wpc

-- end relations-among-weak-limit-diagrams


has-wpb⇒has-wW : {ℂ : ecategory} → has-weak-pullbacks ℂ → has-weak-Wlimits ℂ
has-wpb⇒has-wW {ℂ} has-wpb = record
  { wW-of = λ al spc ar → wpbof→wWlimof (lw×/1.w×/of al spc)
                                         (rw×/2.w×/of spc ar)
                                         (wpb-of (lw×/1.wπ/₂ al spc)
                                                 (rw×/2.wπ/₂ spc ar))
  }
  where open ecategory ℂ
        open comm-shapes ℂ
        open wpullback-squares ℂ
        open relations-among-weak-limit-diagrams ℂ
        open has-weak-pullbacks has-wpb using (wpb-of)
        module lw×/1 {DL DR UL : Obj} (al : || Hom UL DL ||) (spc : span/ DL DR)
                     = wpullback-of-not (wpb-of al (span/.a1 spc))
        module rw×/2 {DL DR UR : Obj} (spc : span/ DL DR) (ar : || Hom UR DR ||)
                     = wpullback-of-not (wpb-of ar (span/.a2 spc))
                             


has-wprd+weql⇒has-wpb : {ℂ : ecategory} → has-bin-weak-products ℂ → has-weak-equalisers ℂ
                             → has-weak-pullbacks ℂ
has-wprd+weql⇒has-wpb {ℂ} wprod weql = mkhas-wpb (λ a b → mkwpb-of
  { w×/sq/ = mksq/ (~proof a ∘ wπ₁ ∘ weqlar      ~[ ass ⊙ weqleq ] /
                           (b ∘ wπ₂) ∘ weqlar    ~[ assˢ ]∎
                           b ∘ wπ₂ ∘ weqlar ∎)
  }
  (record
    { w⟨_,_⟩[_] = λ h k pf → w< h , k > |weql[ outsq pf ]
    ; w×/tr₁ = λ pf → assˢ ⊙ ∘e (weqltr (outsq pf)) r ⊙ w×tr₁
    ; w×/tr₂ = λ pf → assˢ ⊙ ∘e (weqltr (outsq pf)) r ⊙ w×tr₂
    }
  ))
  where open ecategory-aux ℂ
        open comm-shapes ℂ
        open wpullback-defs ℂ
        open has-bin-weak-products wprod
        open has-weak-equalisers weql
        outsq : {I A B C : Obj} {a : || Hom A I ||} {b : || Hom B I ||}
                {h : || Hom C A ||} {k : || Hom C B ||}
                   → a ∘ h ~ b ∘ k → (a ∘ wπ₁) ∘ w< h , k > ~ (b ∘ wπ₂) ∘ w< h , k >
        outsq pf = assˢ ⊙ ((∘e w×tr₁ r) ⊙ (pf ⊙ (∘e (w×tr₂ ˢ) r ⊙ ass)))


has-prd+weql⇒has-wpb : {ℂ : ecategory} → has-bin-products ℂ →  has-weak-equalisers ℂ
                            → has-weak-pullbacks ℂ
has-prd+weql⇒has-wpb {ℂ} prod weql = mkhas-wpb (λ a b → mkwpb-of
  { w×/sq/ = mksq/ (~proof a ∘ π₁ ∘ weqlar      ~[ ass ⊙ weqleq ] /
                           (b ∘ π₂) ∘ weqlar    ~[ assˢ ]∎
                           b ∘ π₂ ∘ weqlar ∎) }
  (record
    { w⟨_,_⟩[_] = λ h k pf → < h , k > |weql[ outsq pf ]
    ; w×/tr₁ = λ pf → assˢ ⊙ ∘e (weqltr (outsq pf)) r ⊙ ×tr₁
    ; w×/tr₂ = λ pf → assˢ ⊙ ∘e (weqltr (outsq pf)) r ⊙ ×tr₂
    }
  ))
  where open ecategory-aux ℂ
        open comm-shapes ℂ
        open wpullback-defs ℂ
        open bin-products-aux prod
        open has-weak-equalisers weql
        outsq : {I A B C : Obj} {a : || Hom A I ||} {b : || Hom B I ||}
                {h : || Hom C A ||} {k : || Hom C B ||}
                   → a ∘ h ~ b ∘ k → (a ∘ π₁) ∘ < h , k > ~ (b ∘ π₂) ∘ < h , k >
        outsq pf = assˢ ⊙ ((∘e ×tr₁ r) ⊙ (pf ⊙ (∘e ×tr₂ˢ r ⊙ ass)))



has-prd+wpb⇒has-weql : {ℂ : ecategory} → has-bin-products ℂ → has-weak-pullbacks ℂ
                            → has-weak-equalisers ℂ
has-prd+wpb⇒has-weql {ℂ} prod wpb = record
  { weql-of = λ f f' → record
            { wEql = < f , f' > w×/ₒ (Δ _)
            ; weqlar = wπ/₁
            ; weqleq = auxf f f' ⊙ (auxf' f f' ˢ)
            ; isweql = record
                     { _|weql[_] = λ h pf → w⟨ h , f ∘ h ⟩[ eqcond pf ]
                     ; weqltr = λ pf → w×/tr₁ (eqcond pf)
                     }
            }
  }
  where open ecategory-aux ℂ
        open comm-shapes ℂ
        open wpullback-defs ℂ
        open wequaliser-defs ℂ
        open bin-products-aux prod
        open has-weak-pullbacks wpb
        eqcond : {A B C : Obj} {f f' : || Hom A B ||} {h : || Hom C A ||}
                    → f ∘ h ~ f' ∘ h → < f , f' > ∘ h ~ Δ B ∘ f ∘ h
        eqcond {f = f} {f'} {h} pf = <>dist h ⊙ <>ar~<>ˢ lid (lidgen pf)
        auxf : {A B : Obj} (f f' : || Hom A B ||) → f ∘ wπ/₁ ~ wπ/₂ {a = < f , f' >} {Δ B}
        auxf f f' = ∘e r (×tr₁ˢ) ⊙ (assˢ ⊙ (∘e w×/sqpf r ⊙ (ass ⊙ lidcmp ×tr₁)))
        auxf' : {A B : Obj} (f f' : || Hom A B ||) → f' ∘ wπ/₁ ~ wπ/₂ {a = < f , f' >} {Δ B}
        auxf' f f' = ∘e r ×tr₂ˢ ⊙ (assˢ ⊙ (∘e w×/sqpf r ⊙ (ass ⊙ lidcmp ×tr₂)))



has-wpb⇒has-wWlim : {ℂ : ecategory} → has-weak-pullbacks ℂ → has-weak-Wlimits ℂ
has-wpb⇒has-wWlim {ℂ} haswpb = record
  { wW-of = λ al spc ar → wpbof→wWlimof  (wpb-of al (a1 spc))
                                              (wpb-of ar (a2 spc))
                                              (wpb-of (×/of.wπ/₂ (wpb-of al (a1 spc))) (×/of.wπ/₂ (wpb-of ar (a2 spc))))
                                       }
                                       where open relations-among-weak-limit-diagrams ℂ
                                             open has-weak-pullbacks haswpb using (wpb-of)
                                             open comm-shapes.span/
                                             module ×/of = wpullback-defs.wpullback-of




module weql+wpb⇒wbw {ℂ : ecategory} (has-weql : has-weak-equalisers ℂ) (has-wpb : has-weak-pullbacks ℂ) where
  open ecategory-aux ℂ
  open comm-shapes ℂ
  open weak-bow-defs ℂ
  open wpullback-squares ℂ
  open wequaliser-defs ℂ
  open has-weak-equalisers has-weql
  open weak-pullbacks-aux (wpb-aux has-wpb)

  module wbows-from-weql+wpb {DL DR : Obj} (sp₁ sp₂ : span/ DL DR) where
    private
      module sp₁ = span/ sp₁
      module sp₂ = span/ sp₂

    wpb-a1 : wpullback-of sp₁.a1 sp₂.a1
    wpb-a1 = wpb-of sp₁.a1 sp₂.a1
    private
      module a1×/a1 = wpullback-of-not wpb-a1

    weql-a2 : wequaliser-of (sp₁.a2 ∘ a1×/a1.wπ/₁) (sp₂.a2 ∘ a1×/a1.wπ/₂)
    weql-a2 = weql-of (sp₁.a2 ∘ a1×/a1.wπ/₁) (sp₂.a2 ∘ a1×/a1.wπ/₂)
    private
      module weql-a2 = wequaliser-of weql-a2

    w×//sqpf₁ : sp₁.a1 ∘ a1×/a1.wπ/₁ ∘ weql-a2.weqlar ~ sp₂.a1 ∘ a1×/a1.wπ/₂ ∘ weql-a2.weqlar
    w×//sqpf₁ = ass ⊙ ∘e r a1×/a1.w×/sqpf ⊙ assˢ

    w×//sqpf₂ : sp₁.a2 ∘ a1×/a1.wπ/₁ ∘ weql-a2.weqlar ~ sp₂.a2 ∘ a1×/a1.wπ/₂ ∘ weql-a2.weqlar
    w×//sqpf₂ = ass ⊙ weql-a2.weqleq ⊙ assˢ

    iswbow : is-wbow w×//sqpf₁ w×//sqpf₂
    iswbow = record
      { ⟨_,_⟩[_,_] = λ f₁ f₂ pf₁ pf₂ →  a1×/a1.w⟨ f₁ , f₂ ⟩[ pf₁ ] weql-a2.|weql[ univpf pf₁ pf₂ ]
      ; tr₁ = λ pf₁ pf₂ → assˢ ⊙ ∘e (weql-a2.weqltr (univpf pf₁ pf₂)) r ⊙ w×/tr₁ pf₁
      ; tr₂ = λ pf₁ pf₂ → assˢ ⊙ ∘e (weql-a2.weqltr (univpf pf₁ pf₂)) r ⊙ w×/tr₂ pf₁
      }
      where univpf : {X : Obj} {f₁ : || Hom X sp₁.O12 ||} {f₂ : || Hom X sp₂.O12 ||}
                     (pf₁ : sp₁.a1 ∘ f₁ ~ sp₂.a1 ∘ f₂) (pf₂ : sp₁.a2 ∘ f₁ ~ sp₂.a2 ∘ f₂)
                       → (sp₁.a2 ∘ a1×/a1.wπ/₁) ∘ a1×/a1.w⟨ f₁ , f₂ ⟩[ pf₁ ] ~ (sp₂.a2 ∘ a1×/a1.wπ/₂) ∘ a1×/a1.w⟨ f₁ , f₂ ⟩[ pf₁ ]
            univpf {_} {f₁} {f₂} pf₁ pf₂ = ~proof
              (sp₁.a2 ∘ a1×/a1.wπ/₁) ∘ a1×/a1.w⟨ f₁ , f₂ ⟩[ pf₁ ]     ~[ assˢ ⊙ ∘e (w×/tr₁ pf₁) r ] /
              sp₁.a2 ∘ f₁                                            ~[ pf₂ ] /
              sp₂.a2 ∘ f₂                                            ~[ ∘e (w×/tr₂ pf₁ ˢ) r ⊙ ass ]∎
              (sp₂.a2 ∘ a1×/a1.wπ/₂) ∘ a1×/a1.w⟨ f₁ , f₂ ⟩[ pf₁ ] ∎

    
    wbw-of : wbow-of sp₁ sp₂
    wbw-of = record
      { sp = mkspan/ (a1×/a1.wπ/₁ ∘ weql-a2.weqlar) (a1×/a1.wπ/₂ ∘ weql-a2.weqlar)
      ; sqpf₁ = w×//sqpf₁
      ; sqpf₂ = w×//sqpf₂
      ; is-wbw = iswbow
      }

  -- end wbows-from-weql+wpb
  
  has-wbw : has-weak-bows ℂ
  has-wbw = record
    { wbw-of = wbw-of
    }
    where open wbows-from-weql+wpb

-- end weql+wpb⇒wbw

has-weql+wpb⇒has-wbw : {ℂ : ecategory} → has-weak-equalisers ℂ → has-weak-pullbacks ℂ
                          → has-weak-bows ℂ
has-weql+wpb⇒has-wbw has-weql has-wpb = has-wbw
                                       where open weql+wpb⇒wbw has-weql has-wpb



