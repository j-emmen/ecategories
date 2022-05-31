
{-# OPTIONS --without-K #-}

module ecats.finite-limits.props.relations-among-limits where

open import ecats.basic-defs.ecat-def&not
open import ecats.basic-defs.commut-shapes
open import ecats.basic-defs.epi&mono
open import ecats.basic-props.epi&mono-basic
open import ecats.finite-limits.defs&not




module relations-among-limit-diagrams (ℂ : ecategory) where
  open ecategory-aux ℂ
  open comm-shapes ℂ
  open epi&mono-defs ℂ
  open epi&mono-props ℂ
  open finite-limits ℂ
  private
    module sp = span/
    module sq/ = square/cosp
    module ×/of = pullback-of-not
    module ×/sq = pb-square
    module ×of = product-of-not
    module ×sp = bin-product
    <>pf = ×of.<_,_>
    Δpf = prod-Δ.Δ
    syntax <>pf prdof f g = < f , g >[ prdof ]



  ×sq-on! : {T : Obj} (is! : is-terminal T)
            {A B A×B : Obj} (π₁ : || Hom A×B A ||) (π₂ : || Hom A×B B ||)
              → comm-square
  ×sq-on! is! {A} {B} π₁ π₂ = mksq (mksq/ (!uqg {f = ! A ∘ π₁} { ! B ∘ π₂}))
                            where open is-terminal is!


  ×is-pb-on! : {T : Obj} (is! : is-terminal T)
               {A B A×B : Obj} {π₁ : || Hom A×B A ||} {π₂ : || Hom A×B B ||} (isprd : is-product (mkspan π₁ π₂))
                 → is-pb-square (×sq-on! is! π₁ π₂)
  ×is-pb-on! is! isprd = record
    { ⟨_,_⟩[_] = λ h k _ → < h , k >
    ; ×/tr₁ = λ _ → ×tr₁
    ; ×/tr₂ = λ _ → ×tr₂
    ; ×/uq = ×uq
    }
    where open bin-product-not (mk× isprd)

  pb-on!-is× : {T : Obj} (is! : is-terminal T)
               {A B : Obj} {tA : || Hom A T ||} {tB : || Hom B T ||} (pbof : pullback-of tA tB)
                 → is-product (mkspan (×/of.π/₁ pbof) (×/of.π/₂ pbof))
  pb-on!-is× is! pbof = record
    { <_,_> = λ f g → ⟨ f , g ⟩[ !uqg ]
    ; ×tr₁ = ×/tr₁ !uqg
    ; ×tr₂ = ×/tr₂ !uqg
    ; ×uq = ×/uq
    }
    where open pullback-of-not pbof
          open is-terminal is!


  pb-trm-so-prd : {T : Obj} (is! : is-terminal T)
                     → has-pullbacks ℂ → has-bin-products ℂ
  pb-trm-so-prd is! pb = record
    { prd-of = λ A B → mk×of (pb-on!-is× is! (×/of {a = ! A} { ! B}))
    }
    where open pullbacks-aux pb
          open is-terminal is!



  module square-is-pullback↔subprod-is-equaliser {I A B : Obj} {a : || Hom A I ||} {b : || Hom B I ||}
                                                  (cone : square/cosp a b)
                                                  (A×B : product-of A B)
                                                  {e : || Hom (sq/.ul cone) (×of.O12 A×B) ||}
                                                  (eq : (a ∘ ×of.π₁ A×B) ∘ e ~ (b ∘ ×of.π₂ A×B) ∘ e)
                                                  (etr₁ : ×of.π₁ A×B ∘ e ~ sq/.left cone)
                                                  (etr₂ : ×of.π₂ A×B ∘ e ~ sq/.up cone)
                                                  where
    open product-of-not A×B renaming (O12 to AxB)
    open square/cosp cone

    is-pb→is-eql : is-pb-square (mksq cone) → is-equaliser eq
    is-pb→is-eql ispb = record
      { _|[_] = λ h pf → ⟨ π₁ ∘ h , π₂ ∘ h ⟩[ unpf pf ]
      ; tr = λ pf → ×uq (ass ⊙ ∘e r etr₁ ⊙ ×/tr₁ (unpf pf)) (ass ⊙ ∘e r etr₂ ⊙ ×/tr₂ (unpf pf))
      ; uq = mono-pf
      }
      where open pullback-sq-not (mkpb-sq ispb)
            unpf : {X : Obj} {h : || Hom X AxB ||} → (a ∘ π₁) ∘ h ~ (b ∘ π₂) ∘ h
                      → a ∘ π₁ ∘ h ~ b ∘ π₂ ∘ h
            unpf pf = ass ⊙ pf ⊙ assˢ
            emon : is-monic e
            emon = jointly-monic-tr etr₁ etr₂ (π/s-are-jointly-monic/ ×/pbsq)
            open is-monic emon

    is-eql→is-pb : is-equaliser eq → is-pb-square (mksq cone)
    is-eql→is-pb iseql = record
      { ⟨_,_⟩[_] = λ h k pf → < h , k > |[ unpf pf ]
      ; ×/tr₁ = λ pf → ∘e r (etr₁ ˢ) ⊙ (assˢ ⊙ ∘e (tr (unpf pf)) r ⊙ ×tr₁) 
      ; ×/tr₂ = λ pf → ∘e r (etr₂ ˢ) ⊙ (assˢ ⊙ ∘e (tr (unpf pf)) r ⊙ ×tr₂) 
      ; ×/uq = jm-pf
      }
      where open is-equaliser iseql
            unpf : {C : Obj} {h : || Hom C A ||} {k : || Hom C B ||} → a ∘ h ~ b ∘ k
                      → (a ∘ π₁) ∘ < h , k > ~ (b ∘ π₂) ∘ < h , k >
            unpf {h = h} pf = assˢ ⊙ ∘e ×tr₁ r ⊙ pf ⊙ ∘e (×tr₂ˢ {f = h}) r ⊙ ass
            π/jm : is-jointly-monic/ (mkspan/ left up)
            π/jm = jm∘mono-is-jm (πs-are-jointly-monic/ prdsp)
                                 (eqlof-is-monic (mkeql-of iseql))
                                 etr₁ etr₂
            open is-jointly-monic/ π/jm

  -- end square-is-pullback↔subprod-is-equaliser


  pbof→eqlofπ's : {A B : Obj} (A×B : product-of A B) {I : Obj} {f : || Hom A I ||} {g : || Hom B I ||} 
                    → pullback-of f g → equaliser-of (f ∘ ×of.π₁ A×B) (g ∘ ×of.π₂ A×B)
  pbof→eqlofπ's A×B {f = f} {g} pbof = record
    { Ob = ul
    ; ar = < π/₁ , π/₂ >
    ; eq = eq
    ; iseql = is-pb→is-eql ×/ispbsq
    }
    where open pullback-of-not pbof
          open product-of-not A×B
          eq : (f ∘ π₁) ∘ < π/₁ , π/₂ > ~ (g ∘ π₂) ∘ < π/₁ , π/₂ >
          eq = assˢ ⊙ ∘e ×tr₁ r ⊙ ×/sqpf ⊙ ∘e (×tr₂ˢ {f = π/₁}) r ⊙ ass
          open square-is-pullback↔subprod-is-equaliser ×/sq/ A×B eq ×tr₁ ×tr₂

  eqlofπ's→pbof : {A B : Obj} (A×B : product-of A B) {I : Obj} {f : || Hom A I ||} {g : || Hom B I ||} 
                    → equaliser-of (f ∘ ×of.π₁ A×B) (g ∘ ×of.π₂ A×B) → pullback-of f g
  eqlofπ's→pbof A×B {_} {f} {g} eqlof = record
    { ×/sq/ = cone
    ; ×/ispbsq = is-eql→is-pb iseql
    }
    where open equaliser-of eqlof
          cone : square/cosp f g
          cone = record
               { upleft = mkspan/ (×of.π₁ A×B ∘ ar) (×of.π₂ A×B ∘ ar)
               ; sq-pf = ass ⊙ eq ⊙ assˢ
               }
          open square-is-pullback↔subprod-is-equaliser cone A×B {ar} eq r r
          



  module equaliser↔pullback-of-diag-aux {B : Obj} (B×B : product-of B B)
                                         {A : Obj} (f f' : || Hom A B ||)
                                         where
    open product-of-not B×B
    open prod-Δ B×B
    sq2eq₁ : {C : Obj} {h : || Hom C A ||} {k : || Hom C B ||}
              → < f , f' > ∘ h ~ Δ ∘ k → f ∘ h ~ k
    sq2eq₁ {C} {h} {k} pf =
                 ~proof f ∘ h                    ~[ ∘e r (×tr₁ˢ {g = f'}) ⊙ assˢ ] /
                        π₁ ∘ < f , f' > ∘ h      ~[ ∘e pf r ⊙ ass ⊙ lidgg r ×tr₁ ]∎
                        k ∎
    sq2eq₂ : {C : Obj} {h : || Hom C A ||} {k : || Hom C B ||}
              → < f , f' > ∘ h ~ Δ ∘ k → f' ∘ h ~ k
    sq2eq₂ {C} {h} {k} pf =
                 ~proof f' ∘ h                    ~[ ∘e r (×tr₂ˢ {f = f}) ⊙ assˢ ] /
                        π₂ ∘ < f , f' > ∘ h       ~[ ∘e pf r ⊙ ass ⊙ lidgg r ×tr₂ ]∎
                        k ∎
    sq2eql : {C : Obj} {h : || Hom C A ||} {k : || Hom C B ||}
                → < f , f' > ∘ h ~ Δ ∘ k → f ∘ h ~ f' ∘ h
    sq2eql {C} {h} {k} pf = sq2eq₁ pf ⊙ sq2eq₂ pf ˢ
  -- end equaliser↔pullback-of-diag-aux

  module equaliser↔pullback-of-diag {B : Obj} (B×B : product-of B B)
                                     {A E : Obj} {f f' : || Hom A B ||} {e : || Hom E A ||}
                                     (eq : f ∘ e ~ f' ∘ e)
                                     {up : || Hom E B ||} (sqpf : < f , f' >[ B×B ] ∘ e ~ Δpf B×B ∘ up)
                                     where
    open product-of-not B×B
    open prod-Δ B×B
    open equaliser↔pullback-of-diag-aux B×B f f'
    tr₁ : up ~ f ∘ e
    tr₂ : up ~ f' ∘ e
    tr₁ = sq2eq₁ sqpf ˢ
    tr₂ = sq2eq₂ sqpf ˢ    

    is-eql→is-pb : is-equaliser eq → is-pb-square (mksq (mksq/ sqpf))
    is-eql→is-pb iseql = record
      { ⟨_,_⟩[_] = λ h k pf → h |[ sq2eql pf ]
      ; ×/tr₁ = λ pf → tr (sq2eql pf)
      ; ×/tr₂ = λ pf → ∘e r tr₁ ⊙ (assˢ ⊙ ∘e (tr (sq2eql pf)) r ⊙ sq2eq₁ pf)
      ; ×/uq = λ pf1 pf2 → uq pf1
      }
      where open is-equaliser iseql            
    
    is-pb→is-eql : is-pb-square (mksq (mksq/ sqpf)) → is-equaliser eq
    is-pb→is-eql ispb = record
      { _|[_] = λ h pf → ⟨ h , f ∘ h ⟩[ unpf pf ]
      ; tr = λ pf → ×/tr₁ (unpf pf)
      ; uq = λ pf → ×/uq pf (∘e r tr₁ ⊙ (assˢ ⊙ ∘e pf r ⊙ (ass ⊙ ∘e r (tr₁ ˢ))))
      }
      where open pullback-of-not (mkpb-of ispb)
            unpf : {C : Obj} {h : || Hom C A ||} (pf : f ∘ h ~ f' ∘ h)
                      → < f , f' >[ B×B ] ∘ h ~ Δpf B×B ∘ f ∘ h
            unpf pf = <>ar~<>ar lidˢ (pf ˢ ⊙ lidˢ)

  -- end equaliser↔pullback-of-diag



  eqlof→pbof<> : {B : Obj} (B×B : product-of B B) {A : Obj} {f f' : || Hom A B ||}
                    → equaliser-of f f' → pullback-of < f , f' >[ B×B ] (Δpf B×B)
  eqlof→pbof<> B×B {f = f} eqlof = record
    { ×/ispbsq = is-eql→is-pb iseql
    }
    where open equaliser-of eqlof
          open product-of-not B×B
          open equaliser↔pullback-of-diag B×B eq {f ∘ ar} (<>ar~<>ar lidˢ (lidgenˢ (eq ˢ)))

  pbof<>→eqlof : {B : Obj} (B×B : product-of B B) {A : Obj} {f f' : || Hom A B ||}
                    → pullback-of < f , f' >[ B×B ] (Δpf B×B) → equaliser-of f f'
  pbof<>→eqlof B×B {f = f} {f'} pbof = mkeql-of (is-pb→is-eql ×/ispbsq)
                                     where open pullback-of-not pbof
                                           open equaliser↔pullback-of-diag-aux B×B f f'
                                           eq : f ∘ π/₁ ~ f' ∘ π/₁
                                           eq = sq2eql ×/sqpf
                                           open equaliser↔pullback-of-diag B×B eq {π/₂} ×/sqpf

-- end relations-among-limit-diagrams





has-prd+eql⇒has-pb : {ℂ : ecategory} (prod : has-bin-products ℂ) → (eql : has-equalisers ℂ)
                          → has-pullbacks ℂ
has-prd+eql⇒has-pb {ℂ} prod eql = record
  { pb-of = λ {I} {A} {B} a b → eqlofπ's→pbof (prd-of A B) (eql-of (a ∘ π₁) (b ∘ π₂))
  }
  where open ecategory ℂ
        open has-bin-products prod
        open has-equalisers eql
        open relations-among-limit-diagrams ℂ


has-prd+pb⇒has-eql : {ℂ : ecategory} (prod : has-bin-products ℂ) → (pb : has-pullbacks ℂ)
                          → has-equalisers ℂ
has-prd+pb⇒has-eql {ℂ} prod pb = record
  { eql-of = λ {A} {B} f f' → pbof<>→eqlof (prd-of B B) (pb-of < f , f' > (Δ B))
  }
  where open ecategory ℂ
        open bin-products-aux prod
        open has-pullbacks pb
        open relations-among-limit-diagrams ℂ
        




module eql+pb⇒bw {ℂ : ecategory} (has-eql : has-equalisers ℂ) (has-pb : has-pullbacks ℂ) where
  open ecategory-aux ℂ
  open comm-shapes ℂ
  open bow-defs ℂ
  open pullback-squares ℂ
  open equaliser-defs ℂ
  open has-equalisers has-eql
  open pullbacks-aux has-pb

  module bows-from-eql+pb {DL DR : Obj} (sp₁ sp₂ : span/ DL DR) where
    private
      module sp₁ = span/ sp₁
      module sp₂ = span/ sp₂

    pb-a1 : pullback-of sp₁.a1 sp₂.a1
    pb-a1 = pb-of sp₁.a1 sp₂.a1
    private
      module a1×/a1 = pullback-of-not pb-a1

    eql-a2 : equaliser-of (sp₁.a2 ∘ a1×/a1.π/₁) (sp₂.a2 ∘ a1×/a1.π/₂)
    eql-a2 = eql-of (sp₁.a2 ∘ a1×/a1.π/₁) (sp₂.a2 ∘ a1×/a1.π/₂)
    private
      module eql-a2 = equaliser-of eql-a2

    ×//sqpf₁ : sp₁.a1 ∘ a1×/a1.π/₁ ∘ eql-a2.ar ~ sp₂.a1 ∘ a1×/a1.π/₂ ∘ eql-a2.ar
    ×//sqpf₁ = ass ⊙ ∘e r a1×/a1.×/sqpf ⊙ assˢ

    ×//sqpf₂ : sp₁.a2 ∘ a1×/a1.π/₁ ∘ eql-a2.ar ~ sp₂.a2 ∘ a1×/a1.π/₂ ∘ eql-a2.ar
    ×//sqpf₂ = ass ⊙ eql-a2.eq ⊙ assˢ

    isbow : is-bow ×//sqpf₁ ×//sqpf₂
    isbow = record
      { ⟨_,_⟩[_,_] = λ f₁ f₂ pf₁ pf₂ →  a1×/a1.⟨ f₁ , f₂ ⟩[ pf₁ ] eql-a2.|[ univpf pf₁ pf₂ ]
      ; tr₁ = λ pf₁ pf₂ → assˢ ⊙ ∘e (eql-a2.tr (univpf pf₁ pf₂)) r ⊙ ×/tr₁ pf₁
      ; tr₂ = λ pf₁ pf₂ → assˢ ⊙ ∘e (eql-a2.tr (univpf pf₁ pf₂)) r ⊙ ×/tr₂ pf₁
      ; uq = λ pf₁ pf₂ → eql-a2.uq (a1×/a1.×/uq (ass ⊙ pf₁ ⊙ assˢ) (ass ⊙ pf₂ ⊙ assˢ))
      }
      where univpf : {X : Obj} {f₁ : || Hom X sp₁.O12 ||} {f₂ : || Hom X sp₂.O12 ||}
                     (pf₁ : sp₁.a1 ∘ f₁ ~ sp₂.a1 ∘ f₂) (pf₂ : sp₁.a2 ∘ f₁ ~ sp₂.a2 ∘ f₂)
                       → (sp₁.a2 ∘ a1×/a1.π/₁) ∘ a1×/a1.⟨ f₁ , f₂ ⟩[ pf₁ ] ~ (sp₂.a2 ∘ a1×/a1.π/₂) ∘ a1×/a1.⟨ f₁ , f₂ ⟩[ pf₁ ]
            univpf {_} {f₁} {f₂} pf₁ pf₂ = ~proof
              (sp₁.a2 ∘ a1×/a1.π/₁) ∘ a1×/a1.⟨ f₁ , f₂ ⟩[ pf₁ ]     ~[ assˢ ⊙ ∘e (×/tr₁ pf₁) r ] /
              sp₁.a2 ∘ f₁                                            ~[ pf₂ ] /
              sp₂.a2 ∘ f₂                                            ~[ ∘e (×/tr₂ pf₁ ˢ) r ⊙ ass ]∎
              (sp₂.a2 ∘ a1×/a1.π/₂) ∘ a1×/a1.⟨ f₁ , f₂ ⟩[ pf₁ ] ∎

    
    bw-of : bow-of sp₁ sp₂
    bw-of = record
      { sp = mkspan/ (a1×/a1.π/₁ ∘ eql-a2.ar) (a1×/a1.π/₂ ∘ eql-a2.ar)
      ; sqpf₁ = ×//sqpf₁
      ; sqpf₂ = ×//sqpf₂
      ; is-bw = isbow
      }

  -- end bows-from-eql+pb
  
  has-bw : has-bows ℂ
  has-bw = record
    { bw-of = bw-of
    }
    where open bows-from-eql+pb

-- end eql+pb⇒bw


has-eql+pb⇒has-bw : {ℂ : ecategory} → has-equalisers ℂ → has-pullbacks ℂ
                         → has-bows ℂ
has-eql+pb⇒has-bw has-eql has-pb = has-bw
                                  where open eql+pb⇒bw has-eql has-pb

