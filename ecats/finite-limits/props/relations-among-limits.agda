
-- disable the K axiom:

{-# OPTIONS --without-K #-}

-- Agda version 2.5.4.1

module ecats.finite-limits.props.relations-among-limits where

open import ecats.basic-defs.ecat-def&not
open import ecats.basic-defs.commut-shapes
open import ecats.finite-limits.defs&not




module relations-among-limit-diagrams (ℂ : ecategory) where
  open ecategory-aux ℂ
  open comm-shapes ℂ
  open finite-limits ℂ
  private
    module sp = span/
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



  module square-is-pullback↔subprod-is-equaliser {A B : Obj} (A×B : product-of A B)
                                                  {C : Obj} {f : || Hom A C ||} {g : || Hom B C ||}
                                                  (cone : square/cosp f g)
                                                  where
    open product-of-not A×B
    open square/cosp cone

    eqlar : || Hom ul O12 ||
    eqlar = < left , up >
    eqleq : (f ∘ π₁) ∘ eqlar ~ (g ∘ π₂) ∘ eqlar
    eqleq = assˢ ⊙ ∘e ×tr₁ r ⊙ sq-pf ⊙ ∘e (×tr₂ˢ {f = left}) r ⊙ ass

    is-pb→is-eql : is-pb-square (mksq cone) → is-equaliser eqleq
    is-pb→is-eql ispb = record
      { _|eql[_] = λ h pf → ⟨ π₁ ∘ h , π₂ ∘ h ⟩[ ass ⊙ pf ⊙ assˢ ]
      ; eqltr = λ pf → <>ar~ar (×/tr₁ (ass ⊙ pf ⊙ assˢ) ˢ) (×/tr₂ (ass ⊙ pf ⊙ assˢ) ˢ)
      ; eqluq =  λ pf → ×/uq (∘e r (×tr₁ˢ {g = up}) ⊙ assˢ ⊙ ∘e pf r ⊙ ass ⊙ ∘e r ×tr₁)
                              (∘e r (×tr₂ˢ {f = left}) ⊙ assˢ ⊙ ∘e pf r ⊙ ass ⊙ ∘e r ×tr₂)
      }
      where open pullback-sq-not (mkpb-sq ispb)
  -- end square-is-pullback↔subprod-is-equaliser
    

  pbof→eqlof : {A B : Obj} (A×B : product-of A B) {I : Obj} {f : || Hom A I ||} {g : || Hom B I ||} 
                    → pullback-of f g → equaliser-of (f ∘ ×of.π₁ A×B) (g ∘ ×of.π₂ A×B)
  pbof→eqlof A×B pbof = record
    { Eql = ul
    ; eqlar = < π/₁ , π/₂ >
    ; eqleq = eqleq
    ; iseql = is-pb→is-eql ×/ispbsq
    }
    where open pullback-of-not pbof
          open ×of A×B
          open square-is-pullback↔subprod-is-equaliser A×B  ×/sq/



  module equaliser↔pullback-of-diag {B : Obj} (B×B : product-of B B)
                                     {A E : Obj} {f f' : || Hom A B ||} {e : || Hom E A ||}
                                     (pf : f ∘ e ~ f' ∘ e)                                     
                                     where
    open product-of-not B×B
    open prod-Δ B×B

    up : || Hom E B ||
    up = f ∘ e
    sqpf : < f , f' > ∘ e ~ Δ ∘ up
    sqpf = <>ar~<>ar lidˢ (lidgenˢ (pf ˢ))

    is-eql→is-pb : is-equaliser pf → is-pb-square (mksq (mksq/ sqpf))
    is-eql→is-pb iseql = record
      { ⟨_,_⟩[_] = λ h k pf → h |eql[ sq2eql pf ]
      ; ×/tr₁ = λ pf → eqltr (sq2eql pf)
      ; ×/tr₂ = λ pf → assˢ ⊙ ∘e (eqltr (sq2eql pf)) r ⊙ aux₁ pf
      ; ×/uq = λ pf1 pf2 → eqluq pf1
      }
      where open is-equaliser iseql
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
  -- end equaliser↔pullback-of-diag


  eqlof2pbof : {B : Obj} (B×B : product-of B B) {A : Obj} {f f' : || Hom A B ||}
                    → equaliser-of f f' → pullback-of < f , f' >[ B×B ] (Δpf B×B)
  eqlof2pbof B×B eqlof = record
    { ×/ispbsq = is-eql→is-pb iseql
    }
    where open equaliser-of eqlof
          open equaliser↔pullback-of-diag B×B eqleq

-- end relations-among-limit-diagrams





has-prd+pb⇒has-eql : {ℂ : ecategory} (prod : has-bin-products ℂ) → (pb : has-pullbacks ℂ)
                          → has-equalisers ℂ
has-prd+pb⇒has-eql {ℂ} prod pb = record
  { eql-of = λ f f' → record
           { Eql = < f , f' > ×/ₒ (Δ _)
           ; eqlar = π/₁
           ; eqleq = auxf f f' ⊙ (auxf' f f' ˢ)
           ; iseql = record
                   { _|eql[_] = λ h pf → ⟨ h , f ∘ h ⟩[ eqcond pf ]
                   ; eqltr = λ pf → ×/tr₁ (eqcond pf)
                   ; eqluq = λ pf → ×/uq pf (∘e r (auxf f f' ˢ) ⊙ assˢ ⊙ ∘e pf r ⊙ ass ⊙ ∘e r (auxf f f'))
                   }
           }
  }
  where open ecategory-aux ℂ
        open comm-shapes ℂ
        open pullback-defs ℂ
        open equaliser-defs ℂ
        open bin-products-aux prod
        open has-pullbacks pb
        eqcond : {A B C : Obj} {f f' : || Hom A B ||} {h : || Hom C A ||}
                    → f ∘ h ~ f' ∘ h → < f , f' > ∘ h ~ Δ B ∘ f ∘ h
        eqcond {f = f} {f'} {h} pf = <>dist h ⊙ <>ar~<>ˢ lid (lidgen pf)
        auxf : {A B : Obj} (f f' : || Hom A B ||) → f ∘ π/₁ ~ π/₂ {a = < f , f' >} {Δ B}
        auxf f f' = ∘e r (×tr₁ˢ) ⊙ (assˢ ⊙ (∘e ×/sqpf r ⊙ (ass ⊙ lidcmp ×tr₁)))
        auxf' : {A B : Obj} (f f' : || Hom A B ||) → f' ∘ π/₁ ~ π/₂ {a = < f , f' >} {Δ B}
        auxf' f f' = ∘e r ×tr₂ˢ ⊙ (assˢ ⊙ (∘e ×/sqpf r ⊙ (ass ⊙ lidcmp ×tr₂)))





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

    ×//sqpf₁ : sp₁.a1 ∘ a1×/a1.π/₁ ∘ eql-a2.eqlar ~ sp₂.a1 ∘ a1×/a1.π/₂ ∘ eql-a2.eqlar
    ×//sqpf₁ = ass ⊙ ∘e r a1×/a1.×/sqpf ⊙ assˢ

    ×//sqpf₂ : sp₁.a2 ∘ a1×/a1.π/₁ ∘ eql-a2.eqlar ~ sp₂.a2 ∘ a1×/a1.π/₂ ∘ eql-a2.eqlar
    ×//sqpf₂ = ass ⊙ eql-a2.eqleq ⊙ assˢ

    isbow : is-bow ×//sqpf₁ ×//sqpf₂
    isbow = record
      { ⟨_,_⟩[_,_] = λ f₁ f₂ pf₁ pf₂ →  a1×/a1.⟨ f₁ , f₂ ⟩[ pf₁ ] eql-a2.|eql[ univpf pf₁ pf₂ ]
      ; tr₁ = λ pf₁ pf₂ → assˢ ⊙ ∘e (eql-a2.eqltr (univpf pf₁ pf₂)) r ⊙ ×/tr₁ pf₁
      ; tr₂ = λ pf₁ pf₂ → assˢ ⊙ ∘e (eql-a2.eqltr (univpf pf₁ pf₂)) r ⊙ ×/tr₂ pf₁
      ; uq = λ pf₁ pf₂ → eql-a2.eqluq (a1×/a1.×/uq (ass ⊙ pf₁ ⊙ assˢ) (ass ⊙ pf₂ ⊙ assˢ))
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
      { sp = mkspan/ (a1×/a1.π/₁ ∘ eql-a2.eqlar) (a1×/a1.π/₂ ∘ eql-a2.eqlar)
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

