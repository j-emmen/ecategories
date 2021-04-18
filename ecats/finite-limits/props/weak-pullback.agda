 
-- disable the K axiom:

{-# OPTIONS --without-K #-}

-- Agda version 2.5.4.1

module ecats.finite-limits.props.weak-pullback where

open import ecats.basic-defs.ecat-def&not
open import ecats.basic-defs.commut-shapes
open import ecats.basic-defs.isomorphism
open import ecats.basic-defs.epi&mono
open import ecats.finite-limits.defs&not




module weak-pullback-props (ℂ : ecategory) where
  open ecategory-aux ℂ
  open iso-defs ℂ
  open epi&mono-defs ℂ
  open comm-shapes ℂ
  open binary-wproducts ℂ
  open binary-products ℂ
  open wequaliser-defs ℂ
  open wpullback-squares ℂ
  private
    module sq/ = square/cosp
    module w×/of = wpullback-of
    module w×/ = wpullback-sq-not
    module ×of {A B : Obj} (×of : product-of A B) = bin-product-not (product-of.prdsp ×of)


  arfromwpb-is-wpb : {I A B : Obj} {a : || Hom A I ||} {b : || Hom B I ||}
                     (a×/b : wpullback-of a b) (sq/ : square/cosp a b)
                     {w : || Hom (w×/of.ul a×/b) (sq/.ul sq/) ||}
                       → sq/.left sq/ ∘ w ~ w×/of.wπ/₁ a×/b → sq/.up sq/ ∘ w ~ w×/of.wπ/₂ a×/b
                           → is-wpb-square (mksq sq/)
  arfromwpb-is-wpb {a = a} {b} a×/b sq/ {w} trl tru = record
    { w⟨_,_⟩[_] = λ h k pf → w ∘ w⟨ h , k ⟩[ pf ]
    ; w×/tr₁ = λ pf → ass ⊙ ∘e r trl ⊙ w×/tr₁ pf
    ; w×/tr₂ = λ pf → ass ⊙ ∘e r tru ⊙ w×/tr₂ pf
    }
    where open wpullback-sq-not (mkwpb-sq (w×/of.w×/iswpbsq a×/b))


  -- Weak pullback extensionality

  w×/ext-sq : {I A B P : Obj} {a : || Hom A I ||}{b : || Hom B I ||}
              {p₁ : || Hom P A ||} {p₂ : || Hom P B ||} ({pf} pf' : a ∘ p₁ ~ b ∘ p₂)
                → is-wpb-square (mksq (mksq/ pf)) → is-wpb-square (mksq (mksq/ pf'))
  w×/ext-sq pf' iswpb =
    arfromwpb-is-wpb (mkwpb-of iswpb) (mksq/ pf') {idar _} rid rid
  

  w×/ext-dr : {I A B : Obj} {a a' : || Hom A I ||}{b b' : || Hom B I ||} {sq/ : square/cosp a b}
              (iswpb : is-wpb-square (mksq sq/)) (pfa : a ~ a') (pfb : b ~ b')
               → is-wpb-square (mksq (sq-ext sq/ pfa pfb))
  w×/ext-dr {I} {A} {B} {a} {a'} {b} {b'} {sq/} iswpb pfa pfb = record
    { w⟨_,_⟩[_] = λ h k pf' → w⟨ h , k ⟩[ w⟨⟩pf pf' ]
    ; w×/tr₁ = λ pf' → w×/tr₁ (w⟨⟩pf pf')
    ; w×/tr₂ = λ pf' → w×/tr₂ (w⟨⟩pf pf')
    }
    where open is-wpb-square iswpb
          w⟨⟩pf : {C : Obj} {h : || Hom C A ||} {k : || Hom C B ||}
                     → a' ∘ h ~ b' ∘ k → a ∘ h ~ b ∘ k
          w⟨⟩pf pf' = ∘e r pfa ⊙ pf' ⊙ ∘e r (pfb ˢ)


  w×/ext-ul : {I A B P : Obj} {a : || Hom A I ||}{b : || Hom B I ||} --(pbof : pullback-of a b) (pbofₙ.ul pbof)
              {p₁ p₁' : || Hom P A ||} {p₂ p₂' : || Hom P B ||} {pfsq : a ∘ p₁ ~ b ∘ p₂} (pfsq' : a ∘ p₁' ~ b ∘ p₂')
               → is-wpb-square (mksq (mksq/ pfsq)) → p₁' ~ p₁ → p₂' ~ p₂
                 → is-wpb-square (mksq (mksq/ pfsq'))
  w×/ext-ul pfsq' iswpb pfp₁ pfp₂ =
    arfromwpb-is-wpb (mkwpb-of iswpb) (mksq/ pfsq') {idar _} (ridgen pfp₁) (ridgen pfp₂)


  w×/ext : {I A B P : Obj} {a a' : || Hom A I ||}{b b' : || Hom B I ||}
           {p₁ p₁' : || Hom P A ||} {p₂ p₂' : || Hom P B ||}
           (pfsq : a ∘ p₁ ~ b ∘ p₂) (pfsq' : a' ∘ p₁' ~ b' ∘ p₂')
           (wpbsq/ : is-wpb-square (mksq (mksq/ pfsq)))
            → a ~ a' → b ~ b' → p₁ ~ p₁' → p₂ ~ p₂'
              → is-wpb-square (mksq (mksq/ pfsq'))
  w×/ext {I} {A} {B} {P} {a} {a'} {b} {b'} pfsq pfsq' wpbsq pfa pfb pfp₁ pfp₂ = record
    { w⟨_,_⟩[_] = λ h k pf → w⟨ h , k ⟩[ w⟨⟩pf pf ]
    ; w×/tr₁ = λ pf → ∘e r (pfp₁ ˢ) ⊙ w×/tr₁ (w⟨⟩pf pf)
    ; w×/tr₂ = λ pf → ∘e r (pfp₂ ˢ) ⊙ w×/tr₂ (w⟨⟩pf pf)
    }
    where open is-wpb-square wpbsq
          w⟨⟩pf : {C : Obj} {h : || Hom C A ||} {k : || Hom C B ||}
                    → a' ∘ h ~ b' ∘ k → a ∘ h ~ b ∘ k
          w⟨⟩pf pf' = ∘e r pfa ⊙ pf' ⊙ ∘e r (pfb ˢ)



  -- Weak pullbacks and weak equalisers    

  module wpb→weql (wpb : wpullback-sq) (dl×ur : product-of (w×/.dl wpb) (w×/.ur wpb)) where
    open bin-product-not (mk× (product-of.×isprd dl×ur))
    open wpullback-sq-not wpb

    weqleq : (down ∘ π₁) ∘ < wπ/₁ , wπ/₂ > ~ (right ∘ π₂) ∘ < wπ/₁ , wπ/₂ >
    weqleq = assˢ ⊙ ∘e ×tr₁ r ⊙ w×/sqpf ⊙ ∘e (×tr₂ˢ {f = wπ/₁}) r ⊙ ass

    iswpb2isweql : is-wequaliser weqleq
    iswpb2isweql = record
      { _|weql[_] = λ h pf → w⟨ π₁ ∘ h , π₂ ∘ h ⟩[ ass ⊙ pf ⊙ assˢ ]
      ; weqltr = λ pf → <>ar~ar (w×/tr₁ (ass ⊙ pf ⊙ assˢ) ˢ) (w×/tr₂ (ass ⊙ pf ⊙ assˢ) ˢ)
      }
      
  -- end wpb→weql


  wpbof2weqlof : {A B I : Obj} {f : || Hom A I ||} {g : || Hom B I ||} (A×B : product-of A B)
                    → wpullback-of f g → wequaliser-of (f ∘ ×of.π₁ A×B) (g ∘ ×of.π₂ A×B)
  wpbof2weqlof B×B wpbof = record
    { wEql = ul
    ; weqlar = < wπ/₁ , wπ/₂ >
    ; weqleq = weqleq
    ;isweql = iswpb2isweql
    }
    where open wpullback-of-not wpbof
          open ×of B×B
          open wpb→weql wpbsq B×B 


  module wpb←weql {B : Obj} (B×B : product-of B B) where
    open bin-product-not (mk× (product-of.×isprd B×B))
    open prod-Δ B×B
    
    wpbeq : {A E : Obj} {f f' : || Hom A B ||} {e : || Hom E A ||} (pfeq : f ∘ e ~ f' ∘ e)
               → < f , f' > ∘ e ~ Δ ∘ (f ∘ e)
    wpbeq pfeq = <>ar~<>ar lidˢ (lidgenˢ (pfeq ˢ))

    isweql2iawpb : {A E : Obj} {f f' : || Hom A B ||} {e : || Hom E A ||} {pfeq : f ∘ e ~ f' ∘ e}
                      → is-wequaliser pfeq → is-wpb-square (mksq (mksq/ (wpbeq pfeq)))
    isweql2iawpb {A} {E} {f} {f'} {e} {pfeq} isweql = record
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


    weqlof2wpbof : {A  : Obj} {f f' : || Hom A B ||}
                      → wequaliser-of f f' → wpullback-of < f , f' > Δ
    weqlof2wpbof weqlof = record
      { w×/iswpbsq = isweql2iawpb isweql
      }
      where open wequaliser-of weqlof
  -- end wpb←weql

-- end weak-pullback-props



{-
  -- limits of diagrams shaped like W
  module wpb→wW (has-wpb : has-weak-pullbacks ℂ) where
    open has-weak-pullbacks has-wpb using (wpb-of) 
    module wW-of {DL DR : Obj} (sp : span/ DL DR) {UL UR : Obj} (al : || Hom UL DL ||) (ar : || Hom UR DR ||)
                 where
      open span/ sp renaming (O12 to UC)
      private
        module a1×/al = wpullback-of-not (wpb-of a1 al)
        module a2×/ar = wpullback-of-not (wpb-of a2 ar)
        module lrpb = wpullback-of-not (wpb-of a1×/al.wπ/₁ a2×/ar.wπ/₁)
      Ob : Obj
      Ob = lrpb.ul
      πl : || Hom Ob UL ||
      πl = a1×/al.wπ/₂ ∘ lrpb.wπ/₁
      πr : || Hom Ob UR ||
      πr = a2×/ar.wπ/₂ ∘ lrpb.wπ/₂
      πc : || Hom Ob UC ||
      πc = a1×/al.wπ/₁ ∘ lrpb.wπ/₁
      πlr : span/ UL UR
      πlr = mkspan/ πl πr

      sql-pf : al ∘ πl ~ a1 ∘ πc
      sql-pf = ass ⊙ ∘e r (a1×/al.w×/sqpf ˢ) ⊙ assˢ
      sqr-pf :  ar ∘ πr ~ a2 ∘ πc
      sqr-pf = ass ⊙ ∘e r (a2×/ar.w×/sqpf ˢ) ⊙ assˢ ⊙ ∘e (lrpb.w×/sqpf ˢ) r

      univ-pf : {A : Obj} {fl : || Hom A UL || } {fc : || Hom A UC ||} {fr : || Hom A UR ||}
                (pfl : al ∘ fl ~ a1 ∘ fc) (pfr : ar ∘ fr ~ a2 ∘ fc)
                     → a1×/al.wπ/₁ ∘ a1×/al.w⟨ fc , fl ⟩[ pfl ˢ ] ~ a2×/ar.wπ/₁ ∘ a2×/ar.w⟨ fc , fr ⟩[ pfr ˢ ]
      univ-pf pfl pfr = a1×/al.w×/tr₁ (pfl ˢ) ⊙ a2×/ar.w×/tr₁ (pfr ˢ) ˢ

      ⟨_,_,_⟩[_,_] : {A : Obj} (fl : || Hom A UL ||) (fc : || Hom A UC ||) (fr : || Hom A UR ||)
                          → al ∘ fl ~ a1 ∘ fc → ar ∘ fr ~ a2 ∘ fc → || Hom A Ob ||
      ⟨ fl , fc , fr ⟩[ pfl , pfr ] = lrpb.w⟨ a1×/al.w⟨ fc , fl ⟩[ pfl ˢ ]
                                             , a2×/ar.w⟨ fc , fr ⟩[ pfr ˢ ]
                                             ⟩[ univ-pf pfl pfr ]


      trl : {A : Obj} {fl : || Hom A UL || } {fc : || Hom A UC ||} {fr : || Hom A UR ||}
              (pfl : al ∘ fl ~ a1 ∘ fc) (pfr : ar ∘ fr ~ a2 ∘ fc)
                → πl ∘ ⟨ fl , fc , fr ⟩[ pfl , pfr ] ~ fl
      trl pfl pfr = assˢ ⊙ ∘e (lrpb.w×/tr₁ (univ-pf pfl pfr)) r ⊙ a1×/al.w×/tr₂ (pfl ˢ)

      trc : {A : Obj} {fl : || Hom A UL || } {fc : || Hom A UC ||} {fr : || Hom A UR ||}
              (pfl : al ∘ fl ~ a1 ∘ fc) (pfr : ar ∘ fr ~ a2 ∘ fc)
                → πc ∘ ⟨ fl , fc , fr ⟩[ pfl , pfr ] ~ fc
      trc pfl pfr = assˢ ⊙ ∘e (lrpb.w×/tr₁ (univ-pf pfl pfr)) r ⊙ a1×/al.w×/tr₁ (pfl ˢ)

      trr : {A : Obj} {fl : || Hom A UL || } {fc : || Hom A UC ||} {fr : || Hom A UR ||}
              (pfl : al ∘ fl ~ a1 ∘ fc) (pfr : ar ∘ fr ~ a2 ∘ fc)
                → πr ∘ ⟨ fl , fc , fr ⟩[ pfl , pfr ] ~ fr
      trr pfl pfr = assˢ ⊙ ∘e (lrpb.w×/tr₂ (univ-pf pfl pfr)) r ⊙ a2×/ar.w×/tr₂ (pfr ˢ)
    -- end wW-of
  -- end wpb→wW
-}


{-
  module wpb↔weqlᶜ (prdC : has-products ℂ) where
    open bin-products-aux prdC
    private
      module isw×/ {sq : comm-square} (iswpb : is-wpb-square sq) = wpullback-sq-not (mkwpb-sq iswpb)

    weqleq : {sq : comm-square} (iswpb : is-wpb-square sq)
                 → (isw×/.down iswpb ∘ π₁) ∘ < isw×/.wπ/₁ iswpb , isw×/.wπ/₂ iswpb >
                               ~ (isw×/.right iswpb ∘ π₂) ∘ < isw×/.wπ/₁ iswpb , isw×/.wπ/₂ iswpb >
    weqleq iswpb = assˢ ⊙ ∘e ×tr₁ r ⊙ isw×/.w×/sqpf iswpb ⊙ ∘e (×tr₂ˢ {f = isw×/.wπ/₁ iswpb}) r ⊙ ass

    iswpb2isweql : {sq : comm-square} (iswpb : is-wpb-square sq) → is-wequaliser (weqleq iswpb)
    iswpb2isweql iswpb = record
      { _|weql[_] = λ h pf → w⟨ π₁ ∘ h , π₂ ∘ h ⟩[ ass ⊙ pf ⊙ assˢ ]
      ; weqltr = λ pf → <>ar~ar (w×/tr₁ (ass ⊙ pf ⊙ assˢ) ˢ) (w×/tr₂ (ass ⊙ pf ⊙ assˢ) ˢ)
      }
      where open wpullback-sq-not (mkwpb-sq iswpb)


    wpbeq : {A B E : Obj} {f f' : || Hom A B ||} {e : || Hom E A ||} (pfeq : f ∘ e ~ f' ∘ e)
               → < f , f' > ∘ e ~ Δ B ∘ (f ∘ e)
    wpbeq pfeq = <>ar~<>ar (lidˢ _) (lidgenˢ (pfeq ˢ))

    isweql2iawpb : {A B E : Obj} {f f' : || Hom A B ||} {e : || Hom E A ||} {pfeq : f ∘ e ~ f' ∘ e}
                      → is-wequaliser pfeq → is-wpb-square (mksq (mksq/ (wpbeq pfeq)))
    isweql2iawpb {A} {B} {E} {f} {f'} {e} {pfeq} isweql = record
      { w⟨_,_⟩[_] = λ h k pf → h |weql[ sq2eql pf ]
      ; w×/tr₁ = λ pf → weqltr (sq2eql pf)
      ; w×/tr₂ = λ pf → assˢ ⊙ ∘e (weqltr (sq2eql pf)) r ⊙ aux₁ pf
      }
      where open is-wequaliser isweql
            aux₁ : {C : Obj} {h : || Hom C A ||} {k : || Hom C B ||}
                      → < f , f' > ∘ h ~ Δ B ∘ k → f ∘ h ~ k
            aux₁ {C} {h} {k} pf =
                         ~proof f ∘ h                    ~[ ∘e r (×tr₁ˢ {g = f'}) ⊙ assˢ ] /
                                π₁ ∘ < f , f' > ∘ h      ~[ ∘e pf r ⊙ ass ⊙ lidgg r ×tr₁ ]∎
                                k ∎
                                
            aux₂ : {C : Obj} {h : || Hom C A ||} {k : || Hom C B ||}
                      → < f , f' > ∘ h ~ Δ B ∘ k → f' ∘ h ~ k
            aux₂ {C} {h} {k} pf =
                         ~proof f' ∘ h                    ~[ ∘e r (×tr₂ˢ {f = f}) ⊙ assˢ ] /
                                π₂ ∘ < f , f' > ∘ h       ~[ ∘e pf r ⊙ ass ⊙ lidgg r ×tr₂ ]∎
                                k ∎
            
            sq2eql : {C : Obj} {h : || Hom C A ||} {k : || Hom C B ||}
                        → < f , f' > ∘ h ~ Δ B ∘ k → f ∘ h ~ f' ∘ h
            sq2eql {C} {h} {k} pf = aux₁ pf ⊙ aux₂ pf ˢ


    wpbof2weqlofᶜ : {A B : Obj} {f f' : || Hom A B ||} → wpullback-of f f' → wequaliser-of (f ∘ π₁) (f' ∘ π₂)
    wpbof2weqlofᶜ wpbof = record
      { wEql = ul
      ; weqlar = < wπ/₁ , wπ/₂ >
      ; weqleq = weqleq w×/iswpbsq
      ;isweql = iswpb2isweql w×/iswpbsq
      }
      where open wpullback-of-not wpbof


    weqlof2wpbofᶜ : {A B : Obj} {f f' : || Hom A B ||} → wequaliser-of f f' → wpullback-of < f , f' > (Δ B)
    weqlof2wpbofᶜ weqlof = record
      { w×/iswpbsq = isweql2iawpb isweql
      }
      where open wequaliser-of weqlof

  -- end wpb↔weqlᶜ
-}
