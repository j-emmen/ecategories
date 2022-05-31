
{-# OPTIONS --without-K #-}

module ecats.finite-limits.props.pullback where

open import Agda.Primitive
open import ecats.basic-defs.ecat-def&not
open import ecats.basic-defs.commut-shapes
open import ecats.basic-defs.isomorphism
open import ecats.basic-defs.epi&mono
open import ecats.basic-props.isomorphism
open import ecats.finite-limits.d&n-pullback
open import ecats.finite-limits.d&n-bin-product




-- Some properties of pullback squares

module pullback-props (ℂ : ecategory) where
  open ecategory-aux ℂ
  open iso-defs ℂ
  open iso-props ℂ
  open iso-transports ℂ 
  open epi&mono-defs ℂ
  open comm-shapes ℂ
  open pullback-squares ℂ
  open binary-products ℂ
  private
    module sq/ₙ = square/cosp
    module sqₙ = comm-square
    module pbofₙ = pullback-of
    module pbsqₙ = pb-square


  -- pullback extensionality

  ×/sqpf-irr : {I A B P : Obj}{a : || Hom A I ||}{b : || Hom B I ||}
               {p : || Hom P A ||}{q : || Hom P B ||}{pf : a ∘ p ~ b ∘ q}
                 → is-pullback pf  → (pf' : a ∘ p ~ b ∘ q) → is-pullback pf'
  ×/sqpf-irr ispb pf' = record
    { ⟨_,_⟩[_] = ⟨_,_⟩[_]
    ; ×/tr₁ = ×/tr₁
    ; ×/tr₂ = ×/tr₂
    ; ×/uq = ×/uq
    }
    where open is-pullback ispb


  ×/sqpf-irr-of : {I A B : Obj}{a : || Hom A I ||}{b : || Hom B I ||}{sq/ : square/cosp a b}
                     → is-pullback-of sq/ → (pf' : a ∘ sq/ₙ.left sq/ ~ b ∘ sq/ₙ.up sq/)
                       → is-pullback-of (mksq/ pf')
  ×/sqpf-irr-of {a = a} {b} {sq/} ispbof pf' = record
    { ispb = record
           { ⟨_,_⟩[_] = ⟨_,_⟩[_]
           ; ×/tr₁ = ×/tr₁
           ; ×/tr₂ = ×/tr₂
           ; ×/uq = ×/uq
           }
    }
    where open is-pullback-of ispbof
    -- Agda complains that pf != pf' when trying to use ×/sqpf-irr
{-
          module sq/ = sq/ₙ sq/
          module ispbof = is-pullback-of ispbof
          ispb' : is-pullback pf'
          ispb' = ×/sqpf-irr {pf = sq/.sq-pf} ispbof.ispb pf'
          module ispb' = is-pullback ispb'
-}
    

  ×/sqpf-irr-sq : {I A B P : Obj}{a : || Hom A I ||}{b : || Hom B I ||}{p₁ : || Hom P A ||}{p₂ : || Hom P B ||}
                  (pf pf' : a ∘ p₁ ~ b ∘ p₂)
                    → is-pb-square (mksq (mksq/ pf)) → is-pb-square (mksq (mksq/ pf'))
  ×/sqpf-irr-sq {a = a} {b} {p₁} {p₂} pf pf' ispb = record
    { ⟨_,_⟩[_] = pbpf.⟨_,_⟩[_]
    ; ×/tr₁ = pbpf.×/tr₁
    ; ×/tr₂ = pbpf.×/tr₂
    ; ×/uq = pbpf.×/uq
    }
    where module pbpf = pullback-sq-not (mkpb-sq ispb)

  ×/ext-dr : {I A B : Obj} {a a' : || Hom A I ||}{b b' : || Hom B I ||} {sq/ : square/cosp a b}
             (pbsq/ : is-pb-square (mksq sq/)) (pfa : a ~ a') (pfb : b ~ b')
               → is-pb-square (mksq (sq-ext sq/ pfa pfb))
  ×/ext-dr {I} {A} {B} {a} {a'} {b} {b'} {sq/} pbsq/ pfa pfb = record
    { ⟨_,_⟩[_] = λ h k pf' → ⟨ h , k ⟩[ ⟨⟩pf pf' ]
    ; ×/tr₁ = λ pf' → ×/tr₁ (⟨⟩pf pf')
    ; ×/tr₂ = λ pf' → ×/tr₂ (⟨⟩pf pf')
    ; ×/uq = ×/uq
    }
    where open is-pb-square pbsq/
          ⟨⟩pf : {C : Obj} {h : || Hom C A ||} {k : || Hom C B ||}
                    → a' ∘ h ~ b' ∘ k → a ∘ h ~ b ∘ k
          ⟨⟩pf pf' = ∘e r pfa ⊙ pf' ⊙ ∘e r (pfb ˢ)


  ×/ext-ul : {I A B P : Obj} {a : || Hom A I ||}{b : || Hom B I ||} --(pbof : pullback-of a b) (pbofₙ.ul pbof)
             {p₁ p₁' : || Hom P A ||} {p₂ p₂' : || Hom P B ||} {pfsq : a ∘ p₁ ~ b ∘ p₂} (pfsq' : a ∘ p₁' ~ b ∘ p₂')
               → is-pb-square (mksq (mksq/ pfsq)) → p₁' ~ p₁ → p₂' ~ p₂
                 → is-pb-square (mksq (mksq/ pfsq'))
  ×/ext-ul pfsq' ispb pfp₁ pfp₂ = record
    { ⟨_,_⟩[_] = λ h k pf → ⟨ h , k ⟩[ pf ]
    ; ×/tr₁ = λ pf → ∘e r pfp₁ ⊙ ×/tr₁ pf
    ; ×/tr₂ = λ pf → ∘e r pfp₂ ⊙ ×/tr₂ pf
    ; ×/uq = λ pf1 pf2 → ×/uq (∘e r (pfp₁ ˢ) ⊙ pf1 ⊙ ∘e r pfp₁)
                               (∘e r (pfp₂ ˢ) ⊙ pf2 ⊙ ∘e r pfp₂)
    }
    where open is-pb-square ispb


  ×/ext : {I A B P : Obj} {a a' : || Hom A I ||}{b b' : || Hom B I ||} {p₁ p₁' : || Hom P A ||} {p₂ p₂' : || Hom P B ||}
          (pfsq : a ∘ p₁ ~ b ∘ p₂) (pfsq' : a' ∘ p₁' ~ b' ∘ p₂')
          (pbsq/ : is-pb-square (mksq (mksq/ pfsq)))
            → a ~ a' → b ~ b' → p₁ ~ p₁' → p₂ ~ p₂'
              → is-pb-square (mksq (mksq/ pfsq'))
  ×/ext {I} {A} {B} {P} {a} {a'} {b} {b'} pfsq pfsq' pbsq pfa pfb pfp₁ pfp₂ = record
    { ⟨_,_⟩[_] = λ h k pf → ⟨ h , k ⟩[ ⟨⟩pf pf ]
    ; ×/tr₁ = λ pf → ∘e r (pfp₁ ˢ) ⊙ ×/tr₁ (⟨⟩pf pf)
    ; ×/tr₂ = λ pf → ∘e r (pfp₂ ˢ) ⊙ ×/tr₂ (⟨⟩pf pf)
    ; ×/uq = λ pf1 pf2 → ×/uq (∘e r pfp₁ ⊙ pf1 ⊙ ∘e r (pfp₁ ˢ))
                               (∘e r pfp₂ ⊙ pf2 ⊙ ∘e r (pfp₂ ˢ))
    }
    where open is-pb-square pbsq
          ⟨⟩pf : {C : Obj} {h : || Hom C A ||} {k : || Hom C B ||}
                    → a' ∘ h ~ b' ∘ k → a ∘ h ~ b ∘ k
          ⟨⟩pf pf' = ∘e r pfa ⊙ pf' ⊙ ∘e r (pfb ˢ)


  -- pb squares on same cospan are isomorphic

  pbs-unv12 : {A B I : Obj} {a : || Hom A I ||} {b : || Hom B I ||} (pb1 pb2 : pullback-of a b)
                  → || Hom (pbofₙ.ul pb1) (pbofₙ.ul pb2) ||
  pbs-unv12 pb1 pb2 = pb2.⟨ pb1.π/₁ , pb1.π/₂ ⟩[ pb1.×/sqpf ]
                    where module pb1 = pullback-of pb1
                          module pb2 = pullback-of pb2

  pbs-unv21 : {A B I : Obj} {a : || Hom A I ||} {b : || Hom B I ||} (pb1 pb2 : pullback-of a b)
                  → || Hom (pbofₙ.ul pb2) (pbofₙ.ul pb1) ||
  pbs-unv21 pb1 pb2 = pb1.⟨ pb2.π/₁ , pb2.π/₂ ⟩[ pb2.×/sqpf ]
                    where module pb1 = pullback-of pb1
                          module pb2 = pullback-of pb2

  pbs-unvar-is-isop : {A B I : Obj} {a : || Hom A I ||} {b : || Hom B I ||} (pb1 pb2 : pullback-of a b)
                      {uar12 : || Hom (pbofₙ.ul pb1) (pbofₙ.ul pb2) ||}{uar21 : || Hom (pbofₙ.ul pb2) (pbofₙ.ul pb1) ||}
                        → pbofₙ.π/₁ pb2 ∘ uar12 ~ pbofₙ.π/₁ pb1 → pbofₙ.π/₂ pb2 ∘ uar12 ~ pbofₙ.π/₂ pb1
                        → pbofₙ.π/₁ pb1 ∘ uar21 ~ pbofₙ.π/₁ pb2 → pbofₙ.π/₂ pb1 ∘ uar21 ~ pbofₙ.π/₂ pb2
                          → is-iso-pair uar12 uar21
  pbs-unvar-is-isop pb1 pb2 {uar12} {uar21} 12tr₁ 12tr₂ 21tr₁ 21tr₂ = record
    { iddom = pb1.×/uq (ass ⊙  ∘e r 21tr₁ ⊙ ridggˢ 12tr₁ r)
                       (ass ⊙  ∘e r 21tr₂ ⊙ ridggˢ 12tr₂ r)
    ; idcod = pb2.×/uq (ass ⊙  ∘e r 12tr₁ ⊙ ridggˢ 21tr₁ r)
                               (ass ⊙  ∘e r 12tr₂ ⊙ ridggˢ 21tr₂ r)
    }
    where module pb1 = pullback-of pb1
          module pb2 = pullback-of pb2

  pbs-unvar-is-iso : {A B I : Obj} {a : || Hom A I ||} {b : || Hom B I ||} (pb1 pb2 : pullback-of a b)
                     {uar : || Hom (pbofₙ.ul pb1) (pbofₙ.ul pb2) ||}
                       → pbofₙ.π/₁ pb2 ∘ uar ~ pbofₙ.π/₁ pb1 → pbofₙ.π/₂ pb2 ∘ uar ~ pbofₙ.π/₂ pb1
                         → is-iso uar
  pbs-unvar-is-iso pb1 pb2 {uar} tr₁ tr₂ = record
    { invf = pbs-unv21 pb1 pb2
    ; isisopair = pbs-unvar-is-isop pb1 pb2 tr₁ tr₂ (pb1.×/tr₁ pb2.×/sqpf) (pb1.×/tr₂ pb2.×/sqpf)
    }
    where module pb1 = pullback-of pb1
          module pb2 = pullback-of pb2

  pbs-unv-is-isop : {A B I : Obj} {a : || Hom A I ||} {b : || Hom B I ||} (pb1 pb2 : pullback-of a b)
                       → is-iso-pair (pbs-unv12 pb1 pb2) (pbs-unv21 pb1 pb2)
  pbs-unv-is-isop pb1 pb2 = pbs-unvar-is-isop pb1 pb2
                                              (pb2.×/tr₁ pb1.×/sqpf) (pb2.×/tr₂ pb1.×/sqpf)
                                              (pb1.×/tr₁ pb2.×/sqpf) (pb1.×/tr₂ pb2.×/sqpf)
                          where module pb1 = pullback-of pb1
                                module pb2 = pullback-of pb2

  pbs-unv-is-iso : {A B I : Obj} {a : || Hom A I ||} {b : || Hom B I ||} (pb1 pb2 : pullback-of a b)
                       → is-iso (pbs-unv12 pb1 pb2)
  pbs-unv-is-iso pb1 pb2 = record
    { invf = pbs-unv21 pb1 pb2
    ; isisopair = pbs-unv-is-isop pb1 pb2
    }


  -- span isomorphic to a pb is pb

  sp≅pb-is-pb : {A B I : Obj} {a : || Hom A I ||} {b : || Hom B I ||} (pb : pullback-of a b) {sq : square/cosp a b}
                  --(pbsq1 : is-pb-square (mksq span1))
                  {f : || Hom (sq/ₙ.ul sq) (pbofₙ.ul pb) ||}
                    → is-iso f → pbofₙ.π/₁ pb ∘ f ~ sq/ₙ.left sq → pbofₙ.π/₂ pb ∘ f ~ sq/ₙ.up sq
                      → is-pb-square (mksq sq)
  sp≅pb-is-pb pb {sq} {f} isof tr1 tr2 = record
    { ⟨_,_⟩[_] = λ h k pf → invf ∘ pb.⟨ h , k ⟩[ pf ]
    ; ×/tr₁ = λ {_} {h} {k} pf → ~proof sq.left ∘ invf ∘ pb.⟨ h , k ⟩[ pf ]            ~[ ass ⊙ ∘e r invtr1 ] /
                                                   pb.π/₁ ∘ pb.⟨ h , k ⟩[ pf ]          ~[ pb.×/tr₁ pf ]∎
                                                   h ∎
    ; ×/tr₂ = λ {_} {h} {k} pf → ~proof sq.up ∘ invf ∘ pb.⟨ h , k ⟩[ pf ]              ~[ ass ⊙ ∘e r invtr2 ] /
                                                  pb.π/₂ ∘ pb.⟨ h , k ⟩[ pf ]          ~[ pb.×/tr₂ pf ]∎
                                                  k ∎
    ; ×/uq = λ {_} {h} {h'} pf1 pf2 → ~proof h               ~[ lidggˢ r iddom ⊙ assˢ ] /
                                          invf ∘ f ∘ h         ~[ ∘e (pb.×/uq (uqtr1 pf1) (uqtr2 pf2)) r ] /
                                          invf ∘ f ∘ h'        ~[ ass ⊙ lidgg r iddom ]∎
                                          h' ∎
    }
    where module pb = pullback-of pb
          module sq = square/cosp sq
          open is-iso isof
          invtr1 = ~proof sq.left ∘ invf     ~[ ∘e r (tr1 ˢ) ⊙ assˢ ] /
                          pb.π/₁ ∘ f ∘ invf   ~[ ridgg r idcod ]∎                          
                          pb.π/₁ ∎
          invtr2 = ~proof sq.up ∘ invf       ~[ ∘e r (tr2 ˢ) ⊙ assˢ ] /
                          pb.π/₂ ∘ f ∘ invf   ~[ ridgg r idcod ]∎                          
                          pb.π/₂ ∎
          uqtr1 : {C : Obj} {h h' : || Hom C sq.ul ||} → sq.left ∘ h ~ sq.left ∘ h' → pb.π/₁ ∘ f ∘ h ~ pb.π/₁ ∘ f ∘ h'
          uqtr1 {h = h} {h'} pf = ~proof pb.π/₁ ∘ f ∘ h     ~[ ass ⊙ ∘e r tr1 ] /
                                         sq.left ∘ h       ~[ pf ] /
                                         sq.left ∘ h'      ~[ ∘e r (tr1 ˢ) ⊙ assˢ ]∎
                                         pb.π/₁ ∘ f ∘ h' ∎
          uqtr2 : {C : Obj} {h h' : || Hom C sq.ul ||} → sq.up ∘ h ~ sq.up ∘ h' → pb.π/₂ ∘ f ∘ h ~ pb.π/₂ ∘ f ∘ h'
          uqtr2 {h = h} {h'} pf = ~proof pb.π/₂ ∘ f ∘ h     ~[ ass ⊙ ∘e r tr2 ] /
                                         sq.up ∘ h         ~[ pf ] /
                                         sq.up ∘ h'        ~[ ∘e r (tr2 ˢ) ⊙ assˢ ]∎
                                         pb.π/₂ ∘ f ∘ h' ∎



  -- symmetric pb square is pb

  diag-sym-pb-sq : {sq : comm-square} → is-pb-square sq → is-pb-square (diag-sym-square sq)
  diag-sym-pb-sq {sq} ispbsq = record
    { ⟨_,_⟩[_] = λ h k pf → ⟨ k , h ⟩[ pf ˢ ]
    ; ×/tr₁ = λ pf → ×/tr₂ (pf ˢ)
    ; ×/tr₂ = λ pf → ×/tr₁ (pf ˢ)
    ; ×/uq = λ pf₁ pf₂ → ×/uq pf₂ pf₁
    }
    where open pullback-sq-not (mkpb-sq ispbsq)

  diag-sym-pb-sq-inv : {sq : comm-square} → is-pb-square (diag-sym-square sq) → is-pb-square sq
  diag-sym-pb-sq-inv {sq} ispbsq = record
    { ⟨_,_⟩[_] = λ h k pf → ⟨ k , h ⟩[ pf ˢ ]
    ; ×/tr₁ = λ pf → ×/tr₂ (pf ˢ)
    ; ×/tr₂ = λ pf → ×/tr₁ (pf ˢ)
    ; ×/uq = λ pf₁ pf₂ → ×/uq pf₂ pf₁
    }
    where open pullback-sq-not (mkpb-sq ispbsq)


  diag-sym-pbof : {I A B : Obj} {a : || Hom A I ||} {b : || Hom B I ||}
                     → pullback-of a b → pullback-of b a
  diag-sym-pbof pbof = mkpb-of (diag-sym-pb-sq ×/ispbsq)
                     where open pullback-of pbof



  -- pasting properties of pb squares

  module lower-and-upper-so-outer {DL DR UR UL UUR : Obj} {down : || Hom DL DR ||} {right : || Hom UR DR ||}
                                  {left : || Hom UL DL ||} {up : || Hom UL UR ||} {lowsq-pf : down ∘ left ~ right ∘ up}
                                  (low-pb : is-pb-square (mksq (mksq/ lowsq-pf)))
                                  {right' : || Hom UUR UR ||} (up-pb : pullback-of up right')
                                  where
    private
      module lowpb = pullback-of (mkpb-of low-pb)
      module uppb = pullback-of up-pb

    any-outer-is-pbsq : {rlong : || Hom UUR DR ||} (r-tr : right ∘ right' ~ rlong)
                        (sqpf : down ∘ (left ∘ uppb.π/₁) ~ rlong ∘ uppb.π/₂)
                          → is-pb-square (mksq (mksq/ sqpf))
    any-outer-is-pbsq {rlong} r-tr sqpf = record
      { ⟨_,_⟩[_] = univ
      ; ×/tr₁ = outtr₁
      ; ×/tr₂ = outtr₂
      ; ×/uq = outuq
      }
      where univl-pf : {D : Obj} {h : || Hom D DL ||} {k : || Hom D UUR ||}
                         → down ∘ h ~ rlong ∘ k → down ∘ h ~ right ∘ right' ∘ k
            univl-pf {h = h} {k} pf = pf ⊙ ∘e r (r-tr ˢ) ⊙ assˢ
            univ-pf : {D : Obj} {h : || Hom D DL ||} {k : || Hom D UUR ||} (pf : down ∘ h ~ rlong ∘ k)
                           → up ∘ lowpb.⟨ h , right' ∘ k ⟩[ univl-pf pf ] ~ right' ∘ k
            univ-pf {h = h} {k} pf = lowpb.×/tr₂ (univl-pf pf)
            univ : {D : Obj} (h : || Hom D DL ||) (k : || Hom D UUR ||)
                      → down ∘ h ~ rlong ∘ k → || Hom D uppb.ul ||
            univ h k pf = uppb.⟨ lowpb.⟨ h , right' ∘ k ⟩[ univl-pf pf ] , k ⟩[ univ-pf pf ]
            outtr₁ : {D : Obj} {h : || Hom D DL ||} {k : || Hom D UUR ||} (pf : down ∘ h ~ rlong ∘ k)
                       → (left ∘ uppb.π/₁) ∘ univ h k pf ~ h
            outtr₁ {h = h} {k} pf = assˢ ⊙ ∘e (uppb.×/tr₁ (univ-pf pf)) r ⊙ lowpb.×/tr₁ (univl-pf pf)
            outtr₂ : {D : Obj} {h : || Hom D DL ||} {k : || Hom D UUR ||} (pf : down ∘ h ~ rlong ∘ k)
                       → uppb.π/₂ ∘ univ h k pf ~ k
            outtr₂ {h = h} {k} pf = uppb.×/tr₂ (univ-pf pf)
            outuq : {D : Obj} {h h' : || Hom D uppb.ul ||}
                      → (left ∘ uppb.π/₁) ∘ h ~ (left ∘ uppb.π/₁) ∘ h' → uppb.π/₂ ∘ h ~ uppb.π/₂ ∘ h'
                        → h ~ h'
            outuq pf₁ pf₂ = uppb.×/uq (lowpb.×/uq (ass ⊙ pf₁ ⊙ assˢ)
                                                 (ass ⊙ ∘e r uppb.×/sqpf ⊙ assˢ ⊙ ∘e pf₂ r
                                                 ⊙ ass ⊙ ∘e r (uppb.×/sqpf ˢ) ⊙ assˢ))
                                     pf₂


    outsq-pf : {rlong : || Hom UUR DR ||} (r-tr : right ∘ right' ~ rlong)
                      → down ∘ (left ∘ uppb.π/₁) ~ rlong ∘ uppb.π/₂
    outsq-pf {rlong} r-tr = ass ⊙ ∘e r lowpb.×/sqpf ⊙ assˢ ⊙ ∘e uppb.×/sqpf r ⊙ ass ⊙ ∘e r r-tr


    outer-is-pbsq : {rlong : || Hom UUR DR ||} (r-tr : right ∘ right' ~ rlong)
                      → is-pb-square (mksq (mksq/ (outsq-pf r-tr)))
    outer-is-pbsq {rlong} r-tr = any-outer-is-pbsq r-tr (outsq-pf r-tr)

    outer-pbof : {rlong : || Hom UUR DR ||} (r-tr : right ∘ right' ~ rlong)
                      → pullback-of down rlong
    outer-pbof r-tr = mkpb-of (outer-is-pbsq  r-tr)
    
  -- end lower-and-upper-so-outer


  module right-and-left-so-outer {DL DR UR UL DLL : Obj} {down : || Hom DL DR ||} {right : || Hom UR DR ||}
                                 {left : || Hom UL DL ||} {up : || Hom UL UR ||} {rightsq-pf : down ∘ left ~ right ∘ up}
                                 (right-pb : is-pb-square (mksq (mksq/ rightsq-pf)))
                                 {down' : || Hom DLL DL ||} (left-pb : pullback-of down' left)
                                 where
    private
      module rpb = pullback-of (mkpb-of right-pb)
      module lpb = pullback-of left-pb
      module rpb-sym = pullback-of (diag-sym-pbof (mkpb-of right-pb))
      module sym = lower-and-upper-so-outer rpb-sym.×/ispbsq (diag-sym-pbof left-pb)

    any-outer-is-pbsq : {dlong : || Hom DLL DR ||} (d-tr : down ∘ down' ~ dlong)
                        (sqpf : dlong ∘ lpb.π/₁ ~ right ∘ (rpb.π/₂ ∘ lpb.π/₂))
                               → is-pb-square (mksq (mksq/ sqpf))
    any-outer-is-pbsq {dlong} d-tr sqpf = diag-sym-pb-sq-inv (sym.any-outer-is-pbsq d-tr (sqpf ˢ))

    outsq-pf : {dlong : || Hom DLL DR ||} (d-tr : down ∘ down' ~ dlong)
                      → dlong ∘ lpb.π/₁ ~ right ∘ (rpb.π/₂ ∘ lpb.π/₂)
    outsq-pf d-tr = sym.outsq-pf d-tr ˢ

    outer-is-pbsq : {dlong : || Hom DLL DR ||} (d-tr : down ∘ down' ~ dlong)
                      → is-pb-square (mksq (mksq/ (outsq-pf d-tr)))
    outer-is-pbsq d-tr = any-outer-is-pbsq d-tr (outsq-pf d-tr)

    outer-pbof : {dlong : || Hom DLL DR ||} (d-tr : down ∘ down' ~ dlong)
                      → pullback-of dlong right
    outer-pbof d-tr = mkpb-of (outer-is-pbsq  d-tr)


  --end right-and-left-so-outer



  module lower-and-outer-so-upper {DL DR UR UUR : Obj} {down : || Hom DL DR ||}
                                  {right : || Hom UR DR ||} {right' : || Hom UUR DR ||}
                                  (low-pb : pullback-of down right) (out-pb : pullback-of down right')
                                  where
    private
      module lowpb = pullback-of low-pb
      module outpb = pullback-of out-pb

    can-l-fill-pf : {r-fill : || Hom UUR UR ||} (r-tr : right ∘ r-fill ~ right')
                            → down ∘ outpb.π/₁ ~ right ∘ r-fill ∘ outpb.π/₂
    can-l-fill-pf r-tr = outpb.×/sqpf ⊙ ∘e r (r-tr ˢ) ⊙ assˢ
    can-l-fill : {r-fill : || Hom UUR UR ||} (r-tr : right ∘ r-fill ~ right')
                         → || Hom outpb.ul lowpb.ul ||
    can-l-fill {r-fill} r-tr = lowpb.⟨ outpb.π/₁ , r-fill ∘ outpb.π/₂ ⟩[ can-l-fill-pf r-tr ]
    can-l-fill-tr : {r-fill : || Hom UUR UR ||} (r-tr : right ∘ r-fill ~ right')
                            → lowpb.π/₁ ∘ can-l-fill r-tr ~ outpb.π/₁
    can-l-fill-tr r-tr = lowpb.×/tr₁ (can-l-fill-pf r-tr)

    can-upsq-pf : {r-fill : || Hom UUR UR ||} (r-tr : right ∘ r-fill ~ right')
                          → lowpb.π/₂ ∘ can-l-fill r-tr ~ r-fill ∘ outpb.π/₂
    can-upsq-pf r-tr = lowpb.×/tr₂ (can-l-fill-pf r-tr)
    
    upper-is-pbsq : {r-fill : || Hom UUR UR ||} {l-fill : || Hom outpb.ul lowpb.ul ||}
                    (r-tr : right ∘ r-fill ~ right') (l-tr : lowpb.π/₁ ∘ l-fill ~ outpb.π/₁)
                    (up-comm : lowpb.π/₂ ∘ l-fill ~ r-fill ∘ outpb.π/₂)
                      → is-pb-square (mksq (mksq/ up-comm))
    upper-is-pbsq {r-fill} {l-fill} r-tr l-tr up-comm = record
      { ⟨_,_⟩[_] = univ
      ; ×/tr₁ = uptr₁
      ; ×/tr₂ = uptr₂
      ; ×/uq = upuq
      }
      where univ-pf : {D : Obj} {h : || Hom D lowpb.ul ||} {k : || Hom D UUR ||}
                         → lowpb.π/₂ ∘ h ~ r-fill ∘ k → down ∘ lowpb.π/₁ ∘ h ~ right' ∘ k
            univ-pf {h = h} {k} pf = ~proof down ∘ lowpb.π/₁ ∘ h      ~[ ass ⊙ ∘e r lowpb.×/sqpf ⊙ assˢ ] /
                                            right ∘ lowpb.π/₂ ∘ h      ~[ ∘e pf r ⊙ ass ⊙ ∘e r r-tr ]∎
                                            right' ∘ k ∎
            univ : {D : Obj} (h : || Hom D lowpb.ul ||) (k : || Hom D UUR ||)
                      → lowpb.π/₂ ∘ h ~ r-fill ∘ k → || Hom D outpb.ul ||
            univ h k pf = outpb.⟨ lowpb.π/₁ ∘ h , k ⟩[ univ-pf pf ]
            uptr₁ : {D : Obj} {h : || Hom D lowpb.ul ||} {k : || Hom D UUR ||} (pf : lowpb.π/₂ ∘ h ~ r-fill ∘ k)
                       → l-fill ∘ univ h k pf ~ h
            uptr₁ {h = h} {k} pf = lowpb.×/uq (ass ⊙ ∘e r l-tr ⊙ outpb.×/tr₁ (univ-pf pf))
                                              (ass ⊙ ∘e r up-comm ⊙ assˢ ⊙ ∘e (outpb.×/tr₂ (univ-pf pf)) r ⊙ pf ˢ)
            uptr₂ : {D : Obj} {h : || Hom D lowpb.ul ||} {k : || Hom D UUR ||} (pf : lowpb.π/₂ ∘ h ~ r-fill ∘ k)
                       → outpb.π/₂ ∘ univ h k pf ~ k
            uptr₂ {h = h} {k} pf = outpb.×/tr₂ (univ-pf pf)
            upuq : {D : Obj} {h h' : || Hom D outpb.ul ||} → l-fill ∘ h ~ l-fill ∘ h' → outpb.π/₂ ∘ h ~ outpb.π/₂ ∘ h'
                      → h ~ h'
            upuq pf₁ pf₂ = outpb.×/uq (∘e r (l-tr ˢ) ⊙ assˢ ⊙ ∘e pf₁ r ⊙ ass ⊙ ∘e r l-tr) pf₂

    upper-pbof : {r-fill : || Hom UUR UR ||} {l-fill : || Hom outpb.ul lowpb.ul ||}
                 (r-tr : right ∘ r-fill ~ right') (l-tr : lowpb.π/₁ ∘ l-fill ~ outpb.π/₁)
                 (up-comm : lowpb.π/₂ ∘ l-fill ~ r-fill ∘ outpb.π/₂)
                   → pullback-of lowpb.π/₂ r-fill
    upper-pbof r-tr l-tr up-comm = mkpb-of (upper-is-pbsq r-tr l-tr up-comm)
    
    can-up-pbof : {r-fill : || Hom UUR UR ||} (r-tr : right ∘ r-fill ~ right')
                            → pullback-of lowpb.π/₂ r-fill
    can-up-pbof r-tr = upper-pbof r-tr (can-l-fill-tr r-tr) (can-upsq-pf r-tr)
  -- end lower-and-outer-so-upper


  module right-and-outer-so-left {DR UR DLL DL : Obj} {right : || Hom UR DR ||} {down : || Hom DL DR ||} {down' : || Hom DLL DR ||}
                                 (rpb : pullback-of down right) (outpb : pullback-of down' right) where
    private
      module rpb = pullback-of rpb
      module outpb = pullback-of outpb

    left-is-pbsq : {d-fill : || Hom DLL DL ||} {u-fill : || Hom outpb.ul rpb.ul ||}
                   (d-tr : down ∘ d-fill ~ down') (u-tr : rpb.π/₂ ∘ u-fill ~ outpb.π/₂)
                   (l-sq-comm : d-fill ∘ outpb.π/₁ ~ rpb.π/₁ ∘ u-fill)
                     → is-pb-square (mksq (mksq/ l-sq-comm))
    left-is-pbsq {d-fill} {u-fill} d-tr u-tr l-sq-comm = diag-sym-pb-sq-inv (upper-is-pbsq d-tr u-tr (l-sq-comm ˢ))
                                                       where open lower-and-outer-so-upper (diag-sym-pbof rpb) (diag-sym-pbof outpb)

  --end right-and-outer-so-left



{-
  -- if down and right arrows factor through same arrow and inner square commutes,
  -- then if outer square is pullback so is inner one

  sub-pb-sq : {sq : comm-square} {dr' : Obj} {down' : || Hom (sqₙ.dl sq) dr' ||} {right' : || Hom (sqₙ.ur sq) dr' ||}
              (pfsq' : down' ∘ sqₙ.left sq ~ right' ∘ sqₙ.up sq) {f : || Hom dr' (sqₙ.dr sq) ||}
                → f ∘ down' ~ sqₙ.down sq → f ∘ right' ~ sqₙ.right sq → is-pb-square sq
                  → is-pb-square (mksq (mksq/ pfsq'))
  sub-pb-sq {sq} {dr'} {down'} {right'} pfsq' {f} d-tr r-tr ispb = record
    { ⟨_,_⟩[_] = λ h k pf → pbsq.⟨ h , k ⟩[ aux pf ]
    ; ×/tr₁ = λ pf → pbsq.×/tr₁ (aux pf)
    ; ×/tr₂ =  λ pf → pbsq.×/tr₂ (aux pf)
    ; ×/uq = pbsq.×/uq
    }
    where module pbsq = is-pb-square ispb
          open comm-square sq
          aux : {C : Obj} {h : || Hom C dl ||} {k : || Hom C ur ||}
                   → down' ∘ h ~ right' ∘ k → down ∘ h ~ right ∘ k
          aux pf = ∘e r (d-tr ˢ) ⊙  assˢ ⊙ ∘e pf r ⊙ ass ⊙ ∘e r r-tr
-}

  -- if arrows in a cospan factor through the same arrow, giving rise to another cospan,
  -- then a pullback of the first cospan is a pullback of the second one if the square commutes.

  subsq-of-pb-is-pb : {dr dr' dl ur : Obj} {down : || Hom dl dr ||} {right : || Hom ur dr ||}
                      (pb : pullback-of down right) {down' : || Hom dl dr' ||} {right' : || Hom ur dr' ||}
                      (subsqpf : down' ∘ pbofₙ.π/₁ pb ~ right' ∘ pbofₙ.π/₂ pb) {m : || Hom dr' dr ||}
                        → m ∘ down' ~ down → m ∘ right' ~ right → is-pb-square (mksq (mksq/ subsqpf))
  subsq-of-pb-is-pb {dr} {dr'} {dl} {ur} {down} {right} pb {down'} {right'} ssqpf {m} trd trr = record
    { ⟨_,_⟩[_] = λ h k pf → pb.⟨ h , k ⟩[ trsp-pf pf ] 
    ; ×/tr₁ = λ pf → pb.×/tr₁ (trsp-pf pf)
    ; ×/tr₂ = λ pf → pb.×/tr₂ (trsp-pf pf)
    ; ×/uq = pb.×/uq
    }
    where module pb = pullback-of-not pb
          trsp-pf : {A : Obj} {h : || Hom A dl ||} {k : || Hom A ur ||}
                       → down' ∘ h ~ right' ∘ k → down ∘ h ~ right ∘ k
          trsp-pf pf = ∘e r (trd ˢ) ⊙ assˢ ⊙ ∘e pf r ⊙ ass ⊙ ∘e r trr

  -- given a mono between bottomo-right corners
  -- if outer square commutes/is pb then so is inner one

  monic-sub-sq-canpf : (sq : comm-square) {dr' : Obj} {down' : || Hom (sqₙ.dl sq) dr' ||} {right' : || Hom (sqₙ.ur sq) dr' ||}
                    {m : || Hom dr' (sqₙ.dr sq) ||} (trd : m ∘ down' ~ sqₙ.down sq) (trr : m ∘ right' ~ sqₙ.right sq)
                    (pfm : is-monic m) → down' ∘ sqₙ.left sq ~ right' ∘ sqₙ.up sq
  monic-sub-sq-canpf sq trd trr pfm = m.mono-pf (ass ⊙ ∘e r trd ⊙ sq.sq-pf ⊙ ∘e r (trr ˢ) ⊙ assˢ)
                                       where module sq = comm-square sq
                                             module m = is-monic pfm

  monic-sub-sq : (sq : comm-square) {dr' : Obj} {down' : || Hom (sqₙ.dl sq) dr' ||} {right' : || Hom (sqₙ.ur sq) dr' ||} {m : || Hom dr' (sqₙ.dr sq) ||}
                     → m ∘ down' ~ sqₙ.down sq → m ∘ right' ~ sqₙ.right sq → is-monic m → comm-square
  monic-sub-sq sq trd trr pfm = mksq (mksq/ (monic-sub-sq-canpf sq trd trr pfm))

  monic-sub-pb-sq : (pbsq : pb-square) {dr' : Obj} {down' : || Hom (pbsqₙ.dl pbsq) dr' ||} {right' : || Hom (pbsqₙ.ur pbsq) dr' ||}
                    {m : || Hom dr' (pbsqₙ.dr pbsq) ||} (trd : m ∘ down' ~ pbsqₙ.down pbsq) (trr : m ∘ right' ~ pbsqₙ.right pbsq)
                    (pfm : is-monic m) → is-pb-square (monic-sub-sq (pbsqₙ.×/sq pbsq) trd trr pfm)
  monic-sub-pb-sq pbsq trd trr pfm = subsq-of-pb-is-pb pbsq.×/of (monic-sub-sq-canpf pbsq.×/sq trd trr pfm) trd trr
                                   where module pbsq = pullback-sq-not pbsq

          


{-
  -- square with vertical identities is a pullback
  idar-sq-is-pb : {A B : Obj} (f : || Hom A B ||) → is-pb-square (mksq (mksq/ (rid f ⊙ lidˢ f)))
  idar-sq-is-pb f = record { ⟨_,_⟩[_] = λ h k pf → h
                           ; ×/tr₁ =  λ {_} {h} {k} pf → lid h
                           ; ×/tr₂ = λ {_} {h} {k} pf → pf ⊙ lid k
                           ; ×/uq = λ {_} {h} {h'} pf₁ pf₂ → lidˢ h ⊙ pf₁ ⊙ lid h'
                           }
-}

  -- square with two parallel identites is pullback

  -- idar ∘ a ~ a ∘ idar
  triv-pbsq : {A I : Obj} (a : || Hom A I ||) → is-pb-square (mksq (mksq/ (lidgen (ridˢ {f = a}))))
  triv-pbsq a = record
    { ⟨_,_⟩[_] = λ h k pf → k
    ; ×/tr₁ = λ pf → pf ˢ ⊙ lid
    ; ×/tr₂ = λ pf → lid
    ; ×/uq = λ pf₁ pf₂ → lidˢ ⊙ pf₂ ⊙ lid
    }
    
  triv-pbsqˢ : {A I : Obj} (a : || Hom A I ||) → is-pb-square (mksq (mksq/ (ridgen (lidˢ {f = a}))))
  triv-pbsqˢ a = ×/sqpf-irr-sq (trsqˢ.sq-pf) (ridgen lidˢ) (diag-sym-pb-sq trpb.×/ispbsq)
               where module trpb = pullback-of-not (mkpb-of (triv-pbsq a))
                     module trsqˢ = comm-square (diag-sym-square (mksq trpb.×/sq/))


  -- pullbacks and isos

  pbof-iso : {I A B : Obj} {i : || Hom A I ||} (f : || Hom B I ||)
                → is-iso i → pullback-of f i
  pbof-iso {i = i} f isiso = record
    { ×/sq/ = mksq/ (ridgen (lidggˢ r idcod ⊙ assˢ))
    ; ×/ispbsq = record
      { ⟨_,_⟩[_] = λ h _ _ → h
      ; ×/tr₁ = λ _ → lid
      ; ×/tr₂ = invpf
      ; ×/uq = λ pf _ → lidˢ ⊙ pf ⊙ lid
      }
    }
    where open is-iso isiso renaming (invf to invi)
          invpf  : {C : Obj} {h : || Hom C _ ||} {k : || Hom C _ ||}
                      → f ∘ h ~ i ∘ k → (invi ∘ f) ∘ h ~ k
          invpf pf = assˢ ⊙ ∘e pf r ⊙ ass ⊙ lidgg r iddom

  pb-alng-iso : (sq : comm-square) → is-iso (sqₙ.down sq) → is-iso (sqₙ.up sq)
                     → is-pb-square sq
  pb-alng-iso sq disiso uisiso = record
    { ⟨_,_⟩[_] = λ h k pf → u.invf ∘ k
    ; ×/tr₁ = λ pf → ass ⊙ ∘e r (inv-sq ˢ) ⊙ assˢ ⊙ ∘e (pf ˢ) r ⊙ ass ⊙ lidgg r d.iddom
    ; ×/tr₂ = λ pf → ass ⊙ lidgg r u.idcod
    ; ×/uq = λ pf₁ pf₂ → lidggˢ r u.iddom ⊙ assˢ ⊙ ∘e pf₂ r ⊙ ass ⊙ lidgg r u.iddom
    }
    where open comm-square sq
          module d = is-iso disiso
          module u = is-iso uisiso
          inv-sq : d.invf ∘ right ~ left ∘ u.invf
          inv-sq = iso-sq u.isisopair d.isisopair sq-pf


  -- pullback from product projections

  module pullback-sq-from-π₁ {A I : Obj} (a : || Hom A I ||) {B : Obj}
                             (A×B : product-of A B) (I×B : product-of I B)
                             where
    private
      module A×B = product-of-not A×B
      module I×B = product-of-not I×B
      open ×ₐdef I×B.prdsp A×B.prdsp
      module ×ₐ = ×ₐnot2-only I×B.prdsp A×B.prdsp
    
    sqpf : a ∘ A×B.π₁ ~ I×B.π₁ ∘ a ×ₐ idar B
    sqpf = I×B.×tr₁ ˢ

    pbsq : pb-square
    pbsq = record
      { ×/sq = mksq (mksq/ sqpf)
      ; ×/ispbsq = record
        { ⟨_,_⟩[_] = λ h k _ → A×B.< h , I×B.π₂ ∘ k >
        ; ×/tr₁ = λ _ → A×B.×tr₁
        ; ×/tr₂ = λ pf → ×ₐ.×ₐ<>~ar (pf ˢ) lidˢ
        ; ×/uq = λ {_} {h} {h'} pf₁ pf₂ →
               A×B.×uq pf₁
                       (~proof A×B.π₂ ∘ h                 ~[ ∘e r (lidˢ ⊙ I×B.×tr₂ˢ) ⊙ assˢ ] /
                               I×B.π₂ ∘ a ×ₐ idar B ∘ h   ~[ ∘e pf₂ r ] /
                               I×B.π₂ ∘ a ×ₐ idar B ∘ h'  ~[ ass ⊙ ∘e r (I×B.×tr₂ ⊙ lid) ]∎
                               A×B.π₂ ∘ h' ∎)
        }
      }
  -- end pullback-sq-from-π₁


  pb-alng-π₁ : {A I : Obj} (a : || Hom A I ||) {B : Obj}
               (A×B : product-of A B) (I×B : product-of I B)
                → pb-square
  pb-alng-π₁ a A×B I×B = pbsq
                       where open pullback-sq-from-π₁ a A×B I×B
                         


  -- preservation of property under pullback

  record is-pbsq-stable {ℓ} (Propos : {X Y : Obj} → || Hom X Y || → Set ℓ) : Set (lsuc lzero ⊔ ℓ) where
    open pb-square
    field
      pres-rl : (pbsq : pb-square) → Propos (pbsqₙ.right pbsq) → Propos (pbsqₙ.π/₁ pbsq)
    pres-du : (pbsq : pb-square) → Propos (pbsqₙ.down pbsq) → Propos (pbsqₙ.π/₂ pbsq)
    pres-du pbsq pf = pres-rl (mkpb-sq (diag-sym-pb-sq (pbsqₙ.×/ispbsq pbsq))) pf

  record is-pbof-stable {ℓ} (Propos : {X Y : Obj} → || Hom X Y || → Set ℓ) : Set (lsuc lzero ⊔ ℓ) where
    open pullback-of
    field
      pres-rl : {A B : Obj} {c : || Hom A B ||} {C : Obj} {f : || Hom C B ||} (pbof : pullback-of f c)
                   → Propos c → Propos (π/₁ pbof)
    pres-du : {A B : Obj} {c : || Hom A B ||} {C : Obj} {f : || Hom C B ||} (pbof : pullback-of c f)
                   → Propos c → Propos (π/₂ pbof)
    pres-du pbof = pres-rl (diag-sym-pbof pbof)

  pbsq-stb→pbof-stb : {ℓ : Level} {Propos : {X Y : Obj} → || Hom X Y || → Set ℓ}
                           → is-pbsq-stable Propos → is-pbof-stable Propos
  pbsq-stb→pbof-stb {Propos} pbsqstb = record
    { pres-rl = λ pbof isPropos → pres-rl (×/pbsq pbof) isPropos
    }
    where open is-pbsq-stable pbsqstb
          open pullback-of-not 

  pbof-stb→pbsq-stb : {ℓ : Level} {Propos : {X Y : Obj} → || Hom X Y || → Set ℓ}
                           → is-pbof-stable Propos → is-pbsq-stable Propos
  pbof-stb→pbsq-stb {Propos} pbofstb = record
    { pres-rl = λ pbsq isPropos → pres-rl (×/of pbsq) isPropos
    }
    where open is-pbof-stable pbofstb
          open pullback-sq-not

  pbof-stb-trsp : {ℓ₁ ℓ₂ : Level} {P : {X Y : Obj} → || Hom X Y || → Set ℓ₁}
                  {Q : {X Y : Obj} → || Hom X Y || → Set ℓ₂}
                  (P→Q : ∀ {X Y} → ∀ {f : || Hom X Y ||} → P f → Q f)
                  (Q→P : ∀ {X Y} → ∀ {f : || Hom X Y ||} → Q f → P f)
                      → is-pbof-stable P → is-pbof-stable Q
  pbof-stb-trsp P→Q Q→P stbP = record
    { pres-rl = λ pbof pfQ → P→Q (stbP.pres-rl pbof (Q→P pfQ))
    }
    where module stbP = is-pbof-stable stbP

  pbsq-stb-trsp :  {ℓ₁ ℓ₂ : Level} {P : {X Y : Obj} → || Hom X Y || → Set ℓ₁}
                   {Q : {X Y : Obj} → || Hom X Y || → Set ℓ₂}
                   (P→Q : ∀ {X Y} → ∀ {f : || Hom X Y ||} → P f → Q f)
                   (Q→P : ∀ {X Y} → ∀ {f : || Hom X Y ||} → Q f → P f)
                      → is-pbsq-stable P → is-pbsq-stable Q
  pbsq-stb-trsp P→Q Q→P stbP = record
    { pres-rl = λ pbsq pfQ → P→Q (stbP.pres-rl pbsq (Q→P pfQ))
    }
    where module stbP = is-pbsq-stable stbP


  module pb-over-pbof (haspb : has-pullbacks ℂ)
                      {I A B : Obj}{a : || Hom A I ||}{b : || Hom B I ||}(pb : pullback-of a b)
                      {A' B' : Obj}(f : || Hom A' A ||)(g : || Hom B' B ||)
                      where
    open has-pullbacks haspb
    module inpb = pullback-of-not pb
    lpb : pullback-of f inpb.π/₁
    lpb = pb-of f inpb.π/₁
    upb : pullback-of inpb.π/₂ g
    upb = pb-of inpb.π/₂ g
    module lpb = pullback-of-not lpb
    module upb = pullback-of-not upb
    ulpb : pullback-of lpb.π/₂ upb.π/₁
    ulpb = pb-of lpb.π/₂ upb.π/₁
    module ulpb = pullback-of-not ulpb
    outsq-pf : (a ∘ f) ∘ (lpb.π/₁ ∘ ulpb.π/₁) ~ (b ∘ g) ∘ (upb.π/₂ ∘ ulpb.π/₂)
    outsq-pf = assˢ ⊙ ∘e (ass ⊙ ∘e r lpb.×/sqpf) r ⊙ ass ⊙ ∘e r (ass ⊙ ∘e r inpb.×/sqpf ⊙ assˢ)
               ⊙ assˢ ⊙ ∘e (assˢ ⊙ ∘e ulpb.×/sqpf r ⊙ ass ⊙ ∘e r upb.×/sqpf ⊙ assˢ) r ⊙ ass
    outsq-pb : is-pb-square (mksq (mksq/ outsq-pf))
    outsq-pb = du.any-outer-is-pbsq r outsq-pf
             where module d-rl = right-and-left-so-outer inpb.×/ispbsq lpb
                   module u-rl = right-and-left-so-outer upb.×/ispbsq ulpb
                   module du = lower-and-upper-so-outer (d-rl.outer-is-pbsq r) (u-rl.outer-pbof r)
    module outpb = pullback-of-not (mkpb-of outsq-pb)
    diagl : || Hom ulpb.ul inpb.ul ||
    diagl = lpb.π/₂ ∘ ulpb.π/₁
    diagr : || Hom ulpb.ul inpb.ul ||
    diagr = upb.π/₁ ∘ ulpb.π/₂
    trl₁ : inpb.π/₁ ∘ diagl ~ f ∘ outpb.π/₁
    trl₁ = ass ⊙ ∘e r (lpb.×/sqpf ˢ) ⊙ assˢ
    trl₂ : inpb.π/₂ ∘ diagl ~ g ∘ outpb.π/₂
    trl₂ = ∘e ulpb.×/sqpf r ⊙ ass ⊙ ∘e r upb.×/sqpf ⊙ assˢ
    trr₁ : inpb.π/₁ ∘ diagr ~ f ∘ outpb.π/₁
    trr₁ = ∘e (ulpb.×/sqpf ˢ) r ⊙ ass ⊙ ∘e r (lpb.×/sqpf ˢ) ⊙ assˢ
    trr₂ : inpb.π/₂ ∘ diagr ~ g ∘ outpb.π/₂
    trr₂ = ass ⊙ ∘e r upb.×/sqpf ⊙ assˢ
  -- end pb-over-pbof


  module decompose-out&in-pbs (haspb : has-pullbacks ℂ)
                              {I A B : Obj}{a : || Hom A I ||}{b : || Hom B I ||}(inpb : pullback-of a b)
                              {A' B' : Obj}{a' : || Hom A' I ||}{b' : || Hom B' I ||}(outpb : pullback-of a' b')
                              {f : || Hom A' A ||}{g : || Hom B' B ||}(ftr : a ∘ f ~ a')(gtr : b ∘ g ~ b')
                              where
    open has-pullbacks haspb
    private
      module inpb = pullback-of-not inpb
      module outpb = pullback-of-not outpb
    lpb : pullback-of f inpb.π/₁
    lpb = pb-of f inpb.π/₁
    upb : pullback-of inpb.π/₂ g
    upb = pb-of inpb.π/₂ g
    module lpb = pullback-of-not lpb
    module upb = pullback-of-not upb
    diag-pf :  a ∘ f ∘ outpb.π/₁ ~ b ∘ g ∘ outpb.π/₂
    diag-pf = ass ⊙ ∘e r ftr ⊙ outpb.×/sqpf ⊙ ∘e r (gtr ˢ) ⊙ assˢ
    diag : || Hom outpb.ul inpb.ul ||
    diag = inpb.⟨ f ∘ outpb.π/₁ , g ∘ outpb.π/₂ ⟩[ diag-pf ]
    f' : || Hom outpb.ul upb.ul ||
    f' = upb.⟨ diag , outpb.π/₂ ⟩[ inpb.×/tr₂ diag-pf ]
    g' : || Hom outpb.ul lpb.ul ||
    g' = lpb.⟨ outpb.π/₁ , diag ⟩[ inpb.×/tr₁ diag-pf ˢ ]
    ul-trlpf : diag ~ lpb.π/₂ ∘ g'
    ul-trlpf = inpb.⟨⟩uq (ass ⊙ ∘e r (lpb.×/sqpf ˢ) ⊙ assˢ ⊙ ∘e (lpb.×/tr₁ (inpb.×/tr₁ diag-pf ˢ)) r)
                        (∘e (lpb.×/tr₂ (inpb.×/tr₁ diag-pf ˢ)) r ⊙ inpb.×/tr₂ diag-pf)
    ul-trrpf : diag ~ upb.π/₁ ∘ f'
    ul-trrpf = inpb.⟨⟩uq (∘e (upb.×/tr₁ (inpb.×/tr₂ diag-pf)) r ⊙ inpb.×/tr₁ diag-pf)
                        (ass ⊙ ∘e r upb.×/sqpf ⊙ assˢ ⊙ ∘e (upb.×/tr₂ (inpb.×/tr₂ diag-pf)) r)
    ul-sqpf : lpb.π/₂ ∘ g' ~ upb.π/₁ ∘ f'
    ul-sqpf = ul-trlpf ˢ ⊙ ul-trrpf
    ulispb : is-pb-square (mksq (mksq/ ul-sqpf))
    ulispb = left-is-pbsq r (upb.×/tr₂ (inpb.×/tr₂ diag-pf)) ul-sqpf
         where open right-and-left-so-outer inpb.×/ispbsq lpb
               lowerpb : pullback-of a' b
               lowerpb = outer-pbof ftr
               open lower-and-outer-so-upper lowerpb outpb
               upperpb : pullback-of (inpb.π/₂ ∘ lpb.π/₂) g
               upperpb = upper-pbof gtr (lpb.×/tr₁ (inpb.×/tr₁ diag-pf ˢ))
                                    (assˢ ⊙ ∘e (lpb.×/tr₂ (inpb.×/tr₁ diag-pf ˢ)) r ⊙ inpb.×/tr₂ diag-pf)
               open right-and-outer-so-left upb upperpb
    ulpb : pullback-of lpb.π/₂ upb.π/₁
    ulpb = mkpb-of ulispb
    module ulpb = pullback-of-not ulpb
  -- end decompose-out&in-pbs


{-
  module ×/ₐ-of-pbstb-Propos-is-Propos-aux {Propos : {X Y : Obj} → || Hom X Y || → Set₁}
                                       --(Propos-ext : is-hom-ext ℂ Propos)
                                       (Propos-pbstb : is-pbof-stable Propos)
                                       {I A' B' : Obj} {a' : || Hom A' I ||} {b' : || Hom B' I ||} (inpb : pullback-of a' b')
                                       {A B : Obj} {a : || Hom A I ||} {b : || Hom B I ||}(outpb : pullback-of a b)
                                       {f : || Hom A A' ||} {g : || Hom B B' ||} (f-tr : a' ∘ f ~ a) (g-tr : b' ∘ g ~ b)
                                       (ldpb : pullback-of a b') (fPropos : Propos f) (gPropos : Propos g)
                                       where
    private
      module inpb = pullback-of-not inpb
      module outpb = pullback-of-not outpb
      module a×/b' =  pullback-of-not ldpb
      snd-pf = outpb.×/sqpf ⊙ ∘e r (g-tr ˢ) ⊙ assˢ
      snd : || Hom outpb.ul a×/b'.ul ||
      snd = a×/b'.⟨ outpb.π/₁ , g ∘ outpb.π/₂ ⟩[ snd-pf ]
      fst-pf : a' ∘ f ∘ a×/b'.π/₁ ~ b' ∘ a×/b'.π/₂
      fst-pf = ass ⊙ ∘e r f-tr ⊙ a×/b'.×/sqpf
      fst : || Hom a×/b'.ul inpb.ul ||
      fst = inpb.⟨ f ∘ a×/b'.π/₁ , a×/b'.π/₂ ⟩[ fst-pf ]
    sndPropos : Propos snd
    sndPropos = pres-rl (mkpb-of snd-pbsq) gPropos
                 where open is-pbof-stable Propos-pbstb
                       snd-sq : a×/b'.π/₂ ∘ snd ~ g ∘ outpb.π/₂
                       snd-sq = a×/b'.×/tr₂ snd-pf
                       snd-pbsq : is-pb-square (mksq (mksq/ snd-sq))
                       snd-pbsq = upper-is-pbsq {g} {snd} g-tr (a×/b'.×/tr₁ snd-pf) snd-sq
                                 where open lower-and-outer-so-upper ldpb outpb
    fstPropos : Propos fst
    fstPropos = pres-du (mkpb-of fst-pbsq) fPropos
           where open is-pbof-stable Propos-pbstb
                 fst-sq : f ∘ a×/b'.π/₁ ~ inpb.π/₁ ∘ fst
                 fst-sq = inpb.×/tr₁ fst-pf ˢ
                 fst-pbsq : is-pb-square (mksq (mksq/ fst-sq))
                 fst-pbsq = left-is-pbsq {f} {fst} f-tr (inpb.×/tr₂ fst-pf) fst-sq
                        where open right-and-outer-so-left inpb ldpb
  -- end ×/ₐ-of-pbstb-Propos-is-Propos-aux


  module ×/ₐ-of-pbstb-Propos-is-Propos-aux2 {Propos : {X Y : Obj} → || Hom X Y || → Set₁} (Propos-congr : is-ecat-congr ℂ Propos)
                                        {I A' B' : Obj} {a' : || Hom A' I ||} {b' : || Hom B' I ||} (inpb : pullback-of a' b')
                                        {A B : Obj} {a : || Hom A I ||} {b : || Hom B I ||}(outpb : pullback-of a b)
                                        {f : || Hom A A' ||} {g : || Hom B B' ||} (f-tr : a' ∘ f ~ a) (g-tr : b' ∘ g ~ b)
                                        (ldpb : pullback-of a b') (fPropos : Propos f) (gPropos : Propos g)
                                        where
    private
      module inpb = pullback-of-not inpb
      module outpb = pullback-of-not outpb
      module a×/b' =  pullback-of-not ldpb
      snd-pf = outpb.×/sqpf ⊙ ∘e r (g-tr ˢ) ⊙ assˢ
      snd : || Hom outpb.ul a×/b'.ul ||
      snd = a×/b'.⟨ outpb.π/₁ , g ∘ outpb.π/₂ ⟩[ snd-pf ]
      fst-pf : a' ∘ f ∘ a×/b'.π/₁ ~ b' ∘ a×/b'.π/₂
      fst-pf = ass ⊙ ∘e r f-tr ⊙ a×/b'.×/sqpf
      fst : || Hom a×/b'.ul inpb.ul ||
      fst = inpb.⟨ f ∘ a×/b'.π/₁ , a×/b'.π/₂ ⟩[ fst-pf ]
      ×/arcan : || Hom outpb.ul inpb.ul ||
      ×/arcan = f ×/ₐ g [ f-tr , g-tr ]
              where open ×/ₐdef inpb outpb
    ×/ar-tr : {h : || Hom outpb.ul inpb.ul ||}
                 → inpb.π/₁ ∘ h ~ f ∘ outpb.π/₁ → inpb.π/₂ ∘ h ~ g ∘ outpb.π/₂
                   → fst ∘ snd ~ h
    ×/ar-tr {h} pf1 pf2 = inpb.×/uq
      (~proof inpb.π/₁ ∘ fst ∘ snd   ~[ ass ⊙ ∘e r (inpb.×/tr₁ fst-pf) ⊙ assˢ ] /
              f ∘ a×/b'.π/₁ ∘ snd      ~[ ∘e (a×/b'.×/tr₁ snd-pf) r ] /
              f ∘ outpb.π/₁              ~[ pf1 ˢ ]∎
              inpb.π/₁ ∘ h ∎)
      (~proof inpb.π/₂ ∘ fst ∘ snd   ~[ ass ⊙ ∘e r (inpb.×/tr₂ fst-pf) ] /
              a×/b'.π/₂ ∘ snd          ~[ a×/b'.×/tr₂ snd-pf ] /
              g ∘ outpb.π/₂              ~[ pf2 ˢ ]∎
              inpb.π/₂ ∘ h ∎)                      
    ×/arPropos-cond : {h : || Hom outpb.ul inpb.ul ||}
                   → inpb.π/₁ ∘ h ~ f ∘ outpb.π/₁ → inpb.π/₂ ∘ h ~ g ∘ outpb.π/₂
                     → Propos fst → Propos snd → Propos h
    ×/arPropos-cond pf1 pf2 fstPropos sndPropos = ∘ce (×/ar-tr pf1 pf2) fstPropos sndPropos
                                          where open is-ecat-congr Propos-congr
    ×/arcanPropos-cond : Propos fst → Propos snd → Propos ×/arcan
    ×/arcanPropos-cond = ×/arPropos-cond {×/arcan} (inpb.×/tr₁ (×/ₐcanpf f-tr g-tr)) (inpb.×/tr₂ (×/ₐcanpf f-tr g-tr))
                     where open ×/ₐdef inpb outpb
  -- end ×/ₐ-of-pbstb-Propos-is-Propos-aux2


  module ×/ₐ-of-pbstb-Propos-is-Propos {Propos : {X Y : Obj} → || Hom X Y || → Set₁}
                                   (Propos-congr : is-ecat-congr ℂ Propos) (Propos-pbstb : is-pbof-stable Propos)
                                   {I A' B' : Obj} {a' : || Hom A' I ||} {b' : || Hom B' I ||} (inpb : pullback-of a' b')
                                   {A B : Obj} {a : || Hom A I ||} {b : || Hom B I ||}(outpb : pullback-of a b)
                                   {f : || Hom A A' ||} {g : || Hom B B' ||} (f-tr : a' ∘ f ~ a) (g-tr : b' ∘ g ~ b)
                                   (ldpb : pullback-of a b') (fPropos : Propos f) (gPropos : Propos g)
                                   where
    private
      module inpb = pullback-of-not inpb
      module outpb = pullback-of-not outpb
      module a×/b' =  pullback-of-not ldpb
    --open is-ecat-congr Propos-congr
    open ×/ₐ-of-pbstb-Propos-is-Propos-aux Propos-pbstb inpb outpb f-tr g-tr ldpb fPropos gPropos
    open ×/ₐ-of-pbstb-Propos-is-Propos-aux2 Propos-congr inpb outpb f-tr g-tr ldpb fPropos gPropos
    ×/arPropos : {h : || Hom outpb.ul inpb.ul ||}
                   → inpb.π/₁ ∘ h ~ f ∘ outpb.π/₁ → inpb.π/₂ ∘ h ~ g ∘ outpb.π/₂ → Propos h
    ×/arPropos pf1 pf2 = ×/arPropos-cond pf1 pf2 fstPropos sndPropos
    ×/arcan : || Hom outpb.ul inpb.ul ||
    ×/arcan = f ×/ₐ g [ f-tr , g-tr ]
            where open ×/ₐdef inpb outpb
    ×/arcanPropos : Propos ×/arcan
    ×/arcanPropos = ×/arPropos {×/arcan} (inpb.×/tr₁ (×/ₐcanpf f-tr g-tr)) (inpb.×/tr₂ (×/ₐcanpf f-tr g-tr))
                where open ×/ₐdef inpb outpb
  -- end ×/ₐ-of-pbstb-Propos-is-Propos
-}


-- end pullback-props
