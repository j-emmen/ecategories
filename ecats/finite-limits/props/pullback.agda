 
-- disable the K axiom:

{-# OPTIONS --without-K #-}

-- Agda version 2.5.4.1

module ecats.finite-limits.props.pullback where

open import ecats.basic-defs.ecat-def&not
open import ecats.basic-defs.commut-shapes
open import ecats.basic-defs.isomorphism
open import ecats.basic-defs.epi&mono
open import ecats.finite-limits.d&n-pullback
open import ecats.finite-limits.d&n-bin-product




-- Some properties of pullback squares

module pullback-props (ℂ : ecategory) where
  open ecategory-aux ℂ
  open iso-defs ℂ
  open iso-transports ℂ 
  open epis&monos-defs ℂ
  open comm-shapes ℂ
  open pullback-squares ℂ
  open binary-products ℂ
  private
    module sq/ₙ = square/cosp
    module sqₙ = comm-square
    module pbofₙ = pullback-of
    module pbsqₙ = pb-square


  -- pullback extensionality

  ×/sqpf-irr : {I A B P : Obj} {a : || Hom A I ||}{b : || Hom B I ||} {p₁ : || Hom P A ||} {p₂ : || Hom P B ||}
               (pf pf' : a ∘ p₁ ~ b ∘ p₂)
                 → is-pb-square (mksq (mksq/ pf)) → is-pb-square (mksq (mksq/ pf'))
  ×/sqpf-irr {a = a} {b} {p₁} {p₂} pf pf' ispb = record
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
  
  pbs-iso-ar : {A B I : Obj} {a : || Hom A I ||} {b : || Hom B I ||} (pb1 pb2 : pullback-of a b)
                  → || Hom (pbofₙ.ul pb1) (pbofₙ.ul pb2) ||
  pbs-iso-ar pb1 pb2 = pb2.⟨ pb1.π/₁ , pb1.π/₂ ⟩[ pb1.×/sqpf ]
                     where module pb1 = pullback-of pb1
                           module pb2 = pullback-of pb2
                           

  pbs-iso-inv : {A B I : Obj} {a : || Hom A I ||} {b : || Hom B I ||} (pb1 pb2 : pullback-of a b)
                   → || Hom (pbofₙ.ul pb2) (pbofₙ.ul pb1) ||
  pbs-iso-inv pb1 pb2 = pb1.⟨ pb2.π/₁ , pb2.π/₂ ⟩[ pb2.×/sqpf ]
                      where module pb1 = pullback-of pb1
                            module pb2 = pullback-of pb2


  pbs-iso : {A B I : Obj} {a : || Hom A I ||} {b : || Hom B I ||} (pb1 pb2 : pullback-of a b)
               → is-iso (pbs-iso-ar pb1 pb2)
  pbs-iso pb1 pb2 = record
    { invf = pbs-iso-inv pb1 pb2
    ; isisopair = record
            { iddom = pb1.×/uq (ass ⊙  ∘e r (pb1.×/tr₁ pb2.×/sqpf) ⊙ ridggˢ (pb2.×/tr₁ pb1.×/sqpf) r)
                               (ass ⊙  ∘e r (pb1.×/tr₂ pb2.×/sqpf) ⊙ ridggˢ (pb2.×/tr₂ pb1.×/sqpf) r)
            ; idcod = pb2.×/uq (ass ⊙  ∘e r (pb2.×/tr₁ pb1.×/sqpf) ⊙ ridggˢ (pb1.×/tr₁ pb2.×/sqpf) r)
                               (ass ⊙  ∘e r (pb2.×/tr₂ pb1.×/sqpf) ⊙ ridggˢ (pb1.×/tr₂ pb2.×/sqpf) r)
            }
    }
    where module pb1 = pullback-of pb1
          module pb2 = pullback-of pb2



  -- cospan isomorphic to a pb is pb

  cosp≅pb-is-pb : {A B I : Obj} {a : || Hom A I ||} {b : || Hom B I ||} (pb : pullback-of a b) {sq : square/cosp a b}
                  --(pbsq1 : is-pb-square (mksq span1))
                  {f : || Hom (sq/ₙ.ul sq) (pbofₙ.ul pb) ||}
                    → is-iso f → pbofₙ.π/₁ pb ∘ f ~ sq/ₙ.left sq → pbofₙ.π/₂ pb ∘ f ~ sq/ₙ.up sq
                      → is-pb-square (mksq sq)
  cosp≅pb-is-pb pb {sq} {f} isof tr1 tr2 = record
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

  module lower-and-outer-so-upper {DL DR UR UUR : Obj} {down : || Hom DL DR ||} {right : || Hom UR DR ||} {right' : || Hom UUR DR ||}
                                  (low-pb : pullback-of down right) (out-pb : pullback-of down right')
                                  where
    private
      module lowpb = pullback-of low-pb
      module outpb = pullback-of out-pb

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
    
  -- end lower-and-outer-so-upper


  module right-and-outer-so-left {DR UR DLL DL : Obj} {right : || Hom UR DR ||} {down : || Hom DL DR ||} {down' : || Hom DLL DR ||}
                                 (rpb : pullback-of down right) (outpb : pullback-of down' right) where
    private
      module rpb = pullback-of rpb
      module outpb = pullback-of outpb

    l-sq-is-pb : {d-fill : || Hom DLL DL ||} {u-fill : || Hom outpb.ul rpb.ul ||}
                 (d-tr : down ∘ d-fill ~ down') (u-tr : rpb.π/₂ ∘ u-fill ~ outpb.π/₂)
                 (l-sq-comm : d-fill ∘ outpb.π/₁ ~ rpb.π/₁ ∘ u-fill)
                   → is-pb-square (mksq (mksq/ l-sq-comm))
    l-sq-is-pb {d-fill} {u-fill} d-tr u-tr l-sq-comm = diag-sym-pb-sq-inv (upper-is-pbsq d-tr u-tr (l-sq-comm ˢ))
                                                     where open lower-and-outer-so-upper (diag-sym-pbof rpb) (diag-sym-pbof outpb)

  --end right-and-outer-so-left

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


  -- given a mono between bottomo-right corners
  -- if outer square commutes/is pb then so is inner one

  monic-sub-sq : (sq : comm-square) {dr' : Obj} {down' : || Hom (sqₙ.dl sq) dr' ||} {right' : || Hom (sqₙ.ur sq) dr' ||} {m : || Hom dr' (sqₙ.dr sq) ||}
                     → m ∘ down' ~ sqₙ.down sq → m ∘ right' ~ sqₙ.right sq → is-monic m → comm-square
  monic-sub-sq sq trd trr pfm = mksq (mksq/ (mono-pf (ass ⊙ ∘e r trd ⊙ sqₙ.sq-pf sq ⊙ ∘e r (trr ˢ) ⊙ assˢ)))
                              where open is-monic pfm

  monic-sub-pb-sq : (pbsq : pb-square) {dr' : Obj} {down' : || Hom (pbsqₙ.dl pbsq) dr' ||} {right' : || Hom (pbsqₙ.ur pbsq) dr' ||}
                    {m : || Hom dr' (pbsqₙ.dr pbsq) ||} (trd : m ∘ down' ~ pbsqₙ.down pbsq) (trr : m ∘ right' ~ pbsqₙ.right pbsq)
                    (pfm : is-monic m) → is-pb-square (monic-sub-sq (pbsqₙ.×/sq pbsq) trd trr pfm)
  monic-sub-pb-sq pbsq trd trr pfm = record
            { ⟨_,_⟩[_] = λ h k pf → pbsq.⟨ h , k ⟩[ mcmp pf ] 
            ; ×/tr₁ = λ pf → pbsq.×/tr₁ (mcmp pf)
            ; ×/tr₂ = λ pf → pbsq.×/tr₂ (mcmp pf)
            ; ×/uq = pbsq.×/uq 
            }
            where module pbsq = pullback-sq-not pbsq
                  open is-monic pfm
                  ssq = monic-sub-sq (pb-square.×/sq pbsq) trd trr pfm
                  mcmp : {A : Obj} {h : || Hom A (sqₙ.dl ssq) ||} {k : || Hom A (sqₙ.ur ssq) ||}
                            → sqₙ.down ssq ∘ h ~ sqₙ.right ssq ∘ k → pbsq.down ∘ h ~ pbsq.right ∘ k
                  mcmp pfs = ∘e r (trd ˢ) ⊙ assˢ ⊙ ∘e pfs r ⊙ ass ⊙ ∘e r trr




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
  triv-pbsqˢ a = ×/sqpf-irr (trsqˢ.sq-pf) (ridgen lidˢ) (diag-sym-pb-sq trpb.×/ispbsq)
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
          inv-sq = invIsNat u.isisopair d.isisopair sq-pf


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

  record is-pbsq-stable (Prop : {X Y : Obj} → || Hom X Y || → Set₁) : Set₁ where
    open pb-square
    field
      pres-rl : (pbsq : pb-square) → Prop (pbsqₙ.right pbsq) → Prop (pbsqₙ.π/₁ pbsq)
    pres-du : (pbsq : pb-square) → Prop (pbsqₙ.down pbsq) → Prop (pbsqₙ.π/₂ pbsq)
    pres-du pbsq pf = pres-rl (mkpb-sq (diag-sym-pb-sq (pbsqₙ.×/ispbsq pbsq))) pf

  record is-pbof-stable (Prop : {X Y : Obj} → || Hom X Y || → Set₁) : Set₁ where
    open pullback-of
    field
      pres-rl : {A B : Obj} {c : || Hom A B ||} {C : Obj} {f : || Hom C B ||} (pbof : pullback-of f c)
                   → Prop c → Prop (π/₁ pbof)
    pres-du : {A B : Obj} {c : || Hom A B ||} {C : Obj} {f : || Hom C B ||} (pbof : pullback-of c f)
                   → Prop c → Prop (π/₂ pbof)
    pres-du pbof = pres-rl (diag-sym-pbof pbof)

  pbsq-stb→pbof-stb : {Prop : {X Y : Obj} → || Hom X Y || → Set₁}
                           → is-pbsq-stable Prop → is-pbof-stable Prop
  pbsq-stb→pbof-stb {Prop} pbsqstb = record
    { pres-rl = λ pbof isProp → pres-rl (×/pbsq pbof) isProp
    }
    where open is-pbsq-stable pbsqstb
          open pullback-of-not 

  pbof-stb→pbsq-stb : {Prop : {X Y : Obj} → || Hom X Y || → Set₁}
                           → is-pbof-stable Prop → is-pbsq-stable Prop
  pbof-stb→pbsq-stb {Prop} pbofstb = record
    { pres-rl = λ pbsq isProp → pres-rl (×/of pbsq) isProp
    }
    where open is-pbof-stable pbofstb
          open pullback-sq-not


  module ×/ₐ-of-pbstb-Prop-is-Prop-aux {Prop : {X Y : Obj} → || Hom X Y || → Set₁}
                                       (Prop-ext : is-hom-ext ℂ Prop) (Prop-pbstb : is-pbof-stable Prop)
                                       {I A' B' : Obj} {a' : || Hom A' I ||} {b' : || Hom B' I ||} (inpb : pullback-of a' b')
                                       {A B : Obj} {a : || Hom A I ||} {b : || Hom B I ||}(outpb : pullback-of a b)
                                       {f : || Hom A A' ||} {g : || Hom B B' ||} (f-tr : a' ∘ f ~ a) (g-tr : b' ∘ g ~ b)
                                       (ldpb : pullback-of a b') (fProp : Prop f) (gProp : Prop g)
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
    sndProp : Prop snd
    sndProp = pres-rl (mkpb-of snd-pbsq) gProp
                 where open is-pbof-stable Prop-pbstb
                       snd-sq : a×/b'.π/₂ ∘ snd ~ g ∘ outpb.π/₂
                       snd-sq = a×/b'.×/tr₂ snd-pf
                       snd-pbsq : is-pb-square (mksq (mksq/ snd-sq))
                       snd-pbsq = upper-is-pbsq {g} {snd} g-tr (a×/b'.×/tr₁ snd-pf) snd-sq
                                 where open lower-and-outer-so-upper ldpb outpb
    fstProp : Prop fst
    fstProp = pres-du (mkpb-of fst-pbsq) fProp
           where open is-pbof-stable Prop-pbstb
                 fst-sq : f ∘ a×/b'.π/₁ ~ inpb.π/₁ ∘ fst
                 fst-sq = inpb.×/tr₁ fst-pf ˢ
                 fst-pbsq : is-pb-square (mksq (mksq/ fst-sq))
                 fst-pbsq = l-sq-is-pb {f} {fst} f-tr (inpb.×/tr₂ fst-pf) fst-sq
                        where open right-and-outer-so-left inpb ldpb
  -- end ×/ₐ-of-pbstb-Prop-is-Prop-aux


  module ×/ₐ-of-pbstb-Prop-is-Prop-aux2 {Prop : {X Y : Obj} → || Hom X Y || → Set₁} (Prop-congr : is-ecat-congr ℂ Prop)
                                        {I A' B' : Obj} {a' : || Hom A' I ||} {b' : || Hom B' I ||} (inpb : pullback-of a' b')
                                        {A B : Obj} {a : || Hom A I ||} {b : || Hom B I ||}(outpb : pullback-of a b)
                                        {f : || Hom A A' ||} {g : || Hom B B' ||} (f-tr : a' ∘ f ~ a) (g-tr : b' ∘ g ~ b)
                                        (ldpb : pullback-of a b') (fProp : Prop f) (gProp : Prop g)
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
    open is-ecat-congr Prop-congr
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
    ×/arProp-cond : {h : || Hom outpb.ul inpb.ul ||}
                   → inpb.π/₁ ∘ h ~ f ∘ outpb.π/₁ → inpb.π/₂ ∘ h ~ g ∘ outpb.π/₂
                     → Prop fst → Prop snd → Prop h
    ×/arProp-cond pf1 pf2 fstProp sndProp = ∘ce (×/ar-tr pf1 pf2) fstProp sndProp
    ×/arcanProp-cond : Prop fst → Prop snd → Prop ×/arcan
    ×/arcanProp-cond = ×/arProp-cond {×/arcan} (inpb.×/tr₁ (×/ₐcanpf f-tr g-tr)) (inpb.×/tr₂ (×/ₐcanpf f-tr g-tr))
                     where open ×/ₐdef inpb outpb
  -- end ×/ₐ-of-pbstb-Prop-is-Prop-aux2


  module ×/ₐ-of-pbstb-Prop-is-Prop {Prop : {X Y : Obj} → || Hom X Y || → Set₁}
                                   (Prop-congr : is-ecat-congr ℂ Prop) (Prop-pbstb : is-pbof-stable Prop)
                                   {I A' B' : Obj} {a' : || Hom A' I ||} {b' : || Hom B' I ||} (inpb : pullback-of a' b')
                                   {A B : Obj} {a : || Hom A I ||} {b : || Hom B I ||}(outpb : pullback-of a b)
                                   {f : || Hom A A' ||} {g : || Hom B B' ||} (f-tr : a' ∘ f ~ a) (g-tr : b' ∘ g ~ b)
                                   (ldpb : pullback-of a b') (fProp : Prop f) (gProp : Prop g)
                                   where
    private
      module inpb = pullback-of-not inpb
      module outpb = pullback-of-not outpb
      module a×/b' =  pullback-of-not ldpb
    open is-ecat-congr Prop-congr
    open ×/ₐ-of-pbstb-Prop-is-Prop-aux ext Prop-pbstb inpb outpb f-tr g-tr ldpb fProp gProp
    open ×/ₐ-of-pbstb-Prop-is-Prop-aux2 Prop-congr inpb outpb f-tr g-tr ldpb fProp gProp
    ×/arProp : {h : || Hom outpb.ul inpb.ul ||}
                   → inpb.π/₁ ∘ h ~ f ∘ outpb.π/₁ → inpb.π/₂ ∘ h ~ g ∘ outpb.π/₂ → Prop h
    ×/arProp pf1 pf2 = ×/arProp-cond pf1 pf2 fstProp sndProp
    ×/arcan : || Hom outpb.ul inpb.ul ||
    ×/arcan = f ×/ₐ g [ f-tr , g-tr ]
            where open ×/ₐdef inpb outpb
    ×/arcanProp : Prop ×/arcan
    ×/arcanProp = ×/arProp {×/arcan} (inpb.×/tr₁ (×/ₐcanpf f-tr g-tr)) (inpb.×/tr₂ (×/ₐcanpf f-tr g-tr))
                where open ×/ₐdef inpb outpb
  -- end ×/ₐ-of-pbstb-Prop-is-Prop



-- end pullback-props
