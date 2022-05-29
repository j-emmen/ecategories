
{-# OPTIONS --without-K #-}

module ecats.functors.props.projective-cover where

open import ecats.basic-defs.ecat-def&not
open import ecats.basic-defs.all-arrows
open import ecats.basic-defs.eqv-rel
open import ecats.basic-defs.regular-ecat
open import ecats.basic-defs.exact-ecat
open import ecats.basic-props.exact-ecat
open import ecats.basic-props.all
open import ecats.finite-limits.all
open import ecats.functors.defs.efunctor-d&n
open import ecats.functors.defs.natural-transformation
open import ecats.functors.defs.basic-defs
open import ecats.functors.defs.preserving-functor
open import ecats.functors.defs.projective-cover
open import ecats.functors.defs.left-covering
open import ecats.functors.props.left-covering
open import ecats.functors.props.basic-props
open import ecats.functors.props.preserving-functor


-- Properties of projective covers into finitely complete categories



module projective-cover-props {ℂ : ecategory}{ℙ : ecategory}
                              {PC : efunctor ℙ ℂ}(ispjcov : is-projective-cover PC)
                              where
  private
    module ℙ = ecategory ℙ
    module ℂ where
      open ecategory ℂ public
      open iso-defs ℂ public
      open epis&monos-defs ℂ public
      open epis&monos-props ℂ public
    module PC where
      open efunctor-aux PC public
      open is-projective-cover ispjcov public


-- Projective covers are invariant under natural iso

  iso-pjc : {F : efunctor ℙ ℂ} → PC ≅ₐ F → is-projective-cover F
  iso-pjc {F} α = record
    { isfull = full-ext PC.isfull α
    ; isfaith = faith-ext PC.isfaith α
    ; img-proj = λ X → record
               { lift = λ repi g → PC.rprj.lift X repi (g ℂ.∘ α.fnc)  ℂ.∘ α.fnc⁻¹
               ; lift-tr = lifttr X
               }
    ; reg-cov-obj = PC.rcov-of.Ob
    ; is-reg-cov = λ A → record
                 { ar = PC.rcov-of.ar A ℂ.∘ α.fnc⁻¹
                 ; is-repi = isrepi A
                 }
    }
    where module F = efunctor-props F
          module α = natural-iso α
          lifttr : (X : ℙ.Obj){A B : ℂ.Obj}{f : || ℂ.Hom A B ||}
                   {repi : ℂ.is-regular-epi f}{g : || ℂ.Hom (F.ₒ X) B ||}
                     → f ℂ.∘ PC.rprj.lift X repi (g ℂ.∘ α.fnc) ℂ.∘ α.fnc⁻¹ ℂ.~ g
          lifttr X {f = f} {repi} {g} = ~proof
            f ℂ.∘ PC.rprj.lift X repi (g ℂ.∘ α.fnc) ℂ.∘ α.fnc⁻¹  ~[ ass ⊙ ∘e r (PC.rprj.lift-tr X) ] /
            (g ℂ.∘ α.fnc) ℂ.∘ α.fnc⁻¹                            ~[ assˢ ⊙ ridgg r α.idcod ]∎
            g ∎
                                      where open ecategory-aux-only ℂ
          isrepi : (A : ℂ.Obj) → ℂ.is-regular-epi (PC.rcov-of.ar A ℂ.∘ α.fnc⁻¹)
          isrepi A = ℂ.iso-to-repi-is-repi-dom (ℂ.mkis-iso α.isiso)
                                               (assˢ ⊙ ridgg r α.iddom)
                                               (PC.rcov-of.is-repi A)
                   where open ecategory-aux-only ℂ



-- Projective covers are invariant under equivalence

  module adj-eqv-preserves-proj-ob {𝔻 : ecategory}{F : efunctor ℂ 𝔻}
                                   (isaeqv : is-adj-equivalence F)
                                   (X : ℙ.Obj)
                                   where
    private
      module 𝔻 where
        open ecategory 𝔻 public
        open epis&monos-defs 𝔻 public
      module F where
        open efunctor-props F public
        open is-adj-equivalence isaeqv public
        module inv where
          open efunctor-aux inv public
          open equivalence-props inv F public
          open preserves-regular-epis (pres-repi (inv-is-adjeqv isadjeqvp)) public
      module F○PC = efunctor-aux (F ○ PC)

    lift : {A B : 𝔻.Obj}{f : || 𝔻.Hom A B ||}
           (repi : 𝔻.is-regular-epi f)(g : || 𝔻.Hom (F○PC.ₒ X) B ||)
             → || 𝔻.Hom (F○PC.ₒ X) A ||
    lift {f = f}  repi g = F.ι1.fnc 𝔻.∘ F.ₐ (PC.rprj.lift X {_} {_} {F.inv.ₐ f}
                                                          (F.inv.pres-repi-pf repi)
                                                          (F.inv.ₐ g ℂ.∘ F.ι2.fnc⁻¹))
    tr : {A B : 𝔻.Obj} {f : || 𝔻.Hom A B ||}
         {repi : 𝔻.is-regular-epi f} {g : || 𝔻.Hom (F○PC.ₒ X) B ||}
           → f 𝔻.∘ lift repi g 𝔻.~ g
    tr {f = f} {repi} {g} = ~proof
      f 𝔻.∘ lift repi g                                   ~[ ass ⊙ ∘e r (F.ι1.natt.nat f ˢ) ⊙ assˢ ] /
      F.ι1.fnc 𝔻.∘ F.ₐ (F.inv.ₐ f) 𝔻.∘ F.ₐ (PC.rprj.lift X {_} {_} {F.inv.ₐ f}
                                                         (F.inv.pres-repi-pf repi)
                                                         (F.inv.ₐ g ℂ.∘ F.ι2.fnc⁻¹))
                                                           ~[ ∘e (F.∘∘ (PC.rprj.lift-tr X)) r ] /
      F.ι1.fnc 𝔻.∘ F.ₐ (F.inv.ₐ g) 𝔻.∘ F.ₐ F.ι2.fnc⁻¹      ~[ ass ⊙ ∘e r (F.ι1.natt.nat g) ⊙ assˢ ] /
      g 𝔻.∘ F.ι1.fnc 𝔻.∘ F.ₐ F.ι2.fnc⁻¹                   ~[ ridgg r F.trid₁ ]∎
      g ∎
                          where open ecategory-aux-only 𝔻
  -- end adj-eqv-preserves-proj-ob


  module adj-eqv-preserves-exist-cover {𝔻 : ecategory}{F : efunctor ℂ 𝔻}
                                       (isaeqv : is-adj-equivalence F)
                                       where
    private
      module 𝔻 where
        open ecategory 𝔻 public
        open iso-defs 𝔻 public
        open epis&monos-defs 𝔻 public
        open epis&monos-props 𝔻 public
      module F where
        open efunctor-props F public
        open is-adj-equivalence isaeqv public
        module props where
          open equivalence-props F inv public
          open preserves-regular-epis (pres-repi isadjeqvp) public
        module inv where
          open efunctor-aux inv public
          open equivalence-props inv F public
          open preserves-regular-epis (pres-repi (inv-is-adjeqv isadjeqvp)) public
      module F○PC = efunctor-aux (F ○ PC)

    cov-ob : 𝔻.Obj → ℙ.Obj
    cov-ob B = PC.rcov-of.Ob (F.inv.ₒ B)

    isreg :  (B : 𝔻.Obj) → F○PC.ₒ (cov-ob B) 𝔻.covers B
    isreg B = record
      { ar = F.ι1.fnc 𝔻.∘ F.ₐ (PC.rcov-of.ar (F.inv.ₒ B))
      ; is-repi = 𝔻.iso-to-repi-is-repi-cod (𝔻.mkis-iso F.ι1.isiso)
                                             r
                                             (F.props.pres-repi-pf (PC.rcov-of.is-repi (F.inv.ₒ B)))
      }
      where open ecategory-aux-only 𝔻
  -- end adj-eqv-preserves-exist-cover



  eqv-pjc : {𝔻 : ecategory}{F : efunctor ℂ 𝔻}
              → is-adj-equivalence F → is-projective-cover (F ○ PC)
  eqv-pjc {𝔻} {F} isaeqv = record
    { isfull = full-cmp PC.isfull (F.eqv-is-full isaeqv)
    ; isfaith = faith-cmp PC.isfaith (F.eqv-is-faith (adjeqv2eqv isaeqv))
    ; img-proj = λ X → record
               { lift = lift X
               ; lift-tr = λ {_} {_} {_} {repi} {g} → tr X {repi = repi} {g}
               }
    ; reg-cov-obj = cov-ob
    ; is-reg-cov = isreg
    }
    where open adj-eqv-preserves-proj-ob isaeqv
          open adj-eqv-preserves-exist-cover isaeqv
          module F = efunctor-props F

-- end projective-cover-props



-- The domain of a projective cover of a category with finite limits has finite weak limits

module prj-cover-of-lex-is-wlex {ℂ : ecategory} (hasfl : has-fin-limits ℂ)
                                {ℙ : ecategory} {PC : efunctor ℙ ℂ} (ispjcov : is-projective-cover PC)
                                where
  private
    module ℙ where
      open ecategory ℙ public
      open comm-shapes ℙ public
      open epis&monos-defs ℙ public
      open epis&monos-props ℙ public
      open kernel-pairs-defs ℙ public
      open finite-limits-d&p ℙ public
      open finite-weak-limits-d&p ℙ public
      open limits→weak-limits ℙ public
      --open relations-among-limit-diagrams ℙ public
    module ℂ where
      open ecategory ℂ public
      open comm-shapes ℂ public
      open iso-defs ℂ public
      open epis&monos-defs ℂ public
      open epis&monos-props ℂ public
      open kernel-pairs-defs ℂ public
      open eq-rel-defs ℂ public
      open finite-limits-d&p ℂ public
      open projective-defs ℂ public
    module flℂ where
      open has-fin-limits hasfl public
      open has-terminal hastrm public
      open has-bin-products hasprd using (prd-of) public
      open has-equalisers haseql using (eql-of) public
      open has-pullbacks haspb using (pb-of) public
      open has-bows hasbw using (bw-of) public
    module PC where
      open efunctor-aux PC public
      open is-projective-cover ispjcov public
      --open full public
      --open faith public


  -- Covers of limits in ℂ are weak limits in ℙ

  module cover-of-terminal-is-weak-terminal {T : ℂ.Obj} (istrm : ℂ.is-terminal T) where
    private
      module T where
        open ℂ.is-terminal istrm public
        module rcov = PC.rcov-of T
    wT : ℙ.Obj
    wT = T.rcov.Ob
    iswtrm : ℙ.is-wterminal wT
    iswtrm = record
             { w! = λ X → PC.full.ar (PC.rprj.lift X T.rcov.is-repi (T.! (PC.ₒ X)))
             }
  -- end cover-of-terminal-is-weak-terminal


  dom-has-weak-terminal : has-weak-terminal ℙ
  dom-has-weak-terminal = record
    { wtrmOb = wT
    ; iswtrm = iswtrm
    }
    where open cover-of-terminal-is-weak-terminal flℂ.istrm



  module cover-of-product-is-weak-product {X Y : ℙ.Obj} (prd : ℂ.product-of (PC.ₒ X) (PC.ₒ Y)) where
    private
      module PCX×PCY = ℂ.product-of-not prd
      module ×rc = PC.rcov-of PCX×PCY.O12
      w×Ob : ℙ.Obj
      w×Ob = PC.rcov-of.Ob PCX×PCY.O12
      wπ₁ : || ℙ.Hom w×Ob X ||
      wπ₁ = PC.full.ar (PCX×PCY.π₁ ℂ.∘ ×rc.ar)
      wπ₂ : || ℙ.Hom w×Ob Y ||
      wπ₂ = PC.full.ar (PCX×PCY.π₂ ℂ.∘ ×rc.ar)
      wun-aux : {Z : ℙ.Obj} (h : || ℙ.Hom Z X ||) (k : || ℙ.Hom Z Y ||) → || ℂ.Hom (PC.ₒ Z) (PC.ₒ w×Ob) ||
      wun-aux {Z} h k = PC.rprj.lift Z ×rc.is-repi PCX×PCY.< PC.ₐ h , PC.ₐ k >
      wun-aux-tr : {Z : ℙ.Obj} (h : || ℙ.Hom Z X ||) (k : || ℙ.Hom Z Y ||)
                      → ×rc.ar ℂ.∘ wun-aux h k ℂ.~ PCX×PCY.< PC.ₐ h , PC.ₐ k >
      wun-aux-tr {Z} h k = PC.rprj.lift-tr Z {repi = ×rc.is-repi} {PCX×PCY.< PC.ₐ h , PC.ₐ k >}
      wun : {Z : ℙ.Obj} (h : || ℙ.Hom Z X ||) (k : || ℙ.Hom Z Y ||) → || ℙ.Hom Z w×Ob ||
      wun h k = PC.full.ar (wun-aux h k)
      tr₁PC : {Z : ℙ.Obj} (h : || ℙ.Hom Z X ||) (k : || ℙ.Hom Z Y ||)
                 → PC.ₐ wπ₁ ℂ.∘ PC.ₐ (wun h k) ℂ.~ PC.ₐ h
      tr₁PC {Z} h k = ~proof
        PC.ₐ wπ₁ ℂ.∘ PC.ₐ (wun h k)                           ~[ ∘e PC.full.pf PC.full.pf ⊙ assˢ ] /
        PCX×PCY.π₁ ℂ.∘ ×rc.ar ℂ.∘ wun-aux h k                 ~[ ∘e (wun-aux-tr h k) r ] /
        PCX×PCY.π₁ ℂ.∘ PCX×PCY.< PC.ₐ h , PC.ₐ k >            ~[ PCX×PCY.×tr₁ ]∎
        PC.ₐ h ∎
                where open ecategory-aux-only ℂ
      tr₂PC : {Z : ℙ.Obj} (h : || ℙ.Hom Z X ||) (k : || ℙ.Hom Z Y ||)
                 → PC.ₐ wπ₂ ℂ.∘ PC.ₐ (wun h k) ℂ.~ PC.ₐ k
      tr₂PC {Z} h k = ~proof
        PC.ₐ wπ₂ ℂ.∘ PC.ₐ (wun h k)                           ~[ ∘e PC.full.pf PC.full.pf ⊙ assˢ ] /
        PCX×PCY.π₂ ℂ.∘ ×rc.ar ℂ.∘ wun-aux h k                 ~[ ∘e (wun-aux-tr h k) r ] /
        PCX×PCY.π₂ ℂ.∘ PCX×PCY.< PC.ₐ h , PC.ₐ k >            ~[ PCX×PCY.×tr₂ ]∎
        PC.ₐ k ∎
               where open ecategory-aux-only ℂ
    -- end private
    Xw×Y : ℙ.wproduct-of X Y
    Xw×Y = record
      { w×sp/ = ℙ.mkspan/ wπ₁ wπ₂
      ; iswprd = record
                { w<_,_> = wun
                ; w×tr₁ = λ {_} {h} {k} → PC.faith-pf (PC.∘ax-rfˢ ⊙ tr₁PC h k)
                ; w×tr₂ = λ {_} {h} {k} → PC.faith-pf (PC.∘ax-rfˢ ⊙ tr₂PC h k)
                }
      }
      where open ecategory-aux-only ℂ
  -- end cover-of-product-is-weak-product


  dom-has-bin-weak-products : has-bin-weak-products ℙ
  dom-has-bin-weak-products = record
    { wprd-of = Xw×Y
    }
    where module tmp (X Y : ℙ.Obj) = cover-of-product-is-weak-product (flℂ.prd-of (PC.ₒ X) (PC.ₒ Y))
          open tmp



  module cover-of-equaliser-is-weak-equaliser {X Y : ℙ.Obj} {f f' : || ℙ.Hom X Y ||}
                                           (eql : ℂ.equaliser-of (PC.ₐ f) (PC.ₐ f'))
                                           where
    private
      module PCf~PCf' = ℂ.equaliser-of eql
      module ~rc = PC.rcov-of PCf~PCf'.Eql
      wE : ℙ.Obj
      wE = PC.rcov-of.Ob PCf~PCf'.Eql
      we : || ℙ.Hom wE X ||
      we = PC.full.ar (PCf~PCf'.eqlar ℂ.∘ ~rc.ar)
      weq : f ℙ.∘ we ℙ.~ f' ℙ.∘ we
      weq = PC.faith-pf (PC.∘ax-rfˢ ⊙ ∘e (PC.full.pf {_}) r ⊙ ass
                        ⊙ ∘e r PCf~PCf'.eqleq ⊙ assˢ ⊙ ∘e (PC.full.pf {_} ˢ) r ⊙ PC.∘ax-rf)
          where open ecategory-aux-only ℂ

      wun-aux : {Z : ℙ.Obj} {h : || ℙ.Hom Z X ||} (pf : f ℙ.∘ h ℙ.~ f' ℙ.∘ h)
                   → || ℂ.Hom (PC.ₒ Z) (PC.ₒ wE) ||
      wun-aux {Z} {h} pf = PC.rprj.lift Z ~rc.is-repi (PC.ₐ h PCf~PCf'.|eql[ PC.∘∘ pf ])
      wun-aux-tr : {Z : ℙ.Obj} {h : || ℙ.Hom Z X ||} (pf : f ℙ.∘ h ℙ.~ f' ℙ.∘ h)
                   → ~rc.ar ℂ.∘ wun-aux pf ℂ.~ PC.ₐ h PCf~PCf'.|eql[ PC.∘∘ pf ]
      wun-aux-tr {Z} {h} pf = PC.rprj.lift-tr Z {repi = ~rc.is-repi} {PC.ₐ h PCf~PCf'.|eql[ PC.∘∘ pf ]}
      wun : {Z : ℙ.Obj} (h : || ℙ.Hom Z X ||) (pf : f ℙ.∘ h ℙ.~ f' ℙ.∘ h) → || ℙ.Hom Z wE ||
      wun _ pf = PC.full.ar (wun-aux pf)
      trPC : {Z : ℙ.Obj} {h : || ℙ.Hom Z X ||} (pf : f ℙ.∘ h ℙ.~ f' ℙ.∘ h)
                → PC.ₐ we ℂ.∘ PC.ₐ (wun h pf) ℂ.~ PC.ₐ h
      trPC {_} {h} pf = ~proof
        PC.ₐ we ℂ.∘ PC.ₐ (wun h pf)                             ~[ ∘e PC.full.pf PC.full.pf ⊙ assˢ ] /
        PCf~PCf'.eqlar  ℂ.∘ ~rc.ar ℂ.∘ wun-aux pf              ~[ ∘e (wun-aux-tr pf) r ] /
        PCf~PCf'.eqlar ℂ.∘ PC.ₐ h PCf~PCf'.|eql[ PC.∘∘ pf ]     ~[ PCf~PCf'.eqltr (PC.∘∘ pf) ]∎
        PC.ₐ h ∎
              where open ecategory-aux-only ℂ
    -- end private
    fw~f' : ℙ.wequaliser-of f f'
    fw~f' = record
      { wEql = wE
      ; weqlar = we
      ; weqleq = weq
      ; isweql = record
               { _|weql[_] = wun
               ; weqltr = λ pf → PC.faith-pf (PC.∘ax-rfˢ ⊙ trPC pf)
               }
      }
      where open ecategory-aux-only ℂ
  -- end cover-of-equaliser-is-weak-equaliser


  dom-has-weak-equalisers : has-weak-equalisers ℙ
  dom-has-weak-equalisers = record
    { weql-of = fw~f'
    }
    where module tmp {X Y : ℙ.Obj} (f f' : || ℙ.Hom X Y ||)
                     = cover-of-equaliser-is-weak-equaliser (flℂ.eql-of (PC.ₐ f) (PC.ₐ f'))
          open tmp



  module cover-of-pullback-is-weak-pullback {X Y Z : ℙ.Obj} {f : || ℙ.Hom X Z ||} {g : || ℙ.Hom Y Z ||}
                                         (pb : ℂ.pullback-of (PC.ₐ f) (PC.ₐ g))
                                         where
    private
      module PCf×/PCg = ℂ.pullback-of-not pb
      module ×/rc = PC.rcov-of PCf×/PCg.ul
      w×/Ob : ℙ.Obj
      w×/Ob = PC.rcov-of.Ob PCf×/PCg.ul
      wπ/₁ : || ℙ.Hom w×/Ob X ||
      wπ/₁ = PC.full.ar (PCf×/PCg.π/₁ ℂ.∘ ×/rc.ar)
      wπ/₂ : || ℙ.Hom w×/Ob Y ||
      wπ/₂ = PC.full.ar (PCf×/PCg.π/₂ ℂ.∘ ×/rc.ar)
      w×/sqpf : f ℙ.∘ wπ/₁ ℙ.~ g ℙ.∘ wπ/₂
      w×/sqpf = PC.faith-pf (~proof
        PC.ₐ (f ℙ.∘ wπ/₁)                     ~[ PC.∘ax-rfˢ ⊙ ∘e PC.full.pf r ] /
        PC.ₐ f ℂ.∘ PCf×/PCg.π/₁ ℂ.∘ ×/rc.ar   ~[ ass ⊙ ∘e r PCf×/PCg.×/sqpf ⊙ assˢ ] /
        PC.ₐ g ℂ.∘ PCf×/PCg.π/₂ ℂ.∘ ×/rc.ar   ~[ ∘e (PC.full.pf ˢ) r ⊙ PC.∘ax-rf ]∎
        PC.ₐ (g ℙ.∘ wπ/₂) ∎)
              where open ecategory-aux-only ℂ
      wun-aux : {W : ℙ.Obj} {h : || ℙ.Hom W X ||} {k : || ℙ.Hom W Y ||}
                   → f ℙ.∘ h ℙ.~ g ℙ.∘ k → || ℂ.Hom (PC.ₒ W) (PC.ₒ w×/Ob) ||
      wun-aux {W} {h} {k} pf = PC.rprj.lift W ×/rc.is-repi PCf×/PCg.⟨ PC.ₐ h , PC.ₐ k ⟩[ PC.∘∘ pf ]
      wun-aux-tr : {W : ℙ.Obj} {h : || ℙ.Hom W X ||} {k : || ℙ.Hom W Y ||} (pf : f ℙ.∘ h ℙ.~ g ℙ.∘ k)
                      → ×/rc.ar ℂ.∘ wun-aux pf ℂ.~ PCf×/PCg.⟨ PC.ₐ h , PC.ₐ k ⟩[ PC.∘∘ pf ]
      wun-aux-tr {W} {h} {k} pf = PC.rprj.lift-tr W {repi = ×/rc.is-repi} {PCf×/PCg.⟨ PC.ₐ h , PC.ₐ k ⟩[ PC.∘∘ pf ]}
      wun : {W : ℙ.Obj} (h : || ℙ.Hom W X ||) (k : || ℙ.Hom W Y ||)
               → f ℙ.∘ h ℙ.~ g ℙ.∘ k → || ℙ.Hom W w×/Ob ||
      wun h k pf = PC.full.ar (wun-aux pf)
      tr₁PC : {W : ℙ.Obj} {h : || ℙ.Hom W X ||} {k : || ℙ.Hom W Y ||} (pf : f ℙ.∘ h ℙ.~ g ℙ.∘ k)
                 → PC.ₐ wπ/₁ ℂ.∘ PC.ₐ (wun h k pf) ℂ.~ PC.ₐ h
      tr₁PC {W} {h} {k} pf = ~proof
        PC.ₐ wπ/₁ ℂ.∘ PC.ₐ (wun h k pf)                                ~[ ∘e PC.full.pf PC.full.pf ⊙ assˢ ] /
        PCf×/PCg.π/₁ ℂ.∘ ×/rc.ar ℂ.∘ wun-aux pf                        ~[ ∘e (wun-aux-tr pf) r ] /
        PCf×/PCg.π/₁ ℂ.∘ PCf×/PCg.⟨ PC.ₐ h , PC.ₐ k ⟩[ PC.∘∘ pf ]        ~[ PCf×/PCg.×/tr₁ (PC.∘∘ pf) ]∎
        PC.ₐ h ∎
                where open ecategory-aux-only ℂ
      tr₂PC : {W : ℙ.Obj} {h : || ℙ.Hom W X ||} {k : || ℙ.Hom W Y ||} (pf : f ℙ.∘ h ℙ.~ g ℙ.∘ k)
                 → PC.ₐ wπ/₂ ℂ.∘ PC.ₐ (wun h k pf) ℂ.~ PC.ₐ k
      tr₂PC {W} {h} {k} pf = ~proof
        PC.ₐ wπ/₂ ℂ.∘ PC.ₐ (wun h k pf)                               ~[ ∘e PC.full.pf PC.full.pf ⊙ assˢ ] /
        PCf×/PCg.π/₂ ℂ.∘ ×/rc.ar ℂ.∘ wun-aux pf                       ~[ ∘e (wun-aux-tr pf) r ] /
        PCf×/PCg.π/₂ ℂ.∘ PCf×/PCg.⟨ PC.ₐ h , PC.ₐ k ⟩[ PC.∘∘ pf ]       ~[ PCf×/PCg.×/tr₂ (PC.∘∘ pf) ]∎
        PC.ₐ k ∎
               where open ecategory-aux-only ℂ
    -- end private
    fw×/g : ℙ.wpullback-of f g
    fw×/g = record
      { w×/sq/ = ℙ.mksq/ w×/sqpf
      ; w×/iswpbsq = record
                   { w⟨_,_⟩[_] = wun
                   ; w×/tr₁ = λ pf → PC.faith-pf (PC.∘ax-rfˢ ⊙ tr₁PC pf)
                   ; w×/tr₂ = λ pf → PC.faith-pf (PC.∘ax-rfˢ ⊙ tr₂PC pf)
                   }
      }
      where open ecategory-aux-only ℂ
  -- end cover-of-pullback-is-weak-pullback


  dom-has-weak-pullbacks : has-weak-pullbacks ℙ
  dom-has-weak-pullbacks = record
    { wpb-of = fw×/g
    }
    where module tmp {X Y Z : ℙ.Obj} (f : || ℙ.Hom X Z ||) (g : || ℙ.Hom Y Z ||)
                     = cover-of-pullback-is-weak-pullback (flℂ.pb-of (PC.ₐ f) (PC.ₐ g))
          open tmp



  dom-has-fin-weak-limits : has-fin-weak-limits ℙ
  dom-has-fin-weak-limits = record
    { haswtrm = dom-has-weak-terminal
    ; haswprd = dom-has-bin-weak-products
    ; hasweql = dom-has-weak-equalisers
    ; haswpb = dom-has-weak-pullbacks
    ; haswbw = has-weql+wpb⇒has-wbw dom-has-weak-equalisers dom-has-weak-pullbacks
    }
-- end prj-cover-of-lex-is-wlex


proj-cov-has-wlim : {ℂ : ecategory} {ℙ : ecategory} {PC : efunctor ℙ ℂ}
                    (ispjcov : is-projective-cover PC)
                      → has-fin-limits ℂ → has-fin-weak-limits ℙ
proj-cov-has-wlim ispjcov hasfl = dom-has-fin-weak-limits
                                where open prj-cover-of-lex-is-wlex hasfl ispjcov
                              



-- Projective cover into a regular category is left covering

module projective-cover-of-reg-cat-is-left-cov {𝔼 : ecategory} (𝔼isreg : is-regular 𝔼)
                                               {ℙ : ecategory} {PC : efunctor ℙ 𝔼} (ispjcov : is-projective-cover PC)
                                               where
  private
    module ℙ where
      open ecategory ℙ public
      open comm-shapes ℙ public
      open epis&monos-defs ℙ public
      open epis&monos-props ℙ public
      open kernel-pairs-defs ℙ public
      open pseudo-eq-rel-defs ℙ public
      open finite-limits-d&p ℙ public
      open finite-weak-limits-d&p ℙ public
      open limits→weak-limits ℙ public
    module 𝔼 where
      open ecategory 𝔼 public
      open comm-shapes 𝔼 public
      open iso-defs 𝔼 public
      open epis&monos-defs 𝔼 public
      open epis&monos-props 𝔼 public
      open kernel-pairs-defs 𝔼 public
      open eq-rel-defs 𝔼 public
      open finite-limits-d&p 𝔼 public
      --open finite-weak-limits-d&p 𝔼 public
      --open limits→weak-limits 𝔼 public
      --open relations-among-limit-diagrams 𝔼 public
      open projective-defs 𝔼 public
    module r𝔼 where
      open regular-cat-d&p 𝔼isreg public
      --open has-fin-limits hasfl public
      open has-terminal hastrm public
      open has-bin-products hasprd using (prd-of) public
      open has-equalisers haseql using (eql-of) public
      open has-pullbacks haspb using (pb-of) public
      open has-bows hasbw using (bw-of) public
    fwlℙ : has-fin-weak-limits ℙ
    fwlℙ = proj-cov-has-wlim ispjcov r𝔼.hasfl
    module fwlℙ where
      open has-fin-weak-limits fwlℙ public
      open has-weak-pullbacks haswpb using (wpb-of) public
    module PC where
      open efunctor-aux PC public
      open is-projective-cover ispjcov public
      open prj-cover-of-lex-is-wlex r𝔼.hasfl ispjcov public
      --open full public
      --open faith public

  module PC-is-left-cov-trm  {PT : ℙ.Obj} (PT-pf : ℙ.is-wterminal PT)
                             {CT : 𝔼.Obj} (CT-pf : 𝔼.is-terminal CT)
                             (cov! : || 𝔼.Hom (PC.ₒ PT) CT ||)
                             where
    private
      module PT = ℙ.is-wterminal PT-pf
      module CT = 𝔼.is-terminal CT-pf
      module rcT = PC.rcov-of CT
      module wTrc where
        Ob : ℙ.Obj
        Ob = PC.cover-of-terminal-is-weak-terminal.wT CT-pf
        open ℙ.is-wterminal (PC.cover-of-terminal-is-weak-terminal.iswtrm CT-pf) public
    med-ar : || ℙ.Hom wTrc.Ob PT ||
    med-ar = PT.w! wTrc.Ob
    cov!-pf : cov! 𝔼.∘ PC.ₐ med-ar 𝔼.~ rcT.ar
    cov!-pf = CT.!uqg
    cov!-repi : 𝔼.is-regular-epi cov!
    cov!-repi = r𝔼.repi-triang cov!-pf rcT.is-repi
 -- end PC-is-left-cov-trm

  PC-is-left-cov-trm : is-left-covering-trm PC
  PC-is-left-cov-trm = record
    { trmuniv-is-repi = cov!-repi
    }
    where open PC-is-left-cov-trm


  module PC-is-left-cov-prd  {X Y : ℙ.Obj} {V : ℙ.Obj} {Pp₁ : || ℙ.Hom V X ||} {Pp₂ : || ℙ.Hom V Y ||}
                             (Pw× : ℙ.is-wproduct (ℙ.mkspan Pp₁ Pp₂))
                             {P : 𝔼.Obj} {Ep₁ : || 𝔼.Hom P (PC.ₒ X) ||} {Ep₂ : || 𝔼.Hom P (PC.ₒ Y) ||}
                             (E× : 𝔼.is-product (𝔼.mkspan Ep₁ Ep₂)) {cov× : || 𝔼.Hom (PC.ₒ V) P ||}
                             (cov×-tr₁ : Ep₁ 𝔼.∘ cov× 𝔼.~ PC.ₐ Pp₁) (cov×-tr₂ : Ep₂ 𝔼.∘ cov× 𝔼.~ PC.ₐ Pp₂)
                             where
    private
      module Pw× = ℙ.bin-wproduct-not (ℙ.mkw× Pw×)
      module E× = 𝔼.bin-product-not (𝔼.mk× E×)
      module rc× = PC.rcov-of E×.O12
      module w×rc = ℙ.wproduct-of-not (PC.cover-of-product-is-weak-product.Xw×Y (𝔼.mk×of E×))
    med-ar : || ℙ.Hom w×rc.O12 V ||
    med-ar = Pw×.w< w×rc.wπ₁ , w×rc.wπ₂ >
    cov×-pf : cov× 𝔼.∘ PC.ₐ med-ar 𝔼.~ rc×.ar
    cov×-pf = E×.×uq (~proof E×.π₁ 𝔼.∘ cov× 𝔼.∘ PC.ₐ med-ar      ~[ ass ⊙ ∘e r cov×-tr₁ ] /
                             PC.ₐ Pw×.wπ₁ 𝔼.∘ PC.ₐ med-ar         ~[ PC.∘ax Pw×.w×tr₁ ⊙ PC.full.pf ]∎
                             E×.π₁ 𝔼.∘ rc×.ar ∎)
                     (~proof E×.π₂ 𝔼.∘ cov× 𝔼.∘ PC.ₐ med-ar      ~[ ass ⊙ ∘e r cov×-tr₂ ] /
                             PC.ₐ Pw×.wπ₂ 𝔼.∘ PC.ₐ med-ar         ~[ PC.∘ax Pw×.w×tr₂ ⊙ PC.full.pf ]∎
                             E×.π₂ 𝔼.∘ rc×.ar ∎)
              where open ecategory-aux-only 𝔼
    cov×-repi : 𝔼.is-regular-epi cov×
    cov×-repi = r𝔼.repi-triang cov×-pf rc×.is-repi
  -- end PC-is-left-cov-prd

  PC-is-left-cov-prd : is-left-covering-prd PC
  PC-is-left-cov-prd = record
    { prduniv-is-repi = λ P×of E×of tr₁ tr₂ → cov×-repi (P.iswprd P×of) (E.×isprd E×of) tr₁ tr₂
    }
    where open PC-is-left-cov-prd
          module P = ℙ.wproduct-of
          module E = 𝔼.product-of


  module PC-is-left-cov-eql {X Y : ℙ.Obj} {f₁ f₂ : || ℙ.Hom X Y ||}
                            {PwE : ℙ.Obj} {Pwe : || ℙ.Hom PwE X ||} {Pweql-eq : f₁ ℙ.∘ Pwe ℙ.~ f₂ ℙ.∘ Pwe}
                            (Pweql-pf : ℙ.is-wequaliser Pweql-eq) {EE : 𝔼.Obj} {Ee : || 𝔼.Hom EE (PC.ₒ X) ||}
                            {Eeql-eq : (PC.ₐ f₁) 𝔼.∘ Ee 𝔼.~ (PC.ₐ f₂) 𝔼.∘ Ee} (Eeql-pf : 𝔼.is-equaliser Eeql-eq)
                            {coveql : || 𝔼.Hom (PC.ₒ PwE) EE ||} (coveql-tr : Ee 𝔼.∘ coveql 𝔼.~ PC.ₐ Pwe)
                            where
    private
      module Pe = ℙ.wequaliser-of (ℙ.mkweql-of Pweql-pf)
      module Ee = 𝔼.equaliser-of (𝔼.mkeql-of Eeql-pf)
      module rce = PC.rcov-of Ee.Eql
      module werc = ℙ.wequaliser-of (PC.cover-of-equaliser-is-weak-equaliser.fw~f' (𝔼.mkeql-of Eeql-pf))
    med-ar : || ℙ.Hom werc.wEql Pe.wEql ||
    med-ar =  werc.weqlar Pe.|weql[ werc.weqleq ]
    coveql-pf : coveql 𝔼.∘ PC.ₐ med-ar 𝔼.~ rce.ar
    coveql-pf = Ee.eqluq (~proof
      Ee.eqlar 𝔼.∘ coveql 𝔼.∘ PC.ₐ med-ar     ~[ ass ⊙ ∘e r coveql-tr ] /
      PC.ₐ Pe.weqlar 𝔼.∘ PC.ₐ med-ar           ~[ PC.∘ax (Pe.weqltr werc.weqleq) ] /
      PC.ₐ werc.weqlar                         ~[ PC.full.pf ]∎
      Ee.eqlar 𝔼.∘ rce.ar ∎)
              where open ecategory-aux-only 𝔼
    coveql-repi : 𝔼.is-regular-epi coveql
    coveql-repi = r𝔼.repi-triang coveql-pf rce.is-repi
-- end PC-is-left-cov-eql

  PC-is-left-cov-eql : is-left-covering-eql PC
  PC-is-left-cov-eql = record
    { eqluniv-is-repi = λ weqlof eqlof tr → coveql-repi (P.isweql weqlof) (E.iseql eqlof) tr
    }
    where open PC-is-left-cov-eql
          module P = ℙ.wequaliser-of
          module E = 𝔼.equaliser-of


  module PC-is-left-cov-pb  {Z X Y : ℙ.Obj} {x : || ℙ.Hom X Z ||} {y : || ℙ.Hom Y Z ||}
                            {V : ℙ.Obj} {Pp₁ : || ℙ.Hom V X ||} {Pp₂ : || ℙ.Hom V Y ||} {Peqpf : x ℙ.∘ Pp₁ ℙ.~ y ℙ.∘ Pp₂}
                            (Pw×/ : ℙ.is-wpb-square (ℙ.mksq (ℙ.mksq/ Peqpf)))
                            {P : 𝔼.Obj} {p₁ : || 𝔼.Hom P (PC.ₒ X) ||} {p₂ : || 𝔼.Hom P (PC.ₒ Y) ||}
                            {Eeqpf : PC.ₐ x 𝔼.∘ p₁ 𝔼.~ PC.ₐ y 𝔼.∘ p₂} (E×/ : 𝔼.is-pb-square (𝔼.mksq (𝔼.mksq/ Eeqpf)))
                            {cov×/ : || 𝔼.Hom (PC.ₒ V) P ||}
                            (cov×/-tr₁ : p₁ 𝔼.∘ cov×/ 𝔼.~ PC.ₐ Pp₁) (cov×/-tr₂ : p₂ 𝔼.∘ cov×/ 𝔼.~ PC.ₐ Pp₂)                           
                            where
    private
      module Pw×/ = ℙ.wpullback-sq-not (ℙ.mkwpb-sq Pw×/)
      module E×/ = 𝔼.pullback-sq-not (𝔼.mkpb-sq E×/)
      module rc×/ = PC.rcov-of E×/.ul
      module w×/rc = ℙ.wpullback-of-not (PC.cover-of-pullback-is-weak-pullback.fw×/g (𝔼.mkpb-of E×/))
    med-ar : || ℙ.Hom w×/rc.ul V ||
    med-ar = Pw×/.w⟨ w×/rc.wπ/₁ , w×/rc.wπ/₂ ⟩[ w×/rc.w×/sqpf ]
    cov×/-pf : cov×/ 𝔼.∘ PC.ₐ med-ar 𝔼.~ rc×/.ar
    cov×/-pf = E×/.×/uq (~proof E×/.π/₁ 𝔼.∘ cov×/ 𝔼.∘ PC.ₐ med-ar      ~[ ass ⊙ ∘e r cov×/-tr₁ ] /
                                PC.ₐ Pw×/.wπ/₁ 𝔼.∘ PC.ₐ med-ar         ~[ PC.∘ax (Pw×/.w×/tr₁ w×/rc.w×/sqpf) ⊙ PC.full.pf ]∎
                                E×/.π/₁ 𝔼.∘ rc×/.ar ∎)
                        (~proof E×/.π/₂ 𝔼.∘ cov×/ 𝔼.∘ PC.ₐ med-ar      ~[ ass ⊙ ∘e r cov×/-tr₂ ] /
                                PC.ₐ Pw×/.wπ/₂ 𝔼.∘ PC.ₐ med-ar         ~[ PC.∘ax (Pw×/.w×/tr₂ w×/rc.w×/sqpf) ⊙ PC.full.pf ]∎
                                E×/.π/₂ 𝔼.∘ rc×/.ar ∎)
              where open ecategory-aux-only 𝔼
    cov×/-repi : 𝔼.is-regular-epi cov×/
    cov×/-repi = r𝔼.repi-triang cov×/-pf rc×/.is-repi
  -- end PC-is-left-cov-pb

  PC-is-left-cov-pb : is-left-covering-pb PC
  PC-is-left-cov-pb = record
    { pbuniv-is-repi = λ P×/of E×/of tr₁ tr₂ → cov×/-repi (P.w×/iswpbsq P×/of) (E.×/ispbsq E×/of) tr₁ tr₂
    }
    where open PC-is-left-cov-pb
          module P = ℙ.wpullback-of
          module E = 𝔼.pullback-of

  PC-is-left-cov : is-left-covering PC
  PC-is-left-cov = record
    { lc! = PC-is-left-cov-trm
    ; lc× = PC-is-left-cov-prd
    ; lceql = PC-is-left-cov-eql
    ; lc×/ = PC-is-left-cov-pb
    ; lcbw = lcov-eql+pb→lcov-bw 𝔼isreg fwlℙ.hasweql fwlℙ.haswpb PC-is-left-cov-eql PC-is-left-cov-pb
    }

-- end projective-cover-of-reg-cat-is-left-cov


pjcov-of-reg-is-lcov : {𝔼 : ecategory} (𝔼isreg : is-regular 𝔼) {ℙ : ecategory}
                    {PC : efunctor ℙ 𝔼} (ispjcov : is-projective-cover PC)
                      → is-left-covering PC
pjcov-of-reg-is-lcov 𝔼isreg ispjcov = PC-is-left-cov
                                    where open projective-cover-of-reg-cat-is-left-cov 𝔼isreg ispjcov

pjcov-of-ex-is-lcov : {𝔼 : ecategory} (𝔼isex : is-exact 𝔼) {ℙ : ecategory}
                    {PC : efunctor ℙ 𝔼} (ispjcov : is-projective-cover PC)
                      → is-left-covering PC
pjcov-of-ex-is-lcov 𝔼isex ispjcov = pjcov-of-reg-is-lcov 𝔼isreg ispjcov
                                   where open exact-cat-d&p 𝔼isex using () renaming (is-reg to 𝔼isreg)


--   -- Peq in ℙ from quasi-exact seq in 𝔼

--   module Peq-from-Obj (A : 𝔼.Obj) where
--     module rc where
--       open PC.rcov-of A public
--       open PC.rprj Ob public
--     private
--       kpA : 𝔼.pullback-of rc.ar rc.ar
--       kpA = r𝔼.pb-of rc.ar rc.ar
--       module kpA = 𝔼.pullback-of-not kpA
--     exs : 𝔼.is-exact-seq kpA.π/₁ kpA.π/₂ rc.ar
--     exs = record
--       { iscoeq = 𝔼.repi-is-coeq-of-ker-pair rc.is-repi kpA
--       ; iskerpair = kpA.×/ispbsq
--       }
--     module exs where
--       open 𝔼.is-exact-seq exs using (iscoeq; iskerpair) public
--       open 𝔼.pullback-of-not kpA public
--       open 𝔼.is-coeq iscoeq public
--       open 𝔼.is-eq-rel (𝔼.is-kerp+τpb→is-eqr (record { ispbsq = ×/ispbsq }) (r𝔼.pb-of π/₂ π/₁)) public
--     module rcK where
--       open PC.rcov-of exs.ul public
--       open PC.rprj Ob public
--     private
--       %0A %1A : || ℙ.Hom rcK.Ob rc.Ob ||
--       %0A = PC.full-ar (exs.π/₁ 𝔼.∘ rcK.ar)
--       %1A = PC.full-ar (exs.π/₂ 𝔼.∘ rcK.ar)
                
--     peq/ : ℙ.PeqOver rc.Ob
--     peq/ = record
--       { Hi = rcK.Ob
--       ; %0 = %0A
--       ; %1 = %1A
--       ; ispeq = record
--         { isρ = record
--           { ρ = PC.full-ar (rc.lift rcK.is-repi exs.ρ)
--           ; ρ-ax₀ = PC.faith-pf (~proof
--                   PC.ₐ (%0A ℙ.∘ PC.full-ar (rc.lift rcK.is-repi exs.ρ))
--                                                      ~[ PC.∘ax-rf ˢ ⊙ ∘e PC.full-pf PC.full-pf ⊙ assˢ ] /
--                   exs.π/₁ 𝔼.∘ rcK.ar 𝔼.∘ rc.lift rcK.is-repi exs.ρ              ~[ ∘e rc.lift-tr r ] /
--                   exs.π/₁ 𝔼.∘ exs.ρ                                               ~[ exs.ρ-ax₀ ⊙ PC.idˢ ]∎
--                   PC.ₐ (ℙ.idar rc.Ob) ∎)
--           ; ρ-ax₁ = PC.faith-pf (~proof
--                   PC.ₐ (%1A ℙ.∘ PC.full-ar (rc.lift rcK.is-repi exs.ρ))
--                                                      ~[ PC.∘ax-rf ˢ ⊙ ∘e PC.full-pf PC.full-pf ⊙ assˢ ] /
--                   exs.π/₂ 𝔼.∘ rcK.ar 𝔼.∘ rc.lift rcK.is-repi exs.ρ              ~[ ∘e rc.lift-tr r ] /
--                   exs.π/₂ 𝔼.∘ exs.ρ                                             ~[ exs.ρ-ax₁ ⊙ PC.idˢ ]∎
--                   PC.ₐ (ℙ.idar rc.Ob) ∎)
--           }
--         ; isσ = record
--           { σ = PC.full-ar (rcK.lift rcK.is-repi (exs.σ 𝔼.∘ rcK.ar))
--           ; σ-ax₀ = PC.faith-pf (~proof
--                   PC.ₐ (%0A ℙ.∘ PC.full-ar (rcK.lift rcK.is-repi (exs.σ 𝔼.∘ rcK.ar)))
--                                                      ~[ PC.∘ax-rf ˢ ⊙ ∘e PC.full-pf PC.full-pf ⊙ assˢ ] /
--                   exs.π/₁ 𝔼.∘ rcK.ar 𝔼.∘ rcK.lift rcK.is-repi (exs.σ 𝔼.∘ rcK.ar)      ~[ ∘e rcK.lift-tr r ] /
--                   exs.π/₁ 𝔼.∘ exs.σ 𝔼.∘ rcK.ar                    ~[ ass ⊙ ∘e r exs.σ-ax₀ ⊙ PC.full-pf ˢ ]∎
--                   PC.ₐ %1A ∎)
--           ; σ-ax₁ = PC.faith-pf (~proof
--                   PC.ₐ (%1A ℙ.∘ PC.full-ar (rcK.lift rcK.is-repi (exs.σ 𝔼.∘ rcK.ar)))
--                                                      ~[ PC.∘ax-rf ˢ ⊙ ∘e PC.full-pf PC.full-pf ⊙ assˢ ] /
--                   exs.π/₂ 𝔼.∘ rcK.ar 𝔼.∘ rcK.lift rcK.is-repi (exs.σ 𝔼.∘ rcK.ar)      ~[ ∘e rcK.lift-tr r ] /
--                   exs.π/₂ 𝔼.∘ exs.σ 𝔼.∘ rcK.ar                    ~[ ass ⊙ ∘e r exs.σ-ax₁ ⊙ PC.full-pf ˢ ]∎
--                   PC.ₐ %0A ∎)
--           }
--         ; τwpb = τwpb
--         ; iswτ = record
--           { τ = PC.full-ar (τwpb.lift rcK.is-repi τaux)
--           ; τ-ax₀ = PC.faith-pf (~proof
--                   PC.ₐ (%0A ℙ.∘ PC.full-ar (τwpb.lift rcK.is-repi τaux))
--                                                       ~[ PC.∘ax-rf ˢ ⊙ ∘e PC.full-pf PC.full-pf ⊙ assˢ ] /
--                   exs.π/₁ 𝔼.∘ rcK.ar 𝔼.∘ τwpb.lift rcK.is-repi τaux      ~[ ∘e τwpb.lift-tr r ] /
--                   exs.π/₁ 𝔼.∘  τaux                                       ~[ exs.×/tr₁ τaux-pf ]∎
--                   PC.ₐ (%0A ℙ.∘ τwpb.wπ/₁) ∎)
--           ; τ-ax₁ = PC.faith-pf (~proof
--                   PC.ₐ (%1A ℙ.∘ PC.full-ar (τwpb.lift rcK.is-repi τaux))
--                                                       ~[ PC.∘ax-rf ˢ ⊙ ∘e PC.full-pf PC.full-pf ⊙ assˢ ] /
--                   exs.π/₂ 𝔼.∘ rcK.ar 𝔼.∘ τwpb.lift rcK.is-repi τaux      ~[ ∘e τwpb.lift-tr r ] /
--                   exs.π/₂ 𝔼.∘  τaux                                       ~[ exs.×/tr₂ τaux-pf ]∎
--                   PC.ₐ (%1A ℙ.∘ τwpb.wπ/₂) ∎)
--           }
--         }
--       }
--       where open ecategory-aux-only 𝔼
--             τwpb : ℙ.wpullback-of %1A %0A
--             τwpb = fwlℙ.wpb-of %1A %0A
--             module τwpb where
--               open ℙ.wpullback-of τwpb public
--               open PC.rprj ul public
--             τaux-pf : rc.ar 𝔼.∘ PC.ₐ (%0A ℙ.∘ τwpb.wπ/₁) 𝔼.~ rc.ar 𝔼.∘ PC.ₐ (%1A ℙ.∘ τwpb.wπ/₂)
--             τaux-pf = ~proof
--               rc.ar 𝔼.∘ PC.ₐ (%0A ℙ.∘ τwpb.wπ/₁)                ~[ ∘e (PC.∘ax-rf ˢ ⊙ ∘e r PC.full-pf ⊙ assˢ) r ] /
--               rc.ar 𝔼.∘ exs.π/₁ 𝔼.∘ rcK.ar 𝔼.∘ PC.ₐ τwpb.wπ/₁    ~[ ass ⊙ ∘e r exs.×/sqpf ⊙ assˢ ] /
--               rc.ar 𝔼.∘ exs.π/₂ 𝔼.∘ rcK.ar 𝔼.∘ PC.ₐ τwpb.wπ/₁ ~[ ∘e (ass ⊙ ∘e r (PC.full-pf ˢ) ⊙ PC.∘ax-rf) r ] /
--               rc.ar 𝔼.∘ PC.ₐ (%1A ℙ.∘ τwpb.wπ/₁)                  ~[ ∘e (PC.ext τwpb.w×/sqpf) r ] /
--               rc.ar 𝔼.∘ PC.ₐ (%0A ℙ.∘ τwpb.wπ/₂)                 ~[ ∘e (PC.∘ax-rf ˢ ⊙ ∘e r PC.full-pf ⊙ assˢ) r ] /
--               rc.ar 𝔼.∘ exs.π/₁ 𝔼.∘ rcK.ar 𝔼.∘ PC.ₐ τwpb.wπ/₂    ~[ ass ⊙ ∘e r exs.×/sqpf ⊙ assˢ ] /
--               rc.ar 𝔼.∘ exs.π/₂ 𝔼.∘ rcK.ar 𝔼.∘ PC.ₐ τwpb.wπ/₂   ~[ ∘e (ass ⊙ ∘e r (PC.full-pf ˢ) ⊙ PC.∘ax-rf) r ]∎
--               rc.ar 𝔼.∘ PC.ₐ (%1A ℙ.∘ τwpb.wπ/₂) ∎
--             τaux : || 𝔼.Hom (PC.ₒ τwpb.ul) exs.ul ||
--             τaux = exs.⟨ PC.ₐ (%0A ℙ.∘ τwpb.wπ/₁) , PC.ₐ (%1A ℙ.∘ τwpb.wπ/₂) ⟩[ τaux-pf ]
--     peq : ℙ.Peq
--     peq = ℙ.mkpeq-c peq/
--     module peq = ℙ.Peq peq
--     qexs : 𝔼.is-coeq (PC.ₐ peq.%0) (PC.ₐ peq.%1) rc.ar
--     qexs = 𝔼.epi/coeq-so-coeq (𝔼.repi-is-epic rcK.is-repi) (PC.full-pf ˢ) (PC.full-pf ˢ) exs.iscoeq
--          where open ecategory-aux-only 𝔼 using (_ˢ)
--     module qexs = 𝔼.is-coeq qexs
--   -- end Peq-from-Obj


--   module Peq-mor-from-ar {A B : 𝔼.Obj} (f : || 𝔼.Hom A B ||) where
--     private
--       module dom = Peq-from-Obj A
--       module cod = Peq-from-Obj B
--       lo : || ℙ.Hom dom.rc.Ob cod.rc.Ob ||
--       lo = PC.full-ar (dom.rc.lift cod.rc.is-repi (f 𝔼.∘ dom.rc.ar))
--       hiaux-pf : cod.rc.ar 𝔼.∘ PC.ₐ (lo ℙ.∘ dom.peq.%0) 𝔼.~ cod.rc.ar 𝔼.∘ PC.ₐ (lo ℙ.∘ dom.peq.%1)
--       hiaux-pf = ~proof
--         cod.rc.ar 𝔼.∘ PC.ₐ (lo ℙ.∘ dom.peq.%0)
--                       ~[ ∘e (PC.∘ax-rf ˢ ⊙ ∘e PC.full-pf PC.full-pf) r ⊙ ass ⊙ ∘e r dom.rc.lift-tr ⊙ assˢ ] /
--         f 𝔼.∘ dom.rc.ar 𝔼.∘ dom.exs.π/₁ 𝔼.∘ dom.rcK.ar              ~[ ∘e (ass ⊙ ∘e r dom.exs.×/sqpf ⊙ assˢ) r ] /
--         f 𝔼.∘ dom.rc.ar 𝔼.∘ dom.exs.π/₂ 𝔼.∘ dom.rcK.ar
--               ~[ ass ⊙ ∘e r (dom.rc.lift-tr ˢ) ⊙ assˢ ⊙ ∘e (∘e (PC.full-pf ˢ) (PC.full-pf ˢ) ⊙ PC.∘ax-rf) r ]∎
--         cod.rc.ar 𝔼.∘ PC.ₐ (lo ℙ.∘ dom.peq.%1) ∎
--                where open ecategory-aux-only 𝔼
--       hiaux : || 𝔼.Hom (PC.ₒ dom.rcK.Ob) cod.exs.ul ||
--       hiaux = cod.exs.⟨ PC.ₐ (lo ℙ.∘ dom.peq.%0) , PC.ₐ (lo ℙ.∘ dom.peq.%1) ⟩[ hiaux-pf ]
--       hi : || ℙ.Hom dom.rcK.Ob cod.rcK.Ob ||
--       hi = PC.full-ar (dom.rcK.lift cod.rcK.is-repi hiaux)

--     ar : ℙ.Peq-mor dom.peq cod.peq
--     ar = record
--       { lo = lo
--       ; isext = record
--         { hi = hi
--         ; cmptb₀ = PC.faith-pf (~proof
--                  PC.ₐ (cod.peq.%0 ℙ.∘ hi)
--                       ~[ PC.∘ax-rf ˢ ⊙ ∘e PC.full-pf PC.full-pf ⊙ assˢ ⊙ ∘e dom.rcK.lift-tr r ] /
--                  cod.exs.π/₁ 𝔼.∘ hiaux   ~[ cod.exs.×/tr₁ hiaux-pf ]∎
--                  PC.ₐ (lo ℙ.∘ dom.peq.%0) ∎)
--         ; cmptb₁ = PC.faith-pf (~proof
--                  PC.ₐ (cod.peq.%1 ℙ.∘ hi)
--                       ~[ PC.∘ax-rf ˢ ⊙ ∘e PC.full-pf PC.full-pf ⊙ assˢ ⊙ ∘e dom.rcK.lift-tr r ] /
--                  cod.exs.π/₂ 𝔼.∘ hiaux   ~[ cod.exs.×/tr₂ hiaux-pf ]∎
--                  PC.ₐ (lo ℙ.∘ dom.peq.%1) ∎)
--         }
--       }
--       where open ecategory-aux-only 𝔼
--     module ar = ℙ.Peq-mor ar
--     sqpf : f 𝔼.∘ dom.rc.ar 𝔼.~ cod.rc.ar 𝔼.∘ PC.ₐ ar.lo
--     sqpf = (∘e PC.full-pf r ⊙ dom.rc.lift-tr) ˢ
--          where open ecategory-aux-only 𝔼
--   -- end Peq-mor-from-ar
  
--   module Exℙ where
--     open ecategory Ex ℙ [ fwlℙ ] public
    
--   module PC2Peq-ext {A B : 𝔼.Obj}{f f' : || 𝔼.Hom A B ||}(eqpf : f 𝔼.~ f') where
--     private
--       module peqA where
--         open Peq-from-Obj A public
--         open ℙ.Peq peq public
--       module peqB where
--         open Peq-from-Obj B public
--         open ℙ.Peq peq public
--       module peqf where
--         open Peq-mor-from-ar {A} {B} f public
--         open ℙ.Peq-mor {peqA.peq} {peqB.peq} ar public
--       module peqf'  where
--         open Peq-mor-from-ar {A} {B} f' public
--         open ℙ.Peq-mor {peqA.peq} {peqB.peq} ar public
--     eq : peqf.ar Exℙ.~ peqf'.ar
--     eq = record
--       { hty = PC.full-ar (PC.rprj.lift peqA.Lo peqB.rcK.is-repi
--                                        peqB.exs.⟨ PC.ₐ peqf.lo , PC.ₐ peqf'.lo
--                                                 ⟩[ hty-pf ])
--       ; hty₀ = PC.faith-pf (PC.cmp _ _ ˢ ⊙ ∘e PC.full-pf PC.full-pf ⊙ assˢ
--                            ⊙ ∘e (PC.rprj.lift-tr peqA.Lo) r ⊙ peqB.exs.×/tr₁ hty-pf)
--       ; hty₁ = PC.faith-pf (PC.cmp _ _ ˢ ⊙ ∘e PC.full-pf PC.full-pf ⊙ assˢ
--                            ⊙ ∘e (PC.rprj.lift-tr peqA.Lo) r ⊙ peqB.exs.×/tr₂ hty-pf)
--       }
--       where open ecategory-aux-only 𝔼
--             hty-pf : peqB.rc.ar 𝔼.∘ PC.ₐ peqf.lo 𝔼.~ peqB.rc.ar 𝔼.∘ PC.ₐ peqf'.lo
--             hty-pf = ~proof peqB.rc.ar 𝔼.∘ PC.ₐ peqf.lo   ~[ peqf.sqpf ˢ ] /
--                             f 𝔼.∘ peqA.rc.ar              ~[ ∘e r eqpf ] /
--                             f' 𝔼.∘ peqA.rc.ar             ~[ peqf'.sqpf ]∎
--                             peqB.rc.ar 𝔼.∘ PC.ₐ peqf'.lo ∎
--   -- end PC2Peq-ext
    
--   module PC2Peq-id (A : 𝔼.Obj) where
--     private
--       module peqA where
--         open Peq-from-Obj A public
--         open ℙ.Peq peq public
--     eq : Peq-mor-from-ar.ar (𝔼.idar A) Exℙ.~ Exℙ.idar peqA.peq
--     eq = record
--       { hty = peqA.ρ
--       ; hty₀ = PC.faith-pf ((PC.full-pf ⊙ {!!}) ˢ)
--       ; hty₁ = peqA.ρ-ax₁
--       }
--       where open ecategory-aux-only 𝔼
--     {-record
--       { hty = PC.full-ar (PC.rprj.lift peqA.Lo peqB.rcK.is-repi
--                                        peqB.exs.⟨ PC.ₐ peqf.lo , PC.ₐ peqf'.lo
--                                                 ⟩[ hty-pf ])
--       ; hty₀ = PC.faith-pf (PC.cmp _ _ ˢ ⊙ ∘e PC.full-pf PC.full-pf ⊙ assˢ
--                            ⊙ ∘e (PC.rprj.lift-tr peqA.Lo) r ⊙ peqB.exs.×/tr₁ hty-pf)
--       ; hty₁ = PC.faith-pf (PC.cmp _ _ ˢ ⊙ ∘e PC.full-pf PC.full-pf ⊙ assˢ
--                            ⊙ ∘e (PC.rprj.lift-tr peqA.Lo) r ⊙ peqB.exs.×/tr₂ hty-pf)
--       }
      
--             hty-pf : peqB.rc.ar 𝔼.∘ PC.ₐ peqf.lo 𝔼.~ peqB.rc.ar 𝔼.∘ PC.ₐ peqf'.lo
--             hty-pf = ~proof peqB.rc.ar 𝔼.∘ PC.ₐ peqf.lo   ~[ peqf.sqpf ˢ ] /
--                             f 𝔼.∘ peqA.rc.ar              ~[ ∘e r eqpf ] /
--                             f' 𝔼.∘ peqA.rc.ar             ~[ peqf'.sqpf ]∎
--                             peqB.rc.ar 𝔼.∘ PC.ₐ peqf'.lo ∎-}
--   -- end PC2Peq-id
    
--   PC2Peq : efunctor 𝔼 Ex ℙ [ fwlℙ ]
--   PC2Peq = record
--     { FObj = Peq-from-Obj.peq
--     ; FHom = Peq-mor-from-ar.ar
--     ; isF = record
--           { ext = PC2Peq-ext.eq
--           ; id = λ {A} → {!!} -- record { hty = {!!} ; hty₀ = {!!} ; hty₁ = {!!} }
--           ; cmp = {!!}
--           }
--     }
  
-- -- end projective-cover-on-reg-cat-props


-- -- A projective cover into a regular category is left covering

-- proj-cover-is-left-covering : {𝔼 : ecategory} (regE : is-regular 𝔼) {ℙ : ecategory} {PC : efunctor ℙ 𝔼}
--                                  → is-projective-cover PC → is-left-covering PC
-- proj-cover-is-left-covering 𝔼isreg ispjcov = PC-is-left-cov
--                                             where open projective-cover-on-reg-cat-props 𝔼isreg ispjcov
