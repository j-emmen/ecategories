
{-# OPTIONS --without-K #-}

module ecats.concr-ecats.Std where

open import Agda.Primitive
open import tt-basics.basics
open import tt-basics.id-type
open import tt-basics.setoids renaming (||_|| to ||_||std)
open import ecats.basic-defs.ecat-def&not
open import ecats.basic-defs.arrows
open import ecats.basic-defs.exact-ecat
open import ecats.basic-props.epi&mono
open import ecats.finite-limits.defs&not
open import ecats.finite-limits.props.relations-among-limits
open import ecats.finite-limits.props.pullback
open import ecats.concr-ecats.Type
open import ecats.concr-ecats.Std-lev using (Std) public

-- This module proves some properties of the category of small setoids Std

private
  trm-Std : has-terminal Std
  trm-Std = record
    { trmOb = Freestd N₁
    ; istrm = record
            { ! =  λ _ → record { op = λ _ → 0₁
                                 ; ext = λ _ → =rf }
            ; !uniq = λ f x → contr= (N₁-isContr) (ap f x)
            }
    }

private
  module Type where
    open ecategory-aux Type public
    open Type-is-elemental public
    open comm-shapes Type public
    open wpullback-squares Type public
    open pseudo-eq-rel-defs Type public
    --open elementality-in-Type public
  module Std where
    open ecategory-aux Std public
    open arrows-defs Std public
    open surjective-defs trm-Std public
    open finite-limits Std public
    open pullback-props Std using (is-pbof-stable; is-pbsq-stable) public
    module pbprop =  pullback-props Std hiding (is-pbof-stable; is-pbsq-stable)
    glel : {A : setoid} → || A ||std → || Hom (Freestd N₁) A ||
    glel {A} a = free-std-is-min {A = A} (Type.glel a)
    tyel : {A : setoid} → || Hom (Freestd N₁) A || → || A ||std
    tyel a = a.op 0₁
           where module a = setoidmap a



module surjective-Std {A B : Std.Obj} {f : || Std.Hom A B ||} (issurj : Std.is-surjective f) where
  open Std.is-surjective issurj public
  module f = setoidmap f
  secop : || B ||std → || A ||std
  secop b = Std.tyel (cntimg (Std.glel b))
  secop-pf : {b : || B ||std} → < B > f.op (secop b) ~ b
  secop-pf {b} = cntimg-pf {Std.glel b} 0₁
-- end surjective-Std


-- Std has finite limits


module bin-products-in-Std (A B : Std.Obj) where
  private
    module A = setoid-aux A
    module B = setoid-aux B
  Ob : setoid
  Ob = record
     { object = prod || A ||std || B ||std
     ; _∼_ = λ z z' → prod (< A > prj1 z ~ prj1 z') (< B > prj2 z ~ prj2 z')
     ; istteqrel = record
                 { refl = λ z → pair A.r B.r
                 ; sym = λ pf → pair (prj1 pf A.ˢ) (prj2 pf B.ˢ)
                 ; tra = λ pf1 pf2 → pair (prj1 pf1 A.⊙ prj1 pf2) (prj2 pf1 B.⊙ prj2 pf2)
                 }
     }
  π₁ : || setoidmaps Ob A ||std
  π₁ = record { op = prj1 ; ext = prj1 }
  π₂ : || setoidmaps Ob B ||std
  π₂ = record { op = prj2 ; ext = prj2 }
  module univ {C : Std.Obj} (f : || Std.Hom C A ||) (g : || Std.Hom C B ||) where
    private
      module f = setoidmap f
      module g = setoidmap g
    ar : || setoidmaps C Ob ||std
    ar = record { op = λ x → pair (f.op x) (g.op x)
                ; ext = λ pf → pair (f.ext pf) (g.ext pf)
                }    
  -- end univ

  Stdprd : Std.product-of A B
  Stdprd = record
      { ×sp/ = Std.mkspan/ π₁ π₂
      ; ×isprd = record
               { <_,_> = univ.ar
               ; ×tr₁ = λ _ → A.r
               ; ×tr₂ = λ _ → B.r
               ; ×uq = λ pf1 pf2 x → pair (pf1 x) (pf2 x)
               }
      }
-- end bin-products-in-Std



module equalisers-in-Std {A B : setoid} (f f' : || setoidmaps A B ||) where
  private
    module A = setoid-aux A
    module B = setoid-aux B
    module f = setoidmap f
    module f' = setoidmap f'
  Ob : setoid {lzero}
  Ob = record
    { object = Σ || A ||std (λ x →  < B > f.op x ~ f'.op x)
    ; _∼_ = λ z z' → < A > pj1 z ~ pj1 z'
    ; istteqrel = record
                { refl = λ _ → A.r
                ; sym = A._ˢ
                ; tra = A._⊙_
                }
    }
  module univ {C : setoid} (h : || setoidmaps C A ||) (pf : f Std.∘ h Std.~ f' Std.∘ h) where
    private
      module C = setoid C
      module h = setoidmap h
    ar : || setoidmaps C Ob ||
    ar = record { op = λ x → (h.op x) , (pf x) ; ext = h.ext }
  -- end univ

  Stdeql : Std.equaliser-of f f'
  Stdeql = record
    { Eql = Ob
    ; eqlar = record { op = pj1 ; ext = λ pf → pf }
    ; eqleq = pj2
    ; iseql = record
            { _|eql[_] = univ.ar
            ; eqltr = λ pf _ → A.r
            ; eqluq = λ pf → pf
            }
    }

-- end equalisers-in-Std


private
{-  trm-Std : has-terminal Std
  trm-Std = record
    { trmOb = Freestd N₁
    ; istrm = record
            { ! =  λ _ → record { op = λ _ → 0₁
                                 ; ext = λ _ → =rf }
            ; !uniq = λ f x → contr= (N₁-isContr) (ap f x)
            }
    }
-}
  prd-Std : has-bin-products Std
  prd-Std = record { prd-of = bin-products-in-Std.Stdprd }
  eql-Std : has-equalisers Std
  eql-Std = record { eql-of = equalisers-in-Std.Stdeql }
  pb-Std : has-pullbacks Std
  pb-Std = has-prd+eql⇒has-pb prd-Std eql-Std

flim-Std : has-fin-limits Std
flim-Std = record
         { hastrm = trm-Std
         ; hasprd = prd-Std
         ; haseql = eql-Std
         ; haspb = pb-Std
         ; hasbw = has-eql+pb⇒has-bw eql-Std pb-Std
         }
private
  module flStd where
    open has-fin-limits flim-Std public
    open has-terminal hastrm public
    open has-bin-products hasprd public
    open has-equalisers haseql public
    open has-pullbacks haspb public




-- Surjective functions are epic.

private
  module surjective-is-epic-aux {A B : Std.Obj} {f : || Std.Hom A B ||} (issurj : Std.is-surjective f)
                                {C : setoid} {g g' : || setoidmaps B C ||} (eq : g Std.∘ f Std.~ g' Std.∘ f)
                                where
    private
      module B = setoid-aux B
      module C = setoid-aux C
      module f where
        open setoidmap f public
        open surjective-Std issurj public
      module g = setoidmap g
      module g' = setoidmap g'
    eqf : g Std.~ g'
    eqf = λ b → C.~proof g.op b                      ~[ g.ext (f.secop-pf B.ˢ) ] C./
                          g.op (f.op (f.secop b))     ~[ eq (f.secop b) ] C./
                          g'.op (f.op (f.secop b))    ~[ g'.ext f.secop-pf ]∎
                          g'.op b ∎                          
  -- end surjective-is-epic-aux


surj-is-epic : {A B : Std.Obj} {f : || Std.Hom A B ||} → Std.is-surjective f → Std.is-epic f
surj-is-epic issurj = record
  { epi-pf = λ {C} {g} {g'} → surjective-is-epic-aux.eqf issurj {C} {g} {g'}
  }





-- Equivalence relations have coequalisers in Std

module coeq-of-eqv-rel-in-Std {A : Std.Obj} (eqr : Std.eqrel-over A) where
  private
    module A = setoid-aux A
    module eqr where
      open Std.eqrel-over eqr public
      module relOb = setoid-aux relOb
      module r₁ = setoidmap r₁
      module r₂ = setoidmap r₂
      module ρ =  setoidmap ρ
      module σ =  setoidmap σ
      module τ =  setoidmap τ
      module τpb = Std.pullback-of-not τpb
    Rel : (a a' : || A ||std) → || eqr.relOb ||std → Set
    Rel a a' p = prod (< A > eqr.r₁.op p ~ a) (< A > eqr.r₂.op p ~ a')
    Ob : setoid {lzero}
    Ob = record
       { object = || A ||std
       ; _∼_ = λ a a' → Σ || eqr.relOb ||std (Rel a a')
       ; istteqrel = record
                   { refl = λ a → eqr.ρ.op a , pair (eqr.ρ-ax₀ a) (eqr.ρ-ax₁ a)
                   ; sym = λ pf → eqr.σ.op (pj1 pf) , pair (eqr.σ-ax₀ (pj1 pf) A.⊙ (prj2 (pj2 pf)))
                                                            (eqr.σ-ax₁ (pj1 pf) A.⊙ (prj1 (pj2 pf)))
                   ; tra = λ pf1 pf2 → Std.tyel (eqr.τ Std.∘ τaux pf1 pf2) , pair (eqr.τ-ax₀g 0₁ A.⊙ prj1 (pj2 pf1))
                                                                               (eqr.τ-ax₁g 0₁ A.⊙ prj2 (pj2 pf2))
                   }
       }
       where --open elementality-in-Std
             glelpf : {x₁ x₂ : || A ||std} (pf : Σ || eqr.relOb ||std (Rel x₁ x₂))
                          → || Std.Hom flStd.trmOb eqr.relOb ||
             glelpf pf = Std.glel (pj1 pf)
             τaux-pf : {x₁ x₂ x₃ : || A ||std} (pf1 : Σ || eqr.relOb ||std (Rel x₁ x₂))
                       (pf2 : Σ || eqr.relOb ||std (Rel x₂ x₃))
                          → eqr.r₂ Std.∘ glelpf pf1 Std.~ eqr.r₁ Std.∘ glelpf pf2
             τaux-pf pf1 pf2 = λ x → prj2 (pj2 pf1) A.⊙ prj1 (pj2 pf2) A.ˢ
             τaux : {x₁ x₂ x₃ : || A ||std} → Σ || eqr.relOb ||std (Rel x₁ x₂)
                        → Σ || eqr.relOb ||std (Rel x₂ x₃)
                          → || Std.Hom flStd.trmOb eqr.τpb.ul ||
             τaux pf1 pf2 = eqr.τpb.⟨ glelpf pf1 , glelpf pf2 ⟩[ τaux-pf pf1 pf2 ]
    qar : || setoidmaps A Ob ||
    qar = record { op = λ x → x
                ; ext = λ {x} pf → (eqr.ρ.op x) , (pair (eqr.ρ-ax₀ x) (eqr.ρ-ax₁ x A.⊙ pf))
                }

    module univ {B : setoid} {f : || setoidmaps A B ||} (eq : f Std.∘ eqr.r₁ Std.~ f Std.∘ eqr.r₂) where
      private
        module B = setoid-aux B
        module f = setoidmap f
      ar : || setoidmaps Ob B ||
      ar = record
        { op = f.op
        ; ext = λ pf → f.ext (prj1 (pj2 pf) A.ˢ) B.⊙ (eq (pj1 pf) B.⊙ f.ext (prj2 (pj2 pf)))
        }
      areq : ar Std.∘ qar Std.~ f
      areq = λ _ → B.r
    -- end univ
  -- end private
  
  coeqof : Std.coeq-of eqr.r₁ eqr.r₂
  coeqof = record
    { Ob = Ob
    ; ar = qar
    ; iscoeq = record
             { eq = λ u → u , (pair A.r A.r)
             ; univ = λ {B} f eq → univ.ar {B} {f} eq
             ; univ-eq = λ {B} {f} eq → univ.areq {B} {f} eq
             ; uniq = record { epi-pf = λ pf x → pf x }
             }
    }
-- end coeq-of-eqv-rel-in-Std


-- Regular epis are isomorphic to canocial ones (constructed in coeq-of-eqv-rel-in-Std)

module can-regular-epi-iso {A B : Std.Obj} {e : || Std.Hom A B ||} (isrepi : Std.is-regular-epi e) where
  open pullback-props Std
  open epi&mono-props-all Std
  private
    module A = setoid-aux A
    module B = setoid-aux B
    module e where
      open setoidmap e public
      open Std.is-regular-epi isrepi public
    kp : Std.pullback-of e e
    kp = flStd.pb-of e e
    module kp where
      open Std.pullback-of-not kp renaming (π/₁ to ₁; π/₂ to ₂) public
      module ₁ = setoidmap ₁
      module ₂ = setoidmap ₂
    e-kp-coeq : Std.is-coeq kp.₁ kp.₂ e
    e-kp-coeq =  repi-is-coeq-of-ker-pair isrepi kp
    module kpcoeq = Std.is-coeq e-kp-coeq
    kp-eqv : Std.is-eq-rel kp.₁ kp.₂
    kp-eqv = is-kp→is-eqr (record { ispbsq = kp.×/ispbsq })
           where open Std.has-pb→ker-are-eqr flStd.haspb
    cancoeq : Std.coeq-of kp.₁ kp.₂
    cancoeq = coeq-of-eqv-rel-in-Std.coeqof (record { iseqrel = kp-eqv })
    module cancoeq where
      open Std.coeq-of cancoeq public
      module Ob = setoid-aux Ob
      module ar = setoidmap ar
    module Q = setoid-aux cancoeq.Ob
  -- end private

  med-ar : || Std.Hom B cancoeq.Ob ||
  med-ar = kpcoeq.univ cancoeq.ar cancoeq.eq
  med-ar⁻¹ : || Std.Hom cancoeq.Ob B ||
  med-ar⁻¹ = cancoeq.univ e kpcoeq.eq
  e∘med~can : med-ar Std.∘ e Std.~ cancoeq.ar
  e∘med~can = λ x → kpcoeq.univ-eq {f = cancoeq.ar} cancoeq.eq x
  can∘med⁻¹~e : med-ar⁻¹ Std.∘ cancoeq.ar Std.~ e
  can∘med⁻¹~e = λ x → cancoeq.univ-eq {f = e} kpcoeq.eq x
  private
    module med where
      open setoidmap med-ar public
      open setoidmap med-ar⁻¹ renaming (op to op⁻¹; ext to ext⁻¹) public
  med-trB : (med-ar⁻¹ Std.∘ med-ar) Std.∘ e Std.~ Std.idar B Std.∘ e
  med-trB = λ x → B.~proof
          med.op⁻¹ (med.op (e.op x))  ~[ med.ext⁻¹ (kpcoeq.univ-eq {f = cancoeq.ar} cancoeq.eq x) ] B./
          med.op⁻¹ (cancoeq.ar.op x)  ~[ cancoeq.univ-eq {f = e} kpcoeq.eq x ]∎
          e.op x ∎
  {-The following requires a lot of implicit argument 
~proof (med-ar⁻¹ Std.∘ med-ar) Std.∘ e ~[ assˢ ⊙ ∘e (kpcoeq.univ-eq cancoeq.eq) (r {f = med-ar⁻¹}) ] /
                   med-ar⁻¹ Std.∘ cancoeq.ar  ~[ lidgenˢ (cancoeq.univ-eq kpcoeq.eq) ]∎
                   Std.idar B Std.∘ e ∎
          where open ecategory-aux Std-}
  med-trQ : (med-ar Std.∘ med-ar⁻¹) Std.∘ cancoeq.ar Std.~ Std.idar cancoeq.Ob Std.∘ cancoeq.ar
  med-trQ = λ x → Q.~proof
          med.op (med.op⁻¹ (cancoeq.ar.op x))  ~[ med.ext (cancoeq.univ-eq {f = e} kpcoeq.eq x) ] Q./
          med.op (e.op x)                      ~[ kpcoeq.univ-eq {f = cancoeq.ar} cancoeq.eq x ]∎
          cancoeq.ar.op x ∎
{-~proof_~[_]_ ((med-ar Std.∘ med-ar⁻¹) Std.∘ cancoeq.ar)
                         {med-ar Std.∘ e} {Std.idar cancoeq.Ob Std.∘ cancoeq.ar}
                         (_⊙_ {f₁ = (med-ar Std.∘ med-ar⁻¹) Std.∘ cancoeq.ar}
                               {med-ar Std.∘ med-ar⁻¹ Std.∘ cancoeq.ar} {med-ar Std.∘ e}
                               (assˢ {f = cancoeq.ar} {med-ar⁻¹} {med-ar})
                               (∘e {f = {!med-ar!}} {{!!}} {{!!}} (cancoeq.univ-eq {f = e} kpcoeq.eq) (r {f = med-ar})))
-}

  med-iso : Std.is-iso-pair med-ar med-ar⁻¹
  med-iso = record
          { iddom = e.epi-pf {g = med-ar⁻¹ Std.∘ med-ar} {Std.idar B} med-trB
          ; idcod = cancoeq.epi-pf {g = med-ar Std.∘ med-ar⁻¹} {Std.idar cancoeq.Ob} med-trQ
          }
-- end can-regular-epi-iso



-- Regular epis are surjective

module regular-epi-is-surjective {A B : Std.Obj} {e : || Std.Hom A B ||} (isrepi : Std.is-regular-epi e) where
  open can-regular-epi-iso isrepi
  private
    module e where
      open setoidmap e public
      open Std.is-regular-epi isrepi public
    module med-iso where
      open setoidmap med-ar public
      open setoidmap med-ar⁻¹ renaming (op to op⁻¹; ext to ext⁻¹) public
      open Std.is-iso-pair med-iso public
    cntimg : || Std.Hom (Freestd N₁) B || → || Std.Hom (Freestd N₁) A ||
    cntimg b = free-std-is-min {A = A} (λ x → med-iso.op (b.op x))
             where module b = setoidmap b
    cntimg-pf : (b : || Std.Hom (Freestd N₁) B ||) → e Std.∘ cntimg b Std.~ b
    cntimg-pf b = λ x → med-iso.iddom (b.op x) 
                where module b = setoidmap b

  issurj : Std.is-surjective e
  issurj = record
         { cntimg = cntimg
         ; cntimg-pf = λ {b} → cntimg-pf b
         }
-- end regular-epi-is-surjective



-- Surjections are regular epic

module surjection-is-regular-epi {A B : Std.Obj} {e : || Std.Hom A B ||} (issurj : Std.is-surjective e) where
  private
    module A = setoid-aux A
    module B = setoid-aux B
    module e where
      open setoidmap e public
      open surjective-Std issurj public
    kp : Std.pullback-of e e
    kp = flStd.pb-of e e
    module kp where
      open Std.pullback-of-not kp renaming (π/₁ to ₁; π/₂ to ₂) public
      module ₁ = setoidmap ₁
      module ₂ = setoidmap ₂
  module univ {C : setoid} {f : || setoidmaps A C ||} (eq : f Std.∘ kp.₁ Std.~ f Std.∘ kp.₂) where
    private
      module C = setoid-aux C
      module f = setoidmap f
    eq-op-aux : {a a' : || A ||std} → < B > e.op a ~ e.op a' → || Std.Hom flStd.trmOb kp.ul ||
    eq-op-aux {a} {a'} pf = kp.⟨ Std.glel a , Std.glel a' ⟩[ (λ _ → pf) ]
    eq-op-aux₁ : {a a' : || A ||std} (pf : < B > e.op a ~ e.op a') → kp.₁ Std.∘ eq-op-aux pf Std.~ Std.glel a
    eq-op-aux₁ pf = kp.×/tr₁ {flStd.trmOb} {Std.glel _} {Std.glel _} (λ _ → pf)
    eq-op-aux₂ : {a a' : || A ||std} (pf : < B > e.op a ~ e.op a') → kp.₂ Std.∘ eq-op-aux pf Std.~ Std.glel a'
    eq-op-aux₂ pf = kp.×/tr₂ {flStd.trmOb} {Std.glel _} {Std.glel _} (λ _ → pf)
    eq-op : {a a' : || A ||std} → < B > e.op a ~ e.op a' → < C > f.op a ~  f.op a'
    eq-op {a} {a'} pf = C.~proof f.op a                                ~[ f.ext ((eq-op-aux₁ pf) 0₁ A.ˢ) ] C./
                                 f.op (kp.₁.op (Std.tyel (eq-op-aux pf)))  ~[ eq (Std.tyel (eq-op-aux pf)) ] C./
                                 f.op (kp.₂.op (Std.tyel (eq-op-aux pf)))  ~[  f.ext ((eq-op-aux₂ pf) 0₁) ]∎
                                 f.op a' ∎
    ext : {b b' : || B ||std} → < B > b ~ b'
             → < C > f.op (Std.tyel (e.cntimg (Std.glel b))) ~ f.op (Std.tyel (e.cntimg (Std.glel b')))
    ext {b} {b'} pf = eq-op (e.cntimg-pf 0₁ B.⊙ (pf B.⊙ e.cntimg-pf 0₁ B.ˢ))
    ar : || Std.Hom B C ||
    ar = record
       { op = λ b → f.op (Std.tyel (e.cntimg (Std.glel b)))
       ; ext = ext
       }
  -- end univ
  isrepi : Std.is-regular-epi e
  isrepi = record
    { relOb = kp.ul
    ; rel₁ = kp.₁
    ; rel₂ = kp.₂
    ; coeq = record
           { eq = kp.×/sqpf
           ; univ = λ f eq → univ.ar {f = f} eq
           ; univ-eq = λ {C} {f} eq a → univ.eq-op {f = f} eq (e.cntimg-pf {Std.glel (e.op a)} 0₁)
           ; uniq = surj-is-epic issurj
           }
    }

-- end surjection-is-regular-epi


-- Surjective functions are the regular epis in Std

issurj→isrepi : {A B : Std.Obj} {e : || Std.Hom A B ||} → Std.is-surjective e → Std.is-regular-epi e
issurj→isrepi = surjection-is-regular-epi.isrepi
isrepi→issurj : {A B : Std.Obj} {e : || Std.Hom A B ||} → Std.is-regular-epi e → Std.is-surjective e
isrepi→issurj = regular-epi-is-surjective.issurj



-- Regular epis are pullback stable

repi-pb-stb : Std.is-pbof-stable Std.is-regular-epi
repi-pb-stb = Std.pbprop.pbof-stb-trsp issurj→isrepi isrepi→issurj surj-pbof-stb
            where open epi&mono-props-all Std
                  open surjective-props flStd.hastrm



-- Equivalence relations are effective

module eqv-rel-is-kernerl-pair {A : Std.Obj} (eqr : Std.eqrel-over A) where
  private
    module A = setoid-aux A
    module eqr where
      open Std.eqrel-over eqr renaming (relOb to Ob) public
      module Ob = setoid-aux Ob
      module r₁ = setoidmap r₁
      module r₂ = setoidmap r₂
      module ρ =  setoidmap ρ
      module σ =  setoidmap σ
      module τ =  setoidmap τ
      module τpb = Std.pullback-of-not τpb
    module q = Std.coeq-of (coeq-of-eqv-rel-in-Std.coeqof eqr)

  module univ {C : Std.Obj} {f g : || Std.Hom C A ||} (eq : q.ar Std.∘ f Std.~ q.ar Std.∘ g) where
    private
      module C = setoid-aux C
      module f = setoidmap f
      module g = setoidmap g
    unext₁ : {X : Set} {k k' : X → || C ||std} (pf : (x : X) → < C > k x ~ k' x)
               → (x : X) → eqr.r₁.op (pj1 (eq (k x))) A.~ eqr.r₁.op (pj1 (eq (k' x)))
    unext₁ {X} {k} {k'} pf x = A.~proof eqr.r₁.op (pj1 (eq (k x)))  ~[ prj1 (pj2 (eq (k x))) ] A./
                                        f.op (k x)                  ~[ f.ext (pf x) ] A./
                                        f.op (k' x)                 ~[ prj1 (pj2 (eq (k' x))) A.ˢ ]∎
                                        eqr.r₁.op (pj1 (eq (k' x))) ∎
    unext₂ : {X : Set} {k k' : X → || C ||std} (pf : (x : X) → < C > k x ~ k' x)
               → (x : X) → eqr.r₂.op (pj1 (eq (k x))) A.~ eqr.r₂.op (pj1 (eq (k' x)))
    unext₂ {X} {k} {k'} pf x = A.~proof eqr.r₂.op (pj1 (eq (k x)))  ~[ prj2 (pj2 (eq (k x))) ] A./
                                        g.op (k x)                  ~[ g.ext (pf x) ] A./
                                        g.op (k' x)                 ~[ prj2 (pj2 (eq (k' x))) A.ˢ ]∎
                                        eqr.r₂.op (pj1 (eq (k' x))) ∎
    unext : {X : Set} {k k' : X → || C ||std} (pf : (x : X) → < C > k x ~ k' x)
               → (x : X) → < eqr.Ob > pj1 (eq (k x)) ~ pj1 (eq (k' x))
    unext {X} {k} {k'} pf = eqr.jm-pf {h = free-std-is-min (λ x → pj1 (eq (k x)))}
                                      {free-std-is-min (λ x → pj1 (eq (k' x)))}
                                      (unext₁ pf)
                                      (unext₂ pf)    
    ar : || Std.Hom C eqr.Ob ||
    ar = record
       { op = λ c → pj1 (eq c)
       ; ext = λ {c} {c'} pf → unext {k = λ _ → c} {λ _ → c'} (λ _ → pf) 0₁
       }
  -- end univ
  
  iskp : Std.is-kernel-pair eqr.r₁ eqr.r₂
  iskp = record
    { Ob = q.Ob
    ; ar = q.ar
    ; sqpf = q.eq
    ; ispbsq = record
             { ⟨_,_⟩[_] = λ h k pf → univ.ar {f = h} {k} pf
             ; ×/tr₁ = λ pf x → prj1 (pj2 (pf x))
             ; ×/tr₂ = λ pf x → prj2 (pj2 (pf x))
             ; ×/uq = λ {C} {h} {h'} pf1 pf2 → eqr.jm-pf {C} {h} {h'} pf1 pf2
             }
    }
-- end eqv-rel-is-kernerl-pair



-- Std is exact

ex-Std : is-exact//has-fin-lim {Std} flim-Std
ex-Std = record
  { repi-pbof-stable = repi-pb-stb
  ; eqr-has-coeq = coeq-of-eqv-rel-in-Std.coeqof
  ; eqr-is-eff = eqv-rel-is-kernerl-pair.iskp
  }
