
-- disable the K axiom:

{-# OPTIONS --without-K --show-implicit #-}

-- Agda version 2.5.4.1

module ecats.exact-completion.embedding.universal-property.def where

open import ecats.basic-defs.ecat-def&not
open import ecats.basic-defs.exact-ecat
open import ecats.basic-props.exact-ecat
open import ecats.finite-limits.defs.collective
open import ecats.functors.defs.efunctor-d&n
open import ecats.functors.defs.basic-defs
open import ecats.functors.defs.left-covering
open import ecats.exact-completion.construction
open import ecats.exact-completion.embedding.universal-property.eqrel-from-peq
open import ecats.constructions.ecat-eqrel



-- Definition of the functor Ex ℂ [ hasfwl ] → 𝔼 induced by a left covering ℂ → 𝔼 into 𝔼 exact.

module exact-compl-universal-def {ℂ : ecategory} (hasfwl : has-fin-weak-limits ℂ) where

  ↑ex : {𝔼 : ecategory} (exE : is-exact 𝔼) {F : efunctor ℂ 𝔼} (Flcov : is-left-covering F)
           → efunctor Ex ℂ [ hasfwl ] 𝔼
  ↑ex exE Flcov = QER exE ○ imgPeq exact-is-regular Flcov
                where open eqrel-from-peq-funct hasfwl
                      open exact-cat-props exE using (exact-is-regular)


  syntax ↑ex exE {F} Flcov = F ↑ex[ exE , Flcov ]

-- end exact-compl-universal-def




-- -- previous attempt

-- module exact-compl-universal-def {ℂ : ecategory} (hasfwl : has-fin-weak-limits ℂ) where
--   private
--     module ℂ where
--       open ecategory ℂ public
--       open comm-shapes ℂ public
--       open pseudo-eq-rel-defs ℂ public
--       open finite-weak-limits ℂ public
--       --open can-epi&mono-defs hasfwl public
--     module fwlℂ where
--       open has-fin-weak-limits hasfwl public
--       open has-weak-pullbacks haswpb using (wpb-of) public
--       open has-weak-Wlimits (has-wpb⇒has-wW haswpb) public
--     module Exℂ where
--       open ecategory Ex ℂ [ hasfwl ] public
--       open comm-shapes Ex ℂ [ hasfwl ] public
--       open iso-defs Ex ℂ [ hasfwl ] public
--       open iso-transports Ex ℂ [ hasfwl ] public
--       open epis&monos-defs Ex ℂ [ hasfwl ] public
--       open epis&monos-props Ex ℂ [ hasfwl ] public
--       open image-fact-defs Ex ℂ [ hasfwl ] public
--       open image-fact-props Ex ℂ [ hasfwl ] public
--       open pullback-squares Ex ℂ [ hasfwl ] public
--       open pullback-props Ex ℂ [ hasfwl ] public
--       open projective-defs Ex ℂ [ hasfwl ] public
--     module imgExℂ = exact-compl-has-image-fact hasfwl
--     module imgof {A B : Exℂ.Obj} (f : || Exℂ.Hom A B ||) = Exℂ.img-fact-of (imgExℂ.img-of f)
--     module Γex where
--       open efunctor-aux Γex ℂ [ hasfwl ] public
--       open is-projective-cover (excmpl-embed-is-projective-cover hasfwl) public
--       open projective-cover-props (exact-compl-has-fin-limits hasfwl) (excmpl-embed-is-projective-cover hasfwl) public
--       open is-left-covering (excmpl-embed-is-left-covering hasfwl) public
--       open left-covering-into-exact-props hasfwl (exact-compl-is-exact hasfwl) (excmpl-embed-is-left-covering hasfwl) public

--   module ↑ex-def {𝔼 : ecategory} (𝔼isex : is-exact 𝔼) {F : efunctor ℂ 𝔼} (Flcov : is-left-covering F) where
--     private
--       module 𝔼 where
--         open ecategory 𝔼 public
--         --open comm-shapes 𝔼 public
--         --open iso-defs 𝔼 public
--         --open iso-transports 𝔼 public
--         open epis&monos-defs 𝔼 public
--         open epis&monos-props 𝔼 public
--         open kernel-pairs-defs 𝔼 public
--         open pseudo-eq-rel-defs 𝔼 public
--         open eq-rel-defs 𝔼 public
--         open image-fact-defs 𝔼 public
--         --open image-fact-props 𝔼 public
--         open binary-products 𝔼 public
--         --open pullback-squares 𝔼 public
--         --open pullback-props 𝔼 public
--         open projective-defs 𝔼 public
--       module ex𝔼 where
--         open exact-cat-d&p 𝔼isex public
--         open has-bin-products hasprd using (prd-of) public
--       module F where
--         open efunctor-aux F public
--         open is-left-covering Flcov public
--         open left-covering-into-exact-props hasfwl 𝔼isex Flcov public
    
--     module F↑ex-ob (A : Exℂ.Obj) where
--       private
--         module A = ℂ.Peq A
--         --module aux = F.eqrel-from-peq-via-left-covering A
--       eqr : 𝔼.eqrel-over (F.ₒ A.Lo)
--       eqr = F.eqrel-from-peq-via-left-covering.eqrel/ A
--       module eqr = 𝔼.eqrel-over eqr
--       module img where
--         open F.eqrel-from-peq-via-left-covering.imgF% A public
--         open F.eqrel-from-peq-via-left-covering A hiding (eqrel/) public
--       --module exs = 𝔼.is-exact-seq (ex𝔼.ex-seq aux.eqrel/) using (iscoeq; iskerpair)
--       q : 𝔼.coeq-of eqr.r₁ eqr.r₂
--       q = ex𝔼.eqr-has-coeq eqr
--       module q = 𝔼.coeq-of q
--       q-is-repi : 𝔼.is-regular-epi q.ar
--       q-is-repi = record { coeq = q.iscoeq }
--       module qq = 𝔼.is-coeq (𝔼.epi/coeq-so-coeq (𝔼.repi-is-epic img.C-is-repi)
--                                                   img.imgF%tr₁
--                                                   img.imgF%tr₂
--                                                   q.iscoeq)
--       --ob : 𝔼.Obj
--       --ob = q.Ob
--     -- end F↑ex-ob
      
--     module F↑ex-ar {A B : Exℂ.Obj} (f : || Exℂ.Hom A B ||) where
--       private
--         module A where
--           open ℂ.Peq A public
--           open F↑ex-ob A public
--         module B where
--           open ℂ.Peq B public
--           open F↑ex-ob B public
--         module f = ℂ.Peq-mor f      
--       pf : (B.q.ar 𝔼.∘ F.ₐ f.lo) 𝔼.∘ A.eqr.r₁ 𝔼.~ (B.q.ar 𝔼.∘ F.ₐ f.lo) 𝔼.∘ A.eqr.r₂
--       pf = epi-pf (~proof
--         ((B.q.ar 𝔼.∘ F.ₐ f.lo) 𝔼.∘ A.eqr.r₁) 𝔼.∘ IA.C     ~[ assˢ ⊙ ∘e IA.imgF%tr₁ r ] /
--         (B.q.ar 𝔼.∘ F.ₐ f.lo) 𝔼.∘ F.ₐ A.%0                 ~[ assˢ ⊙ ∘e (F.∘∘ f.cmptb₀ ˢ) r ] /
--         B.q.ar 𝔼.∘ F.ₐ B.%0 𝔼.∘ F.ₐ f.hi                   ~[ ass ⊙ ∘e r B.qq.eq ⊙ assˢ ] /
--         B.q.ar 𝔼.∘ F.ₐ B.%1 𝔼.∘ F.ₐ f.hi                   ~[ ∘e (F.∘∘ f.cmptb₁) r ⊙ ass ] /
--         (B.q.ar 𝔼.∘ F.ₐ f.lo) 𝔼.∘ F.ₐ A.%1                 ~[ ∘e (IA.imgF%tr₂ ˢ) r ⊙ ass ]∎
--         ((B.q.ar 𝔼.∘ F.ₐ f.lo) 𝔼.∘ A.eqr.r₂) 𝔼.∘ IA.C ∎)
--             where open ecategory-aux-only 𝔼
--                   module IA = A.img
--                   open 𝔼.is-regular-epi A.img.C-is-repi using (epi-pf)
--       ar : || 𝔼.Hom A.q.Ob B.q.Ob ||
--       ar = A.q.univ (B.q.ar 𝔼.∘ F.ₐ f.lo) pf
--       sq : ar 𝔼.∘ A.q.ar 𝔼.~ B.q.ar 𝔼.∘ F.ₐ f.lo
--       sq = A.q.univ-eq pf
--     -- end F↑ex-ar

--     module F↑ex-ext {A B : Exℂ.Obj} {f f' : || Exℂ.Hom A B ||} (pf : f Exℂ.~ f') where
--       private
--         module A where
--           open ℂ.Peq A public
--           open F↑ex-ob A public
--         module B where
--           open ℂ.Peq B public
--           open F↑ex-ob B public
--         module f where
--           open ℂ.Peq-mor f public
--           open F↑ex-ar f public
--         module f' where
--           open ℂ.Peq-mor f' public
--           open F↑ex-ar f' public
--         module pf = ℂ.Peq-mor-eq pf
--       extax : f.ar 𝔼.~ f'.ar
--       extax = epi-pf (~proof
--           f.ar 𝔼.∘ A.q.ar                         ~[ f.sq ] /
--           B.q.ar 𝔼.∘ F.ₐ f.lo                     ~[ ∘e (F.∘axˢ pf.hty₀) r ] /
--           B.q.ar 𝔼.∘  F.ₐ B.%0 𝔼.∘ F.ₐ pf.hty     ~[ ass ⊙ ∘e r B.qq.eq ⊙ assˢ ] /
--           B.q.ar 𝔼.∘  F.ₐ B.%1 𝔼.∘ F.ₐ pf.hty     ~[ ∘e (F.∘ax pf.hty₁) r ] /
--           B.q.ar 𝔼.∘ F.ₐ f'.lo                    ~[ f'.sq ˢ ]∎
--           f'.ar 𝔼.∘ A.q.ar ∎)
--           where open ecategory-aux-only 𝔼
--                 open 𝔼.is-regular-epi A.q-is-repi using (epi-pf)
--     -- end F↑ex-ext

--     module F↑ex-id (A : Exℂ.Obj) where
--       private
--         module A where
--           open ℂ.Peq A public
--           open F↑ex-ob A public
--         module idA where
--           open ℂ.Peq-mor (Exℂ.idar A) public
--           open F↑ex-ar (Exℂ.idar A) public
--       idax : idA.ar 𝔼.~ 𝔼.idar A.q.Ob
--       idax = epi-pf (lidgenˢ (idA.sq ⊙ ridgg r F.id))
--            where open ecategory-aux-only 𝔼
--                  open 𝔼.is-regular-epi A.q-is-repi using (epi-pf)
--     -- end F↑ex-id

--     module F↑ex-cmp {A B C : Exℂ.Obj} (f : || Exℂ.Hom A B ||) (g : || Exℂ.Hom B C ||) where
--       private
--         module A where
--           open ℂ.Peq A public
--           open F↑ex-ob A public
--         module B where
--           open ℂ.Peq B public
--           open F↑ex-ob B public
--         module C where
--           open ℂ.Peq C public
--           open F↑ex-ob C public
--         module f where
--           open ℂ.Peq-mor f public
--           open F↑ex-ar f public
--         module g where
--           open ℂ.Peq-mor g public
--           open F↑ex-ar g public
--         module gf where
--           open ℂ.Peq-mor (g Exℂ.∘ f) public
--           open F↑ex-ar (g Exℂ.∘ f) public
--       cmpax : g.ar 𝔼.∘ f.ar 𝔼.~ gf.ar 
--       cmpax = epi-pf (~proof
--         (g.ar 𝔼.∘ f.ar) 𝔼.∘ A.q.ar            ~[ assˢ ⊙ ∘e f.sq r ] /
--         g.ar 𝔼.∘ B.q.ar 𝔼.∘ F.ₐ f.lo          ~[ ass ⊙ ∘e r g.sq ⊙ assˢ ] /
--         C.q.ar 𝔼.∘ F.ₐ g.lo 𝔼.∘ F.ₐ f.lo      ~[ ∘e F.∘ax-rf r ⊙ gf.sq ˢ ]∎
--         gf.ar 𝔼.∘ A.q.ar ∎)
--             where open ecategory-aux-only 𝔼
--                   open 𝔼.is-regular-epi A.q-is-repi using (epi-pf)
--     -- end F↑ex-cmp


--     open efunctor-defs Ex ℂ [ hasfwl ] 𝔼
    
--     F↑ex-is-functorial : is-functorial {F↑ex-ob.q.Ob} F↑ex-ar.ar
--     F↑ex-is-functorial = record
--       { ext = F↑ex-ext.extax
--       ; id = λ {A} → F↑ex-id.idax A
--       ; cmp = F↑ex-cmp.cmpax
--       }

--     F↑ex : efunctor Ex ℂ [ hasfwl ] 𝔼
--     F↑ex = record
--       { FObj = λ A → F↑ex-ob.q.Ob A
--       ; FHom = F↑ex-ar.ar
--       ; isF = F↑ex-is-functorial
--       }
--   -- end ↑ex-def
  

--   ↑ex : {𝔼 : ecategory} (exE : is-exact 𝔼) {F : efunctor ℂ 𝔼} (Flcov : is-left-covering F)
--            → efunctor Ex ℂ [ hasfwl ] 𝔼
--   ↑ex exE Flcov = F↑ex
--                 where open ↑ex-def exE Flcov


--   syntax ↑ex exE {F} Flcov = F ↑ex[ exE , Flcov ]

-- -- end exact-compl-universal-def







-- {-
--     module F↑ex-idg {A : Exℂ.Obj} {f : || Exℂ.Hom A A ||} (pf : f Exℂ.~ Exℂ.idar A)
--                     --{g : || 𝔼.Hom (F↑ex-ob.q.Ob A) (F↑ex-ob.q.Ob A) ||} (↑pf : g 𝔼.~ 𝔼.idar (F↑ex-ob.q.Ob A))
--                     where
--       private
--         module A where
--           open ℂ.Peq A public
--           open F↑ex-ob A public
--         module f where
--           open ℂ.Peq-mor f public
--           open F↑ex-ar f public
--         module pf = ℂ.Peq-mor-eq pf
--       idaxg : f.ar 𝔼.~ 𝔼.idar A.q.Ob
--       idaxg = epi-pf (~proof f.ar 𝔼.∘ A.q.ar                      ~[ f.sq ] /
--                              A.q.ar 𝔼.∘ F.ₐ f.lo                  ~[ ∘e (F.∘axˢ pf.hty₀) r ] /
--                              A.q.ar 𝔼.∘ F.ₐ A.%0 𝔼.∘ F.ₐ pf.hty   ~[ ass ⊙ ∘e r A.qq.eq ⊙ assˢ ] /
--                              A.q.ar 𝔼.∘ F.ₐ A.%1 𝔼.∘ F.ₐ pf.hty   ~[ ridgg lidˢ (F.∘ax pf.hty₁ ⊙ F.id) ]∎
--                              𝔼.idar A.q.Ob 𝔼.∘ A.q.ar ∎)
--            where open ecategory-aux-only 𝔼
--                  open 𝔼.is-regular-epi A.q-is-repi using (epi-pf)
--     -- end F↑ex-id
-- -}

-- {-
--     private
--       record F↑ex-ar-data {A B : Exℂ.Obj} (f : || Exℂ.Hom A B ||) : Set₀ where
--         private
--           module A = F↑ex-ob A
--           module B = F↑ex-ob B
--           module f = ℂ.Peq-mor f
--         field
--           pf : (B.q.ar 𝔼.∘ F.ₐ f.lo) 𝔼.∘ A.eqr.r₁ 𝔼.~ (B.q.ar 𝔼.∘ F.ₐ f.lo) 𝔼.∘ A.eqr.r₂
--           ar : || 𝔼.Hom A.ob B.ob ||
--           --ar = A.q.univ (B.q.ar 𝔼.∘ F.ₐ f.lo) ar-pf
--           sq : ar 𝔼.∘ A.q.ar 𝔼.~ B.q.ar 𝔼.∘ F.ₐ f.lo
--           --sq = A.q.univ-eq ar-pf
-- -}

-- {-
--     F↑ex-ar-aux : {A B : Exℂ.Obj} (f : || Exℂ.Hom A B ||) → F↑ex-ar-coll f
--     F↑ex-ar-aux f = record { }
--     module F↑ex-ar {A B : Exℂ.Obj} (f : || Exℂ.Hom A B ||) = F↑ex-ar-coll (F↑ex-ar-aux f)
-- -}
-- {-
--     F↑ex-ar-d : {A B : Exℂ.Obj} (f : || Exℂ.Hom A B ||) → F↑ex-ar-data f
--     F↑ex-ar-d {A} {B} f = record
--       { pf = ↑pf --F↑ex-ar.ar-pf
--       ; ar = ↑ar --A.q.univ (B.q.ar 𝔼.∘ F.ₐ f.lo) ar-pf
--       ; sq = ↑sq --F↑ex-ar.sq --A.q.univ-eq ar-pf
--       }
--       where --open F↑ex-ar f
--             open ecategory-aux-only 𝔼
--             module A where
--               open ℂ.Peq A public
--               open F↑ex-ob A public
--             module IA = A.img
--             module ACrepi = 𝔼.is-regular-epi IA.C-is-repi using (epi-pf)
--             module B where
--               open ℂ.Peq B public
--               open F↑ex-ob B public
--             module f = ℂ.Peq-mor f
--             private
--               ↑pf : (B.q.ar 𝔼.∘ F.ₐ f.lo) 𝔼.∘ A.eqr.r₁ 𝔼.~ (B.q.ar 𝔼.∘ F.ₐ f.lo) 𝔼.∘ A.eqr.r₂
--               ↑pf = ACrepi.epi-pf (~proof
--                 ((B.q.ar 𝔼.∘ F.ₐ f.lo) 𝔼.∘ A.eqr.r₁) 𝔼.∘ IA.C     ~[ assˢ ⊙ ∘e IA.imgF%tr₁ r ] /
--                 (B.q.ar 𝔼.∘ F.ₐ f.lo) 𝔼.∘ F.ₐ A.%0                 ~[ assˢ ⊙ ∘e (F.∘∘ f.cmptb₀ ˢ) r ] /
--                 B.q.ar 𝔼.∘ F.ₐ B.%0 𝔼.∘ F.ₐ f.hi                   ~[ ass ⊙ ∘e r B.qq.eq ⊙ assˢ ] /
--                 B.q.ar 𝔼.∘ F.ₐ B.%1 𝔼.∘ F.ₐ f.hi                   ~[ ∘e (F.∘∘ f.cmptb₁) r ⊙ ass ] /
--                 (B.q.ar 𝔼.∘ F.ₐ f.lo) 𝔼.∘ F.ₐ A.%1                 ~[ ∘e (IA.imgF%tr₂ ˢ) r ⊙ ass ]∎
--                 ((B.q.ar 𝔼.∘ F.ₐ f.lo) 𝔼.∘ A.eqr.r₂) 𝔼.∘ IA.C ∎)
--               ↑ar : || 𝔼.Hom A.ob B.ob ||
--               ↑ar = A.q.univ (B.q.ar 𝔼.∘ F.ₐ f.lo) ↑pf
--               ↑sq : ↑ar 𝔼.∘ A.q.ar 𝔼.~ B.q.ar 𝔼.∘ F.ₐ f.lo
--               ↑sq = A.q.univ-eq ↑pf      
--     module F↑ex-ard {A B : Exℂ.Obj} (f : || Exℂ.Hom A B ||) = F↑ex-ar-data (F↑ex-ar-d f)
-- -}

-- {-
--     check : {A B : Exℂ.Obj} (f : || Exℂ.Hom A B ||)
--                → F↑ex-ar.ar f 𝔼.~ F↑ex-ob.q.univ A (F↑ex-ob.q.ar B 𝔼.∘ F.ₐ (ℂ.Peq-mor.lo f)) (F↑ex-ar.pf f)
--     check {A} {B} f = r
--             where open ecategory-aux-only 𝔼

--     checkid : {A : Exℂ.Obj}
--                → F↑ex-ar.ar (Exℂ.idar A)
--                             𝔼.~ F↑ex-ob.q.univ A (F↑ex-ob.q.ar A 𝔼.∘ F.ₐ (ℂ.Peq-mor.lo (Exℂ.idar A)))
--                                                   (F↑ex-ar.pf (Exℂ.idar A))
--     checkid {A} = r
--             where open ecategory-aux-only 𝔼
-- -}

    
  
-- {-
--     F↑ex-ar : {A B : Exℂ.Obj} → || Exℂ.Hom A B || → || 𝔼.Hom (F↑ex-ob.q.Ob A) (F↑ex-ob.q.Ob B) ||
--     F↑ex-ar = F↑ex-ar.ar
--     F↑ex-arsq : {A B : Exℂ.Obj} (f : || Exℂ.Hom A B ||)
--                    → F↑ex-ar f 𝔼.∘ F↑ex-ob.q.ar A 𝔼.~ F↑ex-ob.q.ar B 𝔼.∘ F.ₐ (ℂ.Peq-mor.lo f)
--     F↑ex-arsq = F↑ex-ar.sq
-- -}
