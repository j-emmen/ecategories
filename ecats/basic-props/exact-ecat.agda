
{-# OPTIONS --without-K #-}

module ecats.basic-props.exact-ecat where

open import ecats.basic-defs.ecat-def&not
open import ecats.basic-defs.arrows
open import ecats.basic-defs.reg&ex
open import ecats.finite-limits.all
--open import ecats.basic-defs.regular-ecat
--open import ecats.basic-defs.exact-ecat
open import ecats.basic-props.epi&mono
open import ecats.basic-props.image-fact
open import ecats.basic-props.regular-ecat



-- Some properties of exact categories

module exact-cat-props-only {𝔼 : ecategory} (isex : is-exact 𝔼) where
  open ecategory 𝔼
  open arrows-defs 𝔼
  open image-fact-defs 𝔼
  open epi&mono-props-all 𝔼
  open image-fact-props 𝔼
  open binary-products 𝔼
  open pullback-squares 𝔼
  open pullback-props 𝔼
  open bow-defs 𝔼
  private
    module ex𝔼 where
      open is-exact isex public
      open has-pullbacks haspb using (pb-of) public
      open has-equalisers haseql using (eql-of) public
      open has-bin-products hasprd using (prd-of) public
      open has-pb→has-kerpair haspb public
      open epi&mono-pullbacks haspb public
      module Q {A : Obj} (eqr : eqrel-over A) = coeq-of (eqr-has-coeq eqr)
    module sp/ = span/
    module sp = span
    module sq/ = square/cosp
    module sq = comm-square
    module pbof = pullback-of
    module pbsq = pb-square
    module ×of = product-of
    module prd = bin-product
    module eqr/ = eqrel-over
    module ker {A B : Obj} (f : || Hom A B ||) = pullback-of-not (ex𝔼.pb-of f f)


  -- Any coequaliser diagram of an equivalence relation is an exact diagram
  
  coeq-of-eqrel-is-eff : {A Q : Obj} {q : || Hom A Q ||} (eqr : eqrel-over A)
                → is-coeq (eqr/.r₁ eqr) (eqr/.r₂ eqr) q
                  → is-exact-seq (eqr/.r₁ eqr) (eqr/.r₂ eqr) q
  coeq-of-eqrel-is-eff eqr coeq = record
    { iscoeq = coeq
    ; iskerpair = kerpair-is-kerpair-of-coeq (ex𝔼.eqr-is-eff eqr) coeq
    }
    

  -- The chosen quotients of equivalence relations are effective,
  -- that is, equivalence relations fit into an exact sequence.
  
  ex-seq : {A : Obj} (eqr : eqrel-over A)
                → is-exact-seq (eqr/.r₁ eqr) (eqr/.r₂ eqr) (ex𝔼.Q.ar eqr)
  ex-seq eqr = coeq-of-eqrel-is-eff eqr (ex𝔼.Q.iscoeq eqr)


  module exact-has-repi-mono-fact {A B : Obj} (f : || Hom A B ||) where
    open has-pb→ker-are-eqr ex𝔼.haspb
    open has-pb→has-kerpair ex𝔼.haspb
    private
      module kerf where
        open is-kernel-pair (π/iskp f) public
        open eqrel-over (π/kp-eqr/ f) public
      module Qf = ex𝔼.Q (π/kp-eqr/ f)
      Obf = Qf.Ob
      Cf : || Hom A Obf ||
      Cf = Qf.ar
      Cf-is-repi : is-regular-epi Cf
      Cf-is-repi = record { coeq = Qf.iscoeq }
      module Cf = is-regular-epi Cf-is-repi
      covObf : reg-cover-of Obf
      covObf = record
             { Ob = A
             ; cov = record { ar = Cf ; is-repi = Cf-is-repi }
             }
      Mf : || Hom Obf B ||
      Mf = Qf.univ f kerf.×/sqpf
      Trf : Mf ∘ Cf ~ f
      Trf = Qf.univ-eq kerf.×/sqpf
      module kerMf = pullback-of-not (ex𝔼.pb-of Mf Mf)
      module ul where
        open pb-of-reg-covers-is-epi-cover-of-pb ex𝔼.haspb ex𝔼.repi-pbof-stable
                                                 kerMf.×/of covObf covObf
                                                 public
        open is-epic diagl-epi public
      Mf-is-monic : is-monic Mf
      Mf-is-monic = π/₁~π/₂→mono kerMf.×/of eqπ/
                  where open ecategory-aux-only 𝔼
                        med-ar-pf  = f ∘ ul.outpb.π/₁ ~[ ∘e r (Trf ˢ) ⊙ ul.outpb.×/sqpf ⊙ ∘e r Trf
                                     ] f ∘ ul.outpb.π/₂
                        med-ar : || Hom ul.outpb.ul kerf.ul ||
                        med-ar = kerf.⟨ ul.outpb.π/₁ , ul.outpb.π/₂ ⟩[ med-ar-pf ]
                        eqπ/ : kerMf.π/₁ ~ kerMf.π/₂
                        eqπ/ = ul.epi-pf (~proof
                             kerMf.π/₁ ∘ ul.diagl       ~[ ass ⊙ ∘e r (ul.lpb.×/sqpf ˢ) ⊙ assˢ ] /
                             Cf ∘ ul.outpb.π/₁            ~[ ∘e (kerf.×/tr₁ med-ar-pf ˢ) r ] /
                             Cf ∘ kerf.π/₁ ∘ med-ar       ~[ ass ⊙ ∘e r Cf.eq ⊙ assˢ ] /
                             Cf ∘ kerf.π/₂ ∘ med-ar       ~[ ∘e (kerf.×/tr₂ med-ar-pf) r ] /
                             Cf ∘ ul.outpb.π/₂            ~[ ass ⊙ ∘e r (ul.upb.×/sqpf ˢ) ⊙ assˢ ] /
                             kerMf.π/₂ ∘ ul.upb.π/₁ ∘ ul.ulpb.π/₂       ~[ ∘e (ul.ulpb.×/sqpf ˢ) r ]∎
                             kerMf.π/₂ ∘ ul.diagl ∎)
    -- end private    
    rmfactof : repi-mono-fact-of f
    rmfactof = record
             { Ob = Obf
             ; M = Mf
             ; C = Cf
             ; tr = Trf
             ; isrem = record
                     { M-is-monic = Mf-is-monic
                     ; C-is-repi = Cf-is-repi
                     }
             }
  -- end exact-has-repi-mono-fact


  --------------------
  -- Exact is regular
  --------------------
  
  is-reg : is-regular 𝔼
  is-reg = record
    { hasfl = ex𝔼.hasfl
    ; hasrmf = record { rmf-of = rmfactof }
    ; repi-pbof-stable = ex𝔼.repi-pbof-stable
    }
    where open exact-has-repi-mono-fact

  --open regular-cat-props exact-is-regular



  -----------------------------------------------------
  -- Exact cat has pullback stable image factorisation
  ----------------------------------------------------


  module exact-has-pbstable-image-fact {A B : Obj} (f : || Hom A B ||) where
    open exact-has-repi-mono-fact f
    private module rmf = repi-mono-fact-of rmfactof
    imgof : img-fact-of f
    imgof = record
      { Ob = rmf.Ob
      ; M = rmf.M
      ; C = rmf.C
      ; isimg  = repi-mono-is-img-fact rmf.tr rmf.C-is-repi rmf.M-is-monic
      }
    private module imgf = img-fact-of imgof


    module imgf-is-pbstable {C : Obj} {g : || Hom C B ||} (g×/f : pullback-of g f) (g×/mf : pullback-of g imgf.M)
                            {pbQ : || Hom (pbof.ul g×/f) (pbof.ul g×/mf) ||} (pbtr : pbof.π/₁ g×/mf ∘ pbQ ~ pbof.π/₁ g×/f)
                            where
      open ecategory-aux-only 𝔼
      module g×/f = pullback-of-not g×/f
      module g×/mf = pullback-of-not g×/mf
      module Mf = is-monic imgf.M-is-monic
      pbQpf₂ = ~proof imgf.M ∘ g×/mf.π/₂ ∘ pbQ        ~[ ass ⊙ ∘e r (g×/mf.×/sqpf ˢ) ⊙ assˢ ] /
                      g ∘  g×/mf.π/₁ ∘ pbQ           ~[ ∘e pbtr r ] /
                      g ∘ pbof.π/₁ g×/f              ~[ g×/f.×/sqpf ⊙ ∘e r (imgf.tr ˢ) ⊙ assˢ ]∎
                      imgf.M ∘ imgf.C ∘ g×/f.π/₂ ∎
      pbQ-is-repi : is-regular-epi pbQ
      pbQ-is-repi = pres-rl (mkpb-sq (upper-is-pbsq imgf.tr pbtr (Mf.mono-pf pbQpf₂)))
                            rmf.C-is-repi
                  where open is-pbsq-stable ex𝔼.repi-pbsq-stable
                        open lower-and-outer-so-upper g×/mf g×/f
      g*imgMf-is-monic : is-monic g×/mf.π/₁
      g*imgMf-is-monic = pbof-mono-is-mono g×/mf imgf.M-is-monic
      pbimg-is-img : is-img-fact pbtr
      pbimg-is-img = repi-mono-is-img-fact pbtr pbQ-is-repi g*imgMf-is-monic
    -- end imgf-is-pbstable

    imgof-is-pb-stb : img-fact-is-pb-stable imgof
    imgof-is-pb-stb = record
      { img-pb-stable = pbimg-is-img
      }
      where open imgf-is-pbstable
  -- end exact-has-pbstable-image-fact


  exact-has-pbstb-img-fact : has-pb-stable-img-fact 𝔼
  exact-has-pbstb-img-fact = record
    { imgfact = record { img-of = imgof }
    ; pb-stb = imgof-is-pb-stb
    }
    where open exact-has-pbstable-image-fact using (imgof; imgof-is-pb-stb)

  exact-is-regular-img : is-regular-img 𝔼
  exact-is-regular-img = record
    { hasfl = ex𝔼.hasfl
    ; pb-stb-imgfact = exact-has-pbstb-img-fact
    --isreg/fl = exact-is-regular//has-fl
    }
-- end exact-cat-props-only


--------------------------------
-- Exact categories are regular
--------------------------------

exact2reg : {𝔼 : ecategory} → is-exact 𝔼 → is-regular 𝔼
exact2reg excat = is-reg
                where open exact-cat-props-only excat using (is-reg)

