
{-# OPTIONS --without-K #-}

module ecats.exact-completion.projcov-is-excompl.universal-prop where


open import tt-basics.setoids hiding (||_||; _⇒_)
open import tt-basics.id-type
open import ecats.basic-defs.ecat-def&not
open import ecats.basic-defs.all-arrows
open import ecats.basic-props.epi&mono
open import ecats.basic-defs.regular-ecat
open import ecats.basic-defs.exact-ecat
open import ecats.basic-props.exact-ecat
open import ecats.finite-limits.defs.collective
open import ecats.basic-defs.exact-ecat
open import ecats.functors.defs.efunctor-d&n
open import ecats.functors.defs.natural-transformation
open import ecats.functors.defs.basic-defs
open import ecats.functors.defs.left-covering
open import ecats.functors.defs.projective-cover
open import ecats.functors.props.projective-cover
open import ecats.exact-completion.def
open import ecats.exact-completion.CVconstruction
open import ecats.exact-completion.CVconstr-is-excompl
open import ecats.exact-completion.projcov-is-excompl.eqv-to-CVconstr

open import ecats.exact-completion.CVconstr-is-excompl.exact.is-regular
open import ecats.exact-completion.CVconstr-is-excompl.exact.is-exact
open import ecats.exact-completion.CVconstr-is-excompl.embedding.is-projective-cover
open import ecats.exact-completion.CVconstr-is-excompl.embedding.universal-property.def
open import ecats.exact-completion.CVconstr-is-excompl.embedding.universal-property.commut
open import ecats.exact-completion.CVconstr-is-excompl.embedding.universal-property.is-exact-fun
open import ecats.exact-completion.CVconstr-is-excompl.embedding.universal-property.uniqueness


module projcov-universal-prop {𝔼 : ecategory}(ex𝔼 : is-exact 𝔼){ℙ : ecategory}
                              {PC : efunctor ℙ 𝔼}(pjcPC : is-projective-cover PC)
                              where
  private
    module 𝔼 where
      open ecategory 𝔼 public
      open iso-defs 𝔼 public
      open epis&monos-defs 𝔼 public
      open epis&monos-props 𝔼 public
      open kernel-pairs-defs 𝔼 public
      open eq-rel-defs 𝔼 public
      --open finite-limits-d&p 𝔼 public
    module ex𝔼 where
      open exact-cat-d&p ex𝔼 public
      open has-pullbacks haspb using (pb-of) public
    reg𝔼 : is-regular 𝔼
    reg𝔼 = ex𝔼.is-reg
    -- it seems that declaring reg𝔼 explicitly is crucial
    -- for typechecking F↑ex-coeq.Ob A = F↑ex.ₒ A
    module ℙ where
      open ecategory ℙ public
      open pseudo-eq-rel-defs ℙ public
      --open finite-weak-limits-d&p ℙ public
    {-fwlℙ : has-fin-weak-limits ℙ
    fwlℙ = proj-cov-has-wlim pjcPC ex𝔼.hasfl
    module fwlℙ where
      open has-fin-weak-limits fwlℙ public
      open has-weak-pullbacks haswpb using (wpb-of) public-}
    module PC where
      open efunctor-aux PC public
      open is-projective-cover pjcPC public
      islcov : is-left-covering PC
      islcov = pjcov-of-reg-is-lcov reg𝔼 pjcPC

  module univ-prop-aux (fwlℙ : has-fin-weak-limits ℙ)
                       {𝔻 : ecategory} (ex𝔻 : is-exact 𝔻)
                       {G : efunctor ℙ 𝔻}(lcovG : is-left-covering G)
                       where    
    module Exℙ where
      open ecategory Ex ℙ [ fwlℙ ] public
      open iso-defs Ex ℙ [ fwlℙ ] public
      open epis&monos-defs Ex ℙ [ fwlℙ ] public
      open epis&monos-props Ex ℙ [ fwlℙ ] public
      open image-fact-defs Ex ℙ [ fwlℙ ] public
    module CVex where
      open efunctor-aux CVex ℙ [ fwlℙ ] public
      open is-exwlex-completion (CVconstr-is-excompl fwlℙ) public
    {-PC↑ex : efunctor Ex ℙ [ fwlℙ ] 𝔼
    PC↑ex = CVex.unv.fctr ex𝔼 PC.islcov
    PC↑ex-tr : PC↑ex ○ CVex ℙ [ fwlℙ ] ≅ₐ PC
    PC↑ex-tr = CVex.unv.tr ex𝔼 PC.islcov-}
    module PC↑ex where --= efunctor-aux (CVex.fnct ex𝔼 PC.islcov)
      open CVex.unv ex𝔼 PC.islcov public
      open efunctor-aux fctr public
      --tr : fnct ○ CVex ℙ [ fwlℙ ] ≅ₐ PC
      --tr = ∘e {ℙ} {Ex ℙ [ fwlℙ ]} {𝔼} {CVex ℙ [ fwlℙ ]} {CVex ℙ [ fwlℙ ]} {{!fnct!}} {_} r r ⊙ fnct.tr
      --{ℙ} {Ex ℙ [ fwlℙ ]} {𝔼} {CVex ℙ [ fwlℙ ]} {?} {fnct} {?} r ?
           --where open Large-ecategory-aux Cat
      --open fnct public
      {-open exwlex-universal-prop-data (CVex ℙ [ fwlℙ ]) PC
      fnct : efunctor Ex ℙ [ fwlℙ ] 𝔼
      fnct = CVex.unv.fctr ex𝔼 PC.islcov
      tr : fnct ○ CVex ℙ [ fwlℙ ] ≅ₐ PC
      tr = {!CVex.unv.tr {𝔼} ex𝔼 {PC} PC.islcov!}-}
         --where module aux = is-unique-ex+tr (CVex.unv-prop ex𝔼 PC.islcov)
      --open is-unique-ex+tr (CVex.unv-prop ex𝔼 PC.islcov) public
    module Eqv where
      open projcov-of-exact-is-eqv-to-CVconstr ex𝔼 pjcPC
      open is-equivalence PC↑ex-is-eqv renaming (invF to PC↓ex) public
      tr : _○_ {ℙ} {𝔼} {Ex ℙ [ fwlℙ ]} PC↓ex PC ≅ₐ CVex ℙ [ fwlℙ ]
      tr = iso-trcod {f = PC↑ex.fctr} {PC↓ex} {!ι2!} {!ι1!} {CVex ℙ [ fwlℙ ]} {PC} PC↑ex.tr
      {-∘e {ℙ} {𝔼} {Ex ℙ [ fwlℙ ]} {f = PC} {f' = PC↑ex.fctr ○ CVex ℙ [ fwlℙ ]} {g = PC↓ex} {g' = PC↓ex}
              (PC↑ex.tr ˢ) r ⊙ {!ass ⊙ lidgg r ι2!}-}
      -- ∘e (PC↑ex.tr ˢ) r ⊙ ass ⊙ lidgg r ι2
         where open Large-ecategory-aux Cat
               iso-trcod : {a b c : Obj} {f : || Hom a b ||} {f' : || Hom b a ||}
                           (iddom : f' ∘ f ~ idar a)(idcod : f ∘ f' ~ idar b)
                           {g : || Hom c a ||} {h : || Hom c b ||}
                             → f ∘ g ~ h → (f' ∘ h) ≅ₐ g
               iso-trcod {a} {b} {c} {f = f} {f'} iddom idcod {g} {h} pf = ~proof
                 f' ∘ h         ~[ ∘e {f = h} {f ∘ g} {f'} {f'} (pf ˢ) r ] /
                 f' ∘ f ∘ g     ~[ ass {f = g} {f} {f'} ] /
                 (f' ∘ f) ∘ g   ~[ lidgg r iddom ]∎
                 g ∎

      --open Large-ecategory-aux Cat
      {-PC↑ex.fnct ≅ₐ ecats.exact-completion.CVconstr-is-excompl.embedding.universal-prop.exact-compl-universal-prop.↑ex (proj-cov-has-wlim pjcPC ex𝔼.hasfl) ex𝔼 PC.islcov-}
    {-G↑ex : efunctor Ex ℙ [ fwlℙ ] 𝔻
    G↑ex = CVex.unv.fctr ex𝔻 lcovG
    G↑ex-tr : G↑ex ○ CVex ℙ [ fwlℙ ] ≅ₐ G
    G↑ex-tr = {!CVex.unv.tr {𝔻} ex𝔻 {G} lcovG!}-}
    module G↑ex where --= efunctor-aux (CVex.fnct ex𝔼 PC.islcov)
      open CVex.unv ex𝔻 lcovG public
      open efunctor-aux fctr public

{-
      tr' : PC↑ex.fctr ○ CVex ℙ [ fwlℙ ] ≅ₐ PC
      tr' = {!tr!}
          --where open exwlex-universal-prop-data.is-unique-ex+tr (CVex.unv-prop ex𝔼 PC.islcov)
-}

    fnct : efunctor 𝔼 𝔻
    fnct = G↑ex.fctr ○ Eqv.PC↓ex

    tr : fnct ○ PC ≅ₐ G
    tr = {!!} --assˢ ⊙ ∘e Eqv.tr r ⊙ G↑ex.tr
       where open Large-ecategory-aux Cat
       
  -- end univ-prop-aux  

-- end projcov-universal-prop


-- projcov-is-init-lcov-ex : {𝔼 : ecategory}(ex𝔼 : is-exact 𝔼){ℙ : ecategory}
--                           {PC : efunctor ℙ 𝔼}(pjcPC : is-projective-cover PC)
--                           {𝔻 : ecategory} (ex𝔻 : is-exact 𝔻)
--                           {G : efunctor ℙ 𝔻}(lcovG : is-left-covering G)
--   → exwlex-universal-prop-data (proj-cov-has-wlim pjcPC (is-exact.hasfl ex𝔼))
--                                 ex𝔼 (pjcov-of-ex-is-lcov ex𝔼 pjcPC)
--                                 ex𝔻 lcovG
-- projcov-is-init-lcov-ex {𝔼} ex𝔼 {ℙ} {PC} pjcPC {𝔻} ex𝔻 {G} lcovG = record
--   { fnct = fnct
--   ; ex = {!!}
--   ; tr = {!!}
--   ; uq = {!!}
--   }
--   where open projcov-universal-prop ex𝔼 pjcPC ex𝔻 lcovG
