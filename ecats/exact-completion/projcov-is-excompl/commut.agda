
{-# OPTIONS --without-K --show-implicit #-}

module ecats.exact-completion.projcov-is-excompl.commut where

open import ecats.basic-defs.ecat-def&not
open import ecats.basic-defs.regular-ecat
open import ecats.basic-defs.exact-ecat
open import ecats.basic-props.exact-ecat
open import ecats.finite-limits.defs.collective
open import ecats.constructions.ecat-eqrel
open import ecats.functors.defs.efunctor-d&n
open import ecats.functors.defs.basic-defs
open import ecats.functors.defs.natural-transformation
open import ecats.functors.defs.left-covering
open import ecats.functors.defs.projective-cover
open import ecats.functors.props.projective-cover
open import ecats.exact-completion.def
open import ecats.exact-completion.CVconstruction
open import ecats.exact-completion.CVconstr-is-excompl
open import ecats.exact-completion.projcov-is-excompl.def
open import ecats.exact-completion.projcov-is-excompl.eqv-to-CVconstr




-- Commutativity of the functor ↑ex F : 𝔼 → 𝔻 induced by a left covering F : ℙ → 𝔻 into 𝔻 exact.


module exact-compl-universal-comm {𝔼 : ecategory}(ex𝔼 : is-exact 𝔼)
                                  {ℙ : ecategory}(fwlℙ : has-fin-weak-limits ℙ)
                                  {PC : efunctor ℙ 𝔼}(lcovPC : is-left-covering PC)
                                  (pjcPC : is-projective-cover PC)
                                  where  
  private
    module ex𝔼 where
      open is-exact ex𝔼 public
      open exact-cat-props-only ex𝔼 public
    --fwlℙ : has-fin-weak-limits ℙ
    --fwlℙ = proj-cov-has-wlim pjcPC (ex𝔼.hasfl)
    --reg𝔼 : is-regular 𝔼
    --reg𝔼 = ex𝔼.is-reg
    module CVex where
      open efunctor-aux CVex ℙ [ fwlℙ ] public
      open is-exwlex-completion (CVconstr-is-excompl fwlℙ) public
    module PC where
      open efunctor-aux PC public
      open is-projective-cover pjcPC public
      --islcov : is-left-covering PC
      --islcov = pjcov-of-reg-is-lcov reg𝔼 pjcPC
  open exact-compl-universal-def ex𝔼 fwlℙ lcovPC pjcPC
  private
    module ↑PC where
      open efunctor-aux (↑ex ex𝔼 lcovPC) public
      open projcov-of-exact-is-eqv-to-CVconstr ex𝔼 fwlℙ lcovPC pjcPC using (PC↑ex-is-eqv)
      open PC↑ex-is-eqv public

  ↑ex-tr : {𝔻 : ecategory}(ex𝔻 : is-exact 𝔻){F : efunctor ℙ 𝔻}(lcovF : is-left-covering F)
              → F ↑ex[ ex𝔻 , lcovF ] ○ PC ≅ₐ F
  ↑ex-tr {𝔻}ex𝔻 {F} lcovF =
    natiso-vcmp {F = F ↑ex[ ex𝔻 , lcovF ] ○ PC} {↑F.fctr ○ CVex ℙ [ fwlℙ ]} {F}
      ↑F.tr
      ( natiso-vcmp
          --{F = (↑F.fctr ○ ↑PC.inv) ○ PC} {↑F.fctr ○ ↑PC.inv ○ PC} {↑F.fctr ○ CVex ℙ [ fwlℙ ]}
          (natiso-hcmp --{F = ↑PC.inv ○ PC} {CVex ℙ [ fwlℙ ]} {↑F.fctr} {↑F.fctr}
                       (≅ₐrefl {F = ↑F.fctr}) ↑PC.tr-inv)
          (≅ₐsym --{F = ↑F.fctr ○ ↑PC.inv ○ PC} {(↑F.fctr ○ ↑PC.inv) ○ PC}
                 (○ass {F = PC} {↑PC.inv} {↑F.fctr})) )
                            where module ↑F = CVex.unv ex𝔻 lcovF
-- end exact-compl-universal-commut

{-
module exact-compl-universal-commut {ℂ : ecategory} (hasfwl : has-fin-weak-limits ℂ) where
  private
    module ℂ = ecategory ℂ
    module Exℂ = ecategory Ex ℂ [ hasfwl ]
    Γex : efunctor ℂ Ex ℂ [ hasfwl ]
    Γex = Γex ℂ [ hasfwl ]
    module Γex = efunctor-aux Γex
  open exact-compl-universal-def hasfwl
-}

{-
  module ↑ex-commut {𝔻 : ecategory}(ex𝔻 : is-exact 𝔻)
                    {F : efunctor ℙ 𝔻}(Flcov : is-left-covering F)
                    where
    private
      module 𝔻 = ecategory 𝔻
      module ex𝔻 = exact-cat-d&p ex𝔻
      module ER𝔻 = ecategory (EqRel 𝔻)
      module F = efunctor-aux F
      reg𝔻 : is-regular 𝔻
      reg𝔻 = ex𝔻.is-reg
      module F↑ex = efunctor-aux (↑ex ex𝔻 Flcov)
      module F↑exPC = efunctor-aux (↑ex ex𝔻 Flcov ○ PC)
      --FRel : efunctor Ex ℙ [ fwlℙ ] (EqRel 𝔻)
      --FRel = Rel reg𝔻 Flcov
      --FRel-sq : natural-iso (Rel reg𝔻 Flcov ○ CVex ℙ [ fwlℙ ]) (ΔER 𝔻 ○ F)
      --FRel-sq = {!Rel-sq {𝔻} reg𝔻 {F} Flcov!}
      module Q = efunctor-aux (QER ex𝔻)
      module Δ = efunctor-aux (ΔER 𝔻)
      module RΓ≅ΔF = natural-iso (Rel-sq {𝔻} reg𝔻 {F} Flcov)--FRel-sq
      module QΔ≅Id = natural-iso (ex-retr-EqR ex𝔻)

    red : natural-transformation (↑ex 𝔼isex Flcov ○ Γex ℂ [ hasfwl ]) F
    red = record
      { fnc = λ {X} → QΔ≅Id.fnc {F.ₒ X} 𝔼.∘ Q.ₐ (RΓ≅ΔF.fnc {X})
      ; nat = λ {X} {Y} f → ~proof
      (QΔ≅Id.fnc {F.ₒ Y} 𝔼.∘ Q.ₐ (RΓ≅ΔF.fnc {Y})) 𝔼.∘ F↑exΓex.ₐ f     ~[ assˢ ⊙ ∘e (Q.∘∘ (RΓ≅ΔF.nat f)) r ] /
      QΔ≅Id.fnc {F.ₒ Y} 𝔼.∘ Q.ₐ (Δ.ₐ (F.ₐ f)) 𝔼.∘ Q.ₐ (RΓ≅ΔF.fnc {X}) ~[ ass ⊙ ∘e r (QΔ≅Id.nat (F.ₐ f)) ⊙ assˢ ]∎
      F.ₐ f 𝔼.∘ QΔ≅Id.fnc {F.ₒ X} 𝔼.∘ Q.ₐ (RΓ≅ΔF.fnc {X}) ∎
      }
      where open ecategory-aux-only 𝔼

    exp : natural-transformation F (↑ex 𝔼isex Flcov ○ Γex ℂ [ hasfwl ])
    exp = record
      { fnc = λ {X} → Q.ₐ (RΓ≅ΔF.fnc⁻¹ {X}) 𝔼.∘ QΔ≅Id.fnc⁻¹ {F.ₒ X}
      ; nat = λ {X} {Y} f → ~proof
      (Q.ₐ (RΓ≅ΔF.fnc⁻¹ {Y}) 𝔼.∘ QΔ≅Id.fnc⁻¹ {F.ₒ Y}) 𝔼.∘ F.ₐ f           ~[ assˢ ⊙ ∘e (QΔ≅Id.nat⁻¹ (F.ₐ f)) r ] /
      Q.ₐ (RΓ≅ΔF.fnc⁻¹ {Y}) 𝔼.∘ Q.ₐ (Δ.ₐ (F.ₐ f)) 𝔼.∘ QΔ≅Id.fnc⁻¹ {F.ₒ X} ~[ ass ⊙ ∘e r (Q.∘∘ (RΓ≅ΔF.nat⁻¹ f)) ⊙ assˢ ]∎
      F↑exΓex.ₐ f 𝔼.∘ Q.ₐ (RΓ≅ΔF.fnc⁻¹ {X}) 𝔼.∘ QΔ≅Id.fnc⁻¹ {F.ₒ X} ∎
      }
      where open ecategory-aux-only 𝔼

    tr-iso : natural-iso (↑ex 𝔼isex Flcov ○ Γex ℂ [ hasfwl ]) F
    tr-iso = record
           { natt = red
           ; natt⁻¹ = exp
           ; isiso = λ {X} → record
                   { iddom = ~proof
           exp.fnc 𝔼.∘ red.fnc                           ~[ ass ⊙ ∘e r (assˢ ⊙ ridgg r QΔ≅Id.iddom ) ] /
           Q.ₐ (RΓ≅ΔF.fnc⁻¹ {X}) 𝔼.∘ Q.ₐ (RΓ≅ΔF.fnc {X})    ~[ Q.∘ax (RΓ≅ΔF.iddom) ⊙ Q.id ]∎
           𝔼.idar _ ∎
                   ; idcod = ~proof
           red.fnc 𝔼.∘ exp.fnc              ~[ ass ⊙ ∘e r (assˢ ⊙ ridgg r (Q.∘ax (RΓ≅ΔF.idcod) ⊙ Q.id) ) ] /
           QΔ≅Id.fnc {F.ₒ X} 𝔼.∘ QΔ≅Id.fnc⁻¹ {F.ₒ X}        ~[ QΔ≅Id.idcod ]∎
           𝔼.idar (F.ₒ X) ∎
                   }
           }
           where open ecategory-aux-only 𝔼
                 module red = natural-transformation red
                 module exp = natural-transformation exp
  -- end ↑ex-commut
-}





-- -- OLD

-- {-
--     module quot-of-free-peq-is-idar (freepeq : ℂ.Peq) (isfree : ℂ.Peq.%0 freepeq ℂ.~ ℂ.Peq.%1 freepeq) where
--       module free where
--         open ℂ.Peq freepeq public
--         open F↑ex-ob freepeq public
--       imgfree-is-free : free.eqr.r₁ 𝔼.~ free.eqr.r₂
--       imgfree-is-free = epi-pf (~proof free.eqr.r₁ 𝔼.∘ free.img.C         ~[ free.img.imgF%tr₁ ] /
--                                        F.ₐ free.%0                         ~[ F.ext isfree ] /
--                                        F.ₐ free.%1                         ~[ free.img.imgF%tr₂ ˢ ]∎
--                                        free.eqr.r₂ 𝔼.∘ free.img.C ∎)
--                       where open ecategory-aux-only 𝔼
--                             open 𝔼.is-epic (𝔼.repi-is-epic free.img.C-is-repi)
--       idar-coeq : 𝔼.is-coeq free.eqr.r₁ free.eqr.r₂ (𝔼.idar (F.ₒ free.Lo))
--       idar-coeq = record
--         { eq = lidgen (lidgenˢ imgfree-is-free)
--         ; univ = λ f pf → f
--         ; univ-eq = λ {_} {f} pf → rid
--         ; uniq = 𝔼.iso-is-epic (𝔼.idar-is-iso (F.ₒ free.Lo))
--         }
--         where open ecategory-aux-only 𝔼
--       q-is-iso : 𝔼.is-iso free.q.ar
--       q-is-iso = uq-of-coeq-ar-iso free.q.iscoeq
--                  where open 𝔼.uniq-of-coequalisers idar-coeq
--     -- end quot-of-free-peq-is-idar
-- -}

--     module quot-of-canfree-peq-is-idar (X : ℂ.Obj) where
--       module free where
--         open ℂ.Peq (ℂ.freePeq X) public
--         open F↑ex-ob (ℂ.freePeq X) public
--       imgfree-is-free : free.eqr.r₁ 𝔼.~ free.eqr.r₂
--       imgfree-is-free = epi-pf (~proof free.eqr.r₁ 𝔼.∘ free.img.C         ~[ free.img.imgF%tr₁ ] /
--                                        F.ₐ free.%0                         ~[ r ] /
--                                        F.ₐ free.%1                         ~[ free.img.imgF%tr₂ ˢ ]∎
--                                        free.eqr.r₂ 𝔼.∘ free.img.C ∎)
--                       where open ecategory-aux-only 𝔼
--                             open 𝔼.is-epic (𝔼.repi-is-epic free.img.C-is-repi)
--       idar-coeq : 𝔼.is-coeq free.eqr.r₁ free.eqr.r₂ (𝔼.idar (F.ₒ free.Lo))
--       idar-coeq = record
--         { eq = lidgen (lidgenˢ imgfree-is-free)
--         ; univ = λ f pf → f
--         ; univ-eq = λ {_} {f} pf → rid
--         ; uniq = 𝔼.iso-is-epic (𝔼.idar-is-iso (F.ₒ free.Lo))
--         }
--         where open ecategory-aux-only 𝔼
--       q-is-iso : 𝔼.is-iso free.q.ar
--       q-is-iso = uq-of-coeq-ar-iso free.q.iscoeq
--                  where open 𝔼.uniq-of-coequalisers idar-coeq

--       iso : F.ₒ X 𝔼.≅ₒ free.q.Ob -- F↑ex-ob.q.Ob (Γex.ₒ X) --F↑ex.ₒ (Γex.ₒ X)
--       iso = record
--         { a12 = free.q.ar
--         ; a21 = uq-of-coeq-ar⁻¹ free.q.iscoeq
--         ; isop = uq-of-coeq-isopair free.q.iscoeq
--         }
--         where open 𝔼.uniq-of-coequalisers idar-coeq

--     -- end quot-of-canfree-peq-is-idar


--     module qiso (X : ℂ.Obj) where
--       --open 𝔼.is-iso (quot-of-canfree-peq-is-idar.q-is-iso X) public -- (Γex.ₒ X) (ecategory-aux-only.r ℂ)
--       open 𝔼._≅ₒ_ (quot-of-canfree-peq-is-idar.iso X) public
--       open ℂ.Peq (ℂ.freePeq X) public
--       open F↑ex-ob (ℂ.freePeq X) public

--     tr-red : natural-transformation (↑ex 𝔼isex Flcov ○ Γex ℂ [ hasfwl ]) F
--     tr-red = record
--       { fnc = λ {X} → {!qiso.a21 X!}
--       ; nat = {!!}
--       }

--     check : (X : ℂ.Obj) → || 𝔼.Hom (F.ₒ (ℂ.Peq.Lo (Γex.ₒ X))) (F↑ex-ob.q.Ob (ℂ.freePeq X)) ||
--     check X = {!qiso.q.ar X!}

--     tr-exp : natural-transformation F (↑ex 𝔼isex Flcov ○ Γex ℂ [ hasfwl ])
--     tr-exp = record
--       { fnc = λ {X} → {!!} 𝔼.∘ check X
--       ; nat = {!efunctor.ₒ {ℂ} {𝔼} (F.↑ex ○ Γex ℂ [ hasfwl ]) X!}
--       }

-- {-
-- 𝔼.coeq-of.Ob
-- (ex𝔼.eqr-has-coeq {F.FObj X}
--  (F.eqrel-from-peq-via-left-covering.eqrel/ (ℂ.freePeq X)))

-- 𝔼.coeq-of.Ob
-- (ex𝔼.eqr-has-coeq {F.FObj X}
--  (F.eqrel-from-peq-via-left-covering.eqrel/ (ℂ.freePeq X)))
-- -}
