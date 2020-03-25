
-- disable the K axiom:

{-# OPTIONS --without-K #-}

-- Agda version 2.5.4.1

module ecats.exact-completion.embedding.universal-property.commut where

open import ecats.basic-defs.ecat-def&not
open import ecats.basic-defs.regular-ecat
open import ecats.basic-defs.exact-ecat
open import ecats.basic-props.exact-ecat
open import ecats.finite-limits.defs.collective
open import ecats.constructions.ecat-eqrel
open import ecats.functors.defs.efunctor-d&n
open import ecats.functors.defs.natural-transformation
open import ecats.functors.defs.left-covering
open import ecats.exact-completion.construction
open import ecats.exact-completion.embedding.universal-property.def
open import ecats.exact-completion.embedding.universal-property.eqrel-from-peq




-- Commutativity of the functor Ex ℂ [ hasfwl ] → 𝔼 induced by a left covering ℂ → 𝔼 into 𝔼 exact.

module exact-compl-universal-commut {ℂ : ecategory} (hasfwl : has-fin-weak-limits ℂ) where
  private
    module ℂ = ecategory ℂ
    module Exℂ = ecategory Ex ℂ [ hasfwl ]
    Γex : efunctor ℂ Ex ℂ [ hasfwl ]
    Γex = Γex ℂ [ hasfwl ]
    module Γex = efunctor-aux Γex
  open exact-compl-universal-def hasfwl
  open eqrel-from-peq-funct hasfwl
  
  module ↑ex-commut {𝔼 : ecategory} (𝔼isex : is-exact 𝔼) {F : efunctor ℂ 𝔼} (Flcov : is-left-covering F) where
    private
      module 𝔼 = ecategory 𝔼
      module ex𝔼 = exact-cat-d&p 𝔼isex
      module ER𝔼 = ecategory (EqRel 𝔼)
      module F = efunctor-aux F
      reg𝔼 : is-regular 𝔼
      reg𝔼 = ex𝔼.exact-is-regular
      module F↑ex = efunctor-aux (↑ex 𝔼isex Flcov)
      module F↑exΓex = efunctor-aux (↑ex 𝔼isex Flcov ○ Γex ℂ [ hasfwl ])
      I : efunctor Ex ℂ [ hasfwl ] (EqRel 𝔼)
      I = imgPeq reg𝔼 Flcov
      freesq : natural-iso (I ○ Γex ℂ [ hasfwl ]) (ΔER 𝔼 ○ F)
      freesq = imgPeq-sq reg𝔼 Flcov
      --module I = efunctor-aux I
      module Q = efunctor-aux (QER 𝔼isex)
      module Δ = efunctor-aux (ΔER 𝔼)
      module IΓ≅ΔF = natural-iso freesq
      module QΔ≅Id = natural-iso (ex-retr-EqR 𝔼isex)
      --module FId≅F = natural-iso (○rid {F = F})

{-
    checkf : {A B : Exℂ.Obj} (f : || Exℂ.Hom A B ||) → (Q.ₐ (I.ₐ f)) 𝔼.~ (F↑ex.ₐ f)
    checkf f = r
             where open ecategory-aux-only 𝔼
          
    check2 : (A : Exℂ.Obj) → || 𝔼.Hom (Q.ₒ (I.ₒ A)) (F↑ex.ₒ A) ||
    check2 A = 𝔼.idar (Q.ₒ (I.ₒ A))

    check : (X : ℂ.Obj) → || 𝔼.Hom (Q.ₒ (I.ₒ (Γex.ₒ X))) (F↑ex.ₒ (Γex.ₒ X)) ||
    check X = {!check2 (Γex.ₒ X)!}

    check3 : (A : 𝔼.Obj) → || 𝔼.Hom (Q.ₒ (Δ.ₒ A)) (efunctor.ₒ ((QER 𝔼isex) ○ (ΔER 𝔼)) A) ||
    check3 A = 𝔼.idar (Q.ₒ (Δ.ₒ A))

    check3' : (A : 𝔼.Obj) → (Q.ₒ (Δ.ₒ A)) == (efunctor.ₒ ((QER 𝔼isex) ○ (ΔER 𝔼)) A)
    check3' A = =rf

    check4 : (X : ℂ.Obj) → || ER𝔼.Hom (I.ₒ (Γex.ₒ X)) (efunctor.ₒ (I ○ (Γex ℂ [ hasfwl ])) X) ||
    check4 X = {!ER𝔼.idar (I.ₒ (Γex.ₒ X))!}

    check4' : (X : ℂ.Obj) → (I.ₒ (Γex.ₒ X)) == (efunctor.ₒ (I ○ (Γex ℂ [ hasfwl ])) X)
    check4' X = {!=rf {a = I.ₒ (Γex.ₒ X)}!}

    check5 : (X : ℂ.Obj) → || ER𝔼.Hom (Δ.ₒ (F.ₒ X)) (efunctor.ₒ ((ΔER 𝔼) ○ F) X) ||
    check5 X = ER𝔼.idar (Δ.ₒ (F.ₒ X))
-}
{-
    red-aux : natural-transformation (↑ex 𝔼isex Flcov ○ Γex ℂ [ hasfwl ]) (QER 𝔼isex ○ ΔER 𝔼 ○ F)
    red-aux = record
      { fnc = λ {X} → Q.ₐ (IΓ≅ΔF.fnc {X})
      ; nat = λ {X} {Y} f → Q.∘∘ (IΓ≅ΔF.nat f)
      }
-}

    red : natural-transformation (↑ex 𝔼isex Flcov ○ Γex ℂ [ hasfwl ]) F
    red = record
      { fnc = λ {X} → QΔ≅Id.fnc {F.ₒ X} 𝔼.∘ Q.ₐ (IΓ≅ΔF.fnc {X})
      ; nat = λ {X} {Y} f → ~proof
      (QΔ≅Id.fnc {F.ₒ Y} 𝔼.∘ Q.ₐ (IΓ≅ΔF.fnc {Y})) 𝔼.∘ F↑exΓex.ₐ f     ~[ assˢ ⊙ ∘e (Q.∘∘ (IΓ≅ΔF.nat f)) r ] /
      QΔ≅Id.fnc {F.ₒ Y} 𝔼.∘ Q.ₐ (Δ.ₐ (F.ₐ f)) 𝔼.∘ Q.ₐ (IΓ≅ΔF.fnc {X}) ~[ ass ⊙ ∘e r (QΔ≅Id.nat (F.ₐ f)) ⊙ assˢ ]∎
      F.ₐ f 𝔼.∘ QΔ≅Id.fnc {F.ₒ X} 𝔼.∘ Q.ₐ (IΓ≅ΔF.fnc {X}) ∎
      }
      where open ecategory-aux-only 𝔼

    exp : natural-transformation F (↑ex 𝔼isex Flcov ○ Γex ℂ [ hasfwl ])
    exp = record
      { fnc = λ {X} → Q.ₐ (IΓ≅ΔF.fnc⁻¹ {X}) 𝔼.∘ QΔ≅Id.fnc⁻¹ {F.ₒ X}
      ; nat = λ {X} {Y} f → ~proof
      (Q.ₐ (IΓ≅ΔF.fnc⁻¹ {Y}) 𝔼.∘ QΔ≅Id.fnc⁻¹ {F.ₒ Y}) 𝔼.∘ F.ₐ f           ~[ assˢ ⊙ ∘e (QΔ≅Id.nat⁻¹ (F.ₐ f)) r ] /
      Q.ₐ (IΓ≅ΔF.fnc⁻¹ {Y}) 𝔼.∘ Q.ₐ (Δ.ₐ (F.ₐ f)) 𝔼.∘ QΔ≅Id.fnc⁻¹ {F.ₒ X} ~[ ass ⊙ ∘e r (Q.∘∘ (IΓ≅ΔF.nat⁻¹ f)) ⊙ assˢ ]∎
      F↑exΓex.ₐ f 𝔼.∘ Q.ₐ (IΓ≅ΔF.fnc⁻¹ {X}) 𝔼.∘ QΔ≅Id.fnc⁻¹ {F.ₒ X} ∎
      }
      where open ecategory-aux-only 𝔼

    tr-iso : natural-iso (↑ex 𝔼isex Flcov ○ Γex ℂ [ hasfwl ]) F
    tr-iso = record
           { natt = red
           ; natt⁻¹ = exp
           ; isiso = λ {X} → record
                   { iddom = ~proof
           exp.fnc 𝔼.∘ red.fnc                           ~[ ass ⊙ ∘e r (assˢ ⊙ ridgg r QΔ≅Id.iddom ) ] /
           Q.ₐ (IΓ≅ΔF.fnc⁻¹ {X}) 𝔼.∘ Q.ₐ (IΓ≅ΔF.fnc {X})    ~[ Q.∘ax (IΓ≅ΔF.iddom) ⊙ Q.id ]∎
           𝔼.idar _ ∎
                   ; idcod = ~proof
           red.fnc 𝔼.∘ exp.fnc              ~[ ass ⊙ ∘e r (assˢ ⊙ ridgg r (Q.∘ax (IΓ≅ΔF.idcod) ⊙ Q.id) ) ] /
           QΔ≅Id.fnc {F.ₒ X} 𝔼.∘ QΔ≅Id.fnc⁻¹ {F.ₒ X}        ~[ QΔ≅Id.idcod ]∎
           𝔼.idar (F.ₒ X) ∎
                   }
           }
           where open ecategory-aux-only 𝔼
                 module red = natural-transformation red
                 module exp = natural-transformation exp
                 
    {-assˢ {f = Γex ℂ [ hasfwl ]} {I ex𝔼.exact-is-regular Flcov} {QER 𝔼isex}
             ⊙ ∘e (freesq ex𝔼.exact-is-regular Flcov) (r {f = QER 𝔼isex})
             ⊙ ass {f = F} {ΔER 𝔼} {QER 𝔼isex}
             ⊙ lidgg (r {f = F}) (ex-retr-EqR 𝔼isex)
             where open Large-ecategory-aux-only ECat-}
  -- end ↑ex-commut


  ↑ex-comm : {𝔼 : ecategory} (𝔼isex : is-exact 𝔼)  
              {F : efunctor ℂ 𝔼} (islcov : is-left-covering F)
                → natural-iso (↑ex 𝔼isex islcov ○ Γex ℂ [ hasfwl ]) F
  ↑ex-comm 𝔼isex islcov = tr-iso
                       where open ↑ex-commut 𝔼isex islcov
-- end exact-compl-universal-commut





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
