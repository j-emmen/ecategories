
-- disable the K axiom:

{-# OPTIONS --without-K #-}

-- Agda version 2.5.4.1

module ecats.exact-completion.CVconstr-is-excompl.embedding.universal-property.commut where

open import ecats.basic-defs.ecat-def&not
open import ecats.basic-defs.regular-ecat
open import ecats.basic-defs.exact-ecat
open import ecats.basic-props.exact-ecat
open import ecats.finite-limits.defs.collective
open import ecats.constructions.ecat-eqrel
open import ecats.functors.defs.efunctor-d&n
open import ecats.functors.defs.natural-transformation
open import ecats.functors.defs.left-covering
open import ecats.exact-completion.CVconstruction
open import ecats.exact-completion.CVconstr-is-excompl.embedding.universal-property.def




-- Commutativity of the functor Ex ℂ [ hasfwl ] → 𝔼 induced by a left covering ℂ → 𝔼 into 𝔼 exact.

module exact-compl-universal-commut {ℂ : ecategory} (hasfwl : has-fin-weak-limits ℂ) where
  private
    module ℂ = ecategory ℂ
    module Exℂ = ecategory Ex ℂ [ hasfwl ]
    CVex : efunctor ℂ Ex ℂ [ hasfwl ]
    CVex = CVex ℂ [ hasfwl ]
    module CVex = efunctor-aux CVex
  open exact-compl-universal-def hasfwl
  
  module ↑ex-commut {𝔼 : ecategory} (𝔼isex : is-exact 𝔼) {F : efunctor ℂ 𝔼} (Flcov : is-left-covering F) where
    private
      module 𝔼 = ecategory 𝔼
      module ex𝔼 = exact-cat-d&p 𝔼isex
      module ER𝔼 = ecategory (EqRel 𝔼)
      module F = efunctor-aux F
      reg𝔼 : is-regular 𝔼
      reg𝔼 = ex𝔼.is-reg
      module F↑ex = efunctor-aux (↑ex 𝔼isex Flcov)
      module F↑exCVex = efunctor-aux (↑ex 𝔼isex Flcov ○ CVex ℂ [ hasfwl ])
      FRel : efunctor Ex ℂ [ hasfwl ] (EqRel 𝔼)
      FRel = Rel reg𝔼 Flcov
      FRel-sq : natural-iso (FRel ○ CVex ℂ [ hasfwl ]) (ΔER 𝔼 ○ F)
      FRel-sq = Rel-sq reg𝔼 Flcov
      module Q = efunctor-aux (QER 𝔼isex)
      module Δ = efunctor-aux (ΔER 𝔼)
      module RΓ≅ΔF = natural-iso FRel-sq
      module QΔ≅Id = natural-iso (ex-retr-EqR 𝔼isex)

    red : natural-transformation (↑ex 𝔼isex Flcov ○ CVex ℂ [ hasfwl ]) F
    red = record
      { fnc = λ {X} → QΔ≅Id.fnc {F.ₒ X} 𝔼.∘ Q.ₐ (RΓ≅ΔF.fnc {X})
      ; nat = λ {X} {Y} f → ~proof
      (QΔ≅Id.fnc {F.ₒ Y} 𝔼.∘ Q.ₐ (RΓ≅ΔF.fnc {Y})) 𝔼.∘ F↑exCVex.ₐ f     ~[ assˢ ⊙ ∘e (Q.∘∘ (RΓ≅ΔF.nat f)) r ] /
      QΔ≅Id.fnc {F.ₒ Y} 𝔼.∘ Q.ₐ (Δ.ₐ (F.ₐ f)) 𝔼.∘ Q.ₐ (RΓ≅ΔF.fnc {X}) ~[ ass ⊙ ∘e r (QΔ≅Id.nat (F.ₐ f)) ⊙ assˢ ]∎
      F.ₐ f 𝔼.∘ QΔ≅Id.fnc {F.ₒ X} 𝔼.∘ Q.ₐ (RΓ≅ΔF.fnc {X}) ∎
      }
      where open ecategory-aux-only 𝔼

    exp : natural-transformation F (↑ex 𝔼isex Flcov ○ CVex ℂ [ hasfwl ])
    exp = record
      { fnc = λ {X} → Q.ₐ (RΓ≅ΔF.fnc⁻¹ {X}) 𝔼.∘ QΔ≅Id.fnc⁻¹ {F.ₒ X}
      ; nat = λ {X} {Y} f → ~proof
      (Q.ₐ (RΓ≅ΔF.fnc⁻¹ {Y}) 𝔼.∘ QΔ≅Id.fnc⁻¹ {F.ₒ Y}) 𝔼.∘ F.ₐ f           ~[ assˢ ⊙ ∘e (QΔ≅Id.nat⁻¹ (F.ₐ f)) r ] /
      Q.ₐ (RΓ≅ΔF.fnc⁻¹ {Y}) 𝔼.∘ Q.ₐ (Δ.ₐ (F.ₐ f)) 𝔼.∘ QΔ≅Id.fnc⁻¹ {F.ₒ X} ~[ ass ⊙ ∘e r (Q.∘∘ (RΓ≅ΔF.nat⁻¹ f)) ⊙ assˢ ]∎
      F↑exCVex.ₐ f 𝔼.∘ Q.ₐ (RΓ≅ΔF.fnc⁻¹ {X}) 𝔼.∘ QΔ≅Id.fnc⁻¹ {F.ₒ X} ∎
      }
      where open ecategory-aux-only 𝔼

    tr-iso : natural-iso (↑ex 𝔼isex Flcov ○ CVex ℂ [ hasfwl ]) F
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

  ↑ex-tr : {𝔼 : ecategory} (𝔼isex : is-exact 𝔼)  
              {F : efunctor ℂ 𝔼} (islcov : is-left-covering F)
                → natural-iso (↑ex 𝔼isex islcov ○ CVex ℂ [ hasfwl ]) F
  ↑ex-tr 𝔼isex islcov = tr-iso
                       where open ↑ex-commut 𝔼isex islcov
-- end exact-compl-universal-commut
