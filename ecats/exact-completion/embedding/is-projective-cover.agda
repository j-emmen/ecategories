
-- disable the K axiom:

{-# OPTIONS --without-K #-}

-- Agda version 2.5.4.1

module ecats.exact-completion.embedding.is-projective-cover where

open import ecats.basic-defs.ecat-def&not
open import ecats.basic-defs.all-arrows
open import ecats.basic-props.epi&mono
open import ecats.basic-props.image-fact
open import ecats.basic-defs.regular-ecat
open import ecats.basic-props.regular-ecat
open import ecats.basic-defs.exact-ecat
open import ecats.finite-limits.all
open import ecats.exact-completion.construction
open import ecats.exact-completion.finite-limits.fin-limits
open import ecats.exact-completion.finite-limits.pullback
open import ecats.exact-completion.exact.canonical-epi&mono
open import ecats.exact-completion.exact.is-regular
open import ecats.exact-completion.exact.is-exact
open import ecats.functors.defs.efunctor-d&n
open import ecats.functors.defs.basic-defs
open import ecats.functors.defs.projective-cover
open import ecats.functors.props.projective-cover
open import ecats.functors.defs.left-covering
open import ecats.functors.props.left-covering



---------------------------------------------
-- The embedding Γex is a projective cover --
---------------------------------------------

module exact-compl-embed-is-prjcov {ℂ : ecategory} (hasfwl : has-fin-weak-limits ℂ) where
  private
    module ℂ where
      open ecategory ℂ public
      open comm-shapes ℂ public
      open pseudo-eq-rel-defs ℂ public
      open finite-weak-limits ℂ public
      open can-epi&mono-defs hasfwl public
    module fwlℂ where
      open has-fin-weak-limits hasfwl public
      open has-weak-pullbacks haswpb using (wpb-of) public
      open has-weak-Wlimits (has-wpb⇒has-wW haswpb) public
    module Exℂ where
      open ecategory Ex ℂ [ hasfwl ] public
      open comm-shapes Ex ℂ [ hasfwl ] public
      open iso-defs Ex ℂ [ hasfwl ] public
      open iso-transports Ex ℂ [ hasfwl ] public
      open epis&monos-defs Ex ℂ [ hasfwl ] public
      open epis&monos-props Ex ℂ [ hasfwl ] public
      open image-fact-defs Ex ℂ [ hasfwl ] public
      open image-fact-props Ex ℂ [ hasfwl ] public
      open pullback-squares Ex ℂ [ hasfwl ] public
      open pullback-props Ex ℂ [ hasfwl ] public
      open projective-defs Ex ℂ [ hasfwl ] public
    module imgExℂ = exact-compl-has-image-fact hasfwl
    module imgof {A B : Exℂ.Obj} (f : || Exℂ.Hom A B ||) = Exℂ.img-fact-of (imgExℂ.img-of f)
    module Γex = efunctor-aux Γex ℂ [ hasfwl ]
  

  Γex-faith : is-faithful Γex ℂ [ hasfwl ]
  Γex-faith = record
    { faith-pf = λ pf → hty₀ pf ˢ ⊙ hty₁ pf
    }
    where open ecategory-aux-only ℂ
          open ℂ.Peq-mor-eq
  open is-faithful Γex-faith


  Γex-full : is-full Γex ℂ [ hasfwl ]
  Γex-full = record
    { full-ar = λ f → lo f
    ; full-pf = λ {_} {_} {f} → record { hty = lo f ; hty₀ = lid ; hty₁ = lid }
    }
    where open ecategory-aux-only ℂ
          open ℂ.Peq-mor
  open is-full Γex-full



  module Γex-img-crepi-projective {Y : ℂ.Obj} {R S : ℂ.PeqOver Y} (crepi : ℂ.canonical-repi R S)
                                  {X : ℂ.Obj} (f : || Exℂ.Hom (Γex.ₒ X) (ℂ.mkpeq-c S) ||)
                                  where
    private
      module R = ℂ.PeqOver R
      module S = ℂ.PeqOver S
      module cr = ℂ.canonical-repi crepi
      module f = ℂ.Peq-mor f
    lift-crepi : || Exℂ.Hom (Γex.ₒ X) (ℂ.mkpeq-c R) ||
    lift-crepi = record { lo = f.lo
                        ; isext = record
                          { hi = R.ρ ℂ.∘ f.lo
                          ; cmptb₀ = ass ⊙ lidgg ridˢ R.ρ-ax₀
                          ; cmptb₁ = ass ⊙ lidgg ridˢ R.ρ-ax₁
                          }
                        }
                        where open ecategory-aux-only ℂ
    lift-crepi-tr : cr.can-repi Exℂ.∘ lift-crepi Exℂ.~ f
    lift-crepi-tr = record { hty = S.ρ ℂ.∘ f.lo
                           ; hty₀ = ass ⊙ lidgg lidˢ S.ρ-ax₀
                           ; hty₁ = ass ⊙ lidgg r S.ρ-ax₁
                           }
                           where open ecategory-aux-only ℂ
  -- end Γex-img-crepi-projective


  Γex-img-proj : (X : ℂ.Obj) → Exℂ.is-reg-projective (Γex.ₒ X)
  Γex-img-proj X = record
    { lift = cr.lift-crepi
    ; lift-tr = λ {A} {B} {f} {repi} {g} → lift-tr repi g
    }
    where imgMf-iso : {A B : Exℂ.Obj} {f : || Exℂ.Hom A B ||} (repi : Exℂ.is-regular-epi f)
                      → Exℂ.is-iso (imgof.M f)
          imgMf-iso {f = f} repi = cov-pf (imgof.tr f) (imgof.M-is-monic f)
                             where open Exℂ.is-cover (Exℂ.repi-is-cover repi)
          module Mf {A B : Exℂ.Obj} {f : || Exℂ.Hom A B ||} (repi : Exℂ.is-regular-epi f)
                    = Exℂ.is-iso (imgMf-iso repi)
          module cr {A B : Exℂ.Obj} {f : || Exℂ.Hom A B ||} (repi : Exℂ.is-regular-epi f)
                    (g : || Exℂ.Hom (Γex.ₒ X) B ||)
                    = Γex-img-crepi-projective (imgExℂ.imgC-is-can-repi f) (Mf.⁻¹ repi Exℂ.∘ g)
          lift-tr : {A B : Exℂ.Obj} {f : || Exℂ.Hom A B ||} (repi : Exℂ.is-regular-epi f)
                    (g : || Exℂ.Hom (Γex.ₒ X) B ||) → f Exℂ.∘ cr.lift-crepi repi g Exℂ.~ g
          lift-tr {f = f} repi g = ~proof
            f Exℂ.∘ cr.lift-crepi repi g                         ~[ ∘e r (imgof.tr f ˢ) ⊙ assˢ {g = imgof.C f} ] /
            imgof.M f Exℂ.∘ imgof.C f Exℂ.∘ cr.lift-crepi repi g     ~[ ∘e (cr.lift-crepi-tr repi g) r ] /
            imgof.M f Exℂ.∘ Mf.⁻¹ repi Exℂ.∘ g                   ~[ ass {g = Mf.⁻¹ repi} ⊙ lidgg r (Mf.idcod repi) ]∎
                                          g ∎
                                 where open ecategory-aux-only Ex ℂ [ hasfwl ]



  Γex-proj-cov : is-projective-cover Γex ℂ [ hasfwl ]
  Γex-proj-cov = record
                   { isfull = Γex-full
                   ; isfaith = Γex-faith
                   ; img-proj = Γex-img-proj
                   ; reg-cover-obj = λ A → Lo A
                   ; reg-cover-ar = λ A → crepiPeq.can-repi A
                   ; reg-cover-is-repi = λ A → crepiPeq.can-repi-is-repi A
                   }
                   where open ℂ.Peq
                         crepiPeq : (A : Exℂ.Obj)
                                       → ℂ.canonical-repi (peqover (Γex.ₒ (Lo A))) (peqover A)
                         crepiPeq A = record { crepi-hi = ρ A
                                             ; crepi-ax₀ = ρ-ax₀ A 
                                             ; crepi-ax₁ = ρ-ax₁ A
                                             }
                         module crepiPeq (A : Exℂ.Obj) = ℂ.canonical-repi (crepiPeq A)

-- end exact-compl-embed-is-prjcov



excmpl-embed-is-projective-cover : {ℂ : ecategory} (hasfwl : has-fin-weak-limits ℂ)
                                      → is-projective-cover Γex ℂ [ hasfwl ]
excmpl-embed-is-projective-cover hasfwl = Γex-proj-cov
                                        where open exact-compl-embed-is-prjcov hasfwl

excmpl-embed-is-left-covering : {ℂ : ecategory} (hasfwl : has-fin-weak-limits ℂ)
                                   → is-left-covering Γex ℂ [ hasfwl ]
excmpl-embed-is-left-covering hasfwl = proj-cover-is-left-covering (exact-compl-is-regular hasfwl)
                                                                   (excmpl-embed-is-projective-cover hasfwl)


