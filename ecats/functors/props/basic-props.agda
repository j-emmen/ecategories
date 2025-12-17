
{-# OPTIONS --without-K #-}

module ecats.functors.props.basic-props where

open import ecats.basic-defs.ecat-def&not
open import ecats.basic-defs.arrows
open import ecats.basic-props.epi&mono-basic
open import ecats.basic-props.isomorphism
open import ecats.finite-limits.all
open import ecats.functors.defs.efunctor-d&n
open import ecats.functors.defs.natural-transformation
open import ecats.functors.defs.natural-iso
open import ecats.functors.defs.basic-defs
open import ecats.functors.defs.preserving-functor
open import ecats.functors.props.efunctor


module efunctor-basic-props {ℂ 𝔻 : ecategory} (F : efunctor ℂ 𝔻) where
  private
    module macros (𝕏 : ecategory) where
        open ecategory-aux 𝕏 public
        open arrows-defs 𝕏 public
        open iso-props 𝕏 public
        open finite-limits 𝕏 public
        open finite-weak-limits 𝕏 public
    module ℂ = macros ℂ
    module 𝔻 = macros 𝔻
    module F where
      open efunctor-aux F public
      open efunctor-lev-props F public

  Fpres-iso : {A B : ℂ.Obj} {f : || ℂ.Hom A B ||}
                 → ℂ.is-iso f → 𝔻.is-iso (F.ₐ f)
  Fpres-iso isof = record
    { invf = F.ₐ invf
    ; isisopair = F.ᵢₛₒ isisopair
    }
    where open ℂ.is-iso isof

{- these two are in natural-transformation.agda
  Fpres-natt : {𝔹 : ecategory}{H K : efunctor 𝔹 ℂ}(α : natural-transformation H K)
                  → natural-transformation (F ○ H) (F ○ K)
  Fpres-natt {𝔹} {H} {K} α = record
    { fnc = λ {B} → F.ₐ (α.fnc {B})
    ; nat = λ f → F.∘∘ (α.nat f)
    }
    where module α = natural-transformation α

  Fridx-natt : {𝔼 : ecategory}{H K : efunctor 𝔻 𝔼}(α : natural-transformation H K)
                  → natural-transformation (H ○ F) (K ○ F)
  Fridx-natt {𝔹} {H} {K} α = record
    { fnc = λ {A} → α.fnc {F.ₒ A}
    ; nat = λ f → α.nat (F.ₐ f)
    }
    where module α = natural-transformation α
-}

  ₙₜ : {𝔹 : ecategory}{H K : efunctor 𝔹 ℂ}(α : natural-transformation H K)
                  → natural-transformation (F ○ H) (F ○ K)
  ₙₜ = natt-fctr-post F

  ⋆ₙₜ : {𝔼 : ecategory}{H K : efunctor 𝔻 𝔼}(α : natural-transformation H K)
                  → natural-transformation (H ○ F) (K ○ F)
  ⋆ₙₜ = natt-fctr-pre F

  eqv-is-faith : is-equivalence F → is-faithful F
  eqv-is-faith eqv = record
    { faith-pf = λ {X} {_} {f} {g} eq → ~proof
               f                                     ~[ ridggˢ r ι2.idcod ⊙ ass  ] /
               (f ℂ.∘ ι2.fnc) ℂ.∘ ι2.fnc⁻¹ {X}        ~[ ∘e r (ι2.nat f ˢ) ] /
               (ι2.fnc ℂ.∘ G○F.ₐ f) ℂ.∘ ι2.fnc⁻¹ {X}  ~[ ∘e r (∘e (G.ext eq) r) ] /
               (ι2.fnc ℂ.∘ G○F.ₐ g) ℂ.∘ ι2.fnc⁻¹ {X}  ~[ ∘e r (ι2.nat g) ] /
               (g ℂ.∘ ι2.fnc) ℂ.∘ ι2.fnc⁻¹ {X}        ~[ assˢ ⊙ ridgg r ι2.idcod ]∎
               g ∎
    }
    where open is-equivalence eqv renaming (inv to G)
          module G = efunctor-aux G
          module G○F = efunctor-aux (G ○ F)
          open ecategory-aux-only ℂ


  eqv-is-full : is-adj-equivalence F → is-full F
  eqv-is-full adjeqv = record
    { ar = λ {X} {Y} g → ι2.fnc {Y} ℂ.∘ G.ₐ g ℂ.∘ ι2.fnc⁻¹ {X}
    ; pf = λ {X} {_} {g} → ~proof
              F.ₐ (ι2.fnc ℂ.∘ G.ₐ g ℂ.∘ ι2.fnc⁻¹ {X})          ~[ F.∘ax-rfˢ ⊙ ∘e F.∘ax-rfˢ r ] /
              F.ₐ ι2.fnc 𝔻.∘ F○G.ₐ g 𝔻.∘ F.ₐ (ι2.fnc⁻¹ {X})   ~[ ∘e (∘e eq⁻¹₁ r) eq₁ ] /
              ι1.fnc 𝔻.∘ F○G.ₐ g 𝔻.∘ ι1.fnc⁻¹ {F.ₒ X}         ~[ ∘e (ι1.nat⁻¹ g ˢ) r ] /
              ι1.fnc 𝔻.∘ ι1.fnc⁻¹ 𝔻.∘ g                       ~[ ass ⊙ lidgg r ι1.idcod ]∎
              g ∎
    }
    where open is-adj-equivalence adjeqv renaming (inv to G)
          module G = efunctor-aux G
          module F○G = efunctor-aux (F ○ G)
          open ecategory-aux-only 𝔻


  eqv-is-ess-surj-ob : is-equivalence F → is-ess-surjective-ob F
  eqv-is-ess-surj-ob eqv = record
    { ob = G.ₒ
    ; ar = λ Y → ι1.fnc {Y}
    ; iso = λ Y → 𝔻.mkis-iso (ι1.isiso {Y})
    }
    where open is-equivalence eqv renaming (inv to G)
          module G = efunctor-aux G
          module F○G = efunctor-aux (F ○ G)

-- end functor-basic-props


module efunctor-props {ℂ 𝔻 : ecategory}(F : efunctor ℂ 𝔻) where
  open efunctor-aux F public
  open efunctor-basic-props F public
-- end efunctor-props



-- Essential equivalences are adjoint equivalences

module esseqv-is-adjeqv {ℂ 𝔻 : ecategory}{F : efunctor ℂ 𝔻}(eeqv : is-ess-equivalence F) where
  open is-ess-equivalence eeqv
  open is-faithful isfaithful
  private
    module macros (𝕏 : ecategory) where
        open ecategory 𝕏 public
        open arrows-defs 𝕏 public
        open iso-props 𝕏 public
    module ℂ = macros ℂ
    module 𝔻 = macros 𝔻
    module F = efunctor-aux F
    module full = is-full isfull
    module essrj = is-ess-surjective-ob isesurjobj

  invFₒ : 𝔻.Obj → ℂ.Obj
  invFₒ = essrj.ob
  γ : (Y : 𝔻.Obj) → || 𝔻.Hom (F.ₒ (invFₒ Y)) Y ||
  γ = essrj.ar
  private module γ (Y : 𝔻.Obj) = 𝔻.is-iso (essrj.iso Y)

  invFₐ : {Y Y' : 𝔻.Obj} → || 𝔻.Hom Y Y' || → || ℂ.Hom (invFₒ Y) (invFₒ Y') ||
  invFₐ {Y} {Y'} g = full.ar (γ.⁻¹ Y' 𝔻.∘ g 𝔻.∘ γ Y)

  δ : (X : ℂ.Obj) → || ℂ.Hom (invFₒ (F.ₒ X)) X ||
  δ X = full.ar (γ (F.ₒ X))
  δ⁻¹ : (X : ℂ.Obj) → || ℂ.Hom X (invFₒ (F.ₒ X)) ||
  δ⁻¹ X = full.ar (γ.⁻¹ (F.ₒ X))
  δ-isopair : (X : ℂ.Obj) → ℂ.is-iso-pair (δ X) (δ⁻¹ X)
  δ-isopair X = record
    { iddom = faith-pf (~proof F.ₐ (δ⁻¹ X ℂ.∘ δ X)               ~[ F.∘ax-rfˢ ] /
                               F.ₐ (δ⁻¹ X) 𝔻.∘ F.ₐ (δ X)          ~[ ∘e full.pf full.pf ] /
                               γ.⁻¹ (F.ₒ X) 𝔻.∘ γ (F.ₒ X)          ~[ γ.iddom (F.ₒ X) ⊙ F.idˢ ]∎
                               F.ₐ (ℂ.idar (invFₒ (F.ₒ X)))      ∎)
    ; idcod = faith-pf (~proof F.ₐ (δ X ℂ.∘ δ⁻¹ X)               ~[ F.∘ax-rfˢ ] /
                               F.ₐ (δ X) 𝔻.∘ F.ₐ (δ⁻¹ X)          ~[ ∘e full.pf full.pf ] /
                               γ (F.ₒ X) 𝔻.∘ γ.⁻¹ (F.ₒ X)          ~[ γ.idcod (F.ₒ X) ⊙ F.idˢ ]∎
                               F.ₐ (ℂ.idar X)                  ∎)
    }
    where open ecategory-aux-only 𝔻
  private module δ-tmp (X : ℂ.Obj) = ℂ.is-iso-pair (δ-isopair X)
  open δ-tmp renaming (iddom to δ⁻¹δ=id; idcod to δδ⁻¹=id)

  invF : efunctor 𝔻 ℂ
  invF = record
       { FObj = invFₒ
       ; FHom = invFₐ
       ; isF = record
             { ext = λ {Y} {Y'} {g} {g'} pf → faith-pf (~proof
                   F.ₐ (invFₐ g)                       ~[ full.pf ] /
                   γ.⁻¹ Y' 𝔻.∘ g 𝔻.∘ γ Y              ~[ ∘e (∘e r pf) r ] /
                   γ.⁻¹ Y' 𝔻.∘ g' 𝔻.∘ γ Y             ~[ full.pf ˢ ]∎
                   F.ₐ (invFₐ g')         ∎)
             ; id = λ {Y} → faith-pf (~proof
                  F.ₐ (invFₐ (𝔻.idar Y))              ~[ full.pf ] /
                  γ.⁻¹ Y 𝔻.∘ (𝔻.idar Y) 𝔻.∘ γ Y      ~[ ∘e lid r ⊙ γ.iddom Y ⊙ F.idˢ ]∎
                  F.ₐ (ℂ.idar (invFₒ Y))          ∎)
             ; cmp = λ {Y₁} {Y₂} {Y₃} g₁ g₂ → faith-pf (~proof
                   F.ₐ (invFₐ g₂ ℂ.∘ invFₐ g₁)                                 ~[ F.∘ax-rfˢ ] /
                   F.ₐ (invFₐ g₂) 𝔻.∘ F.ₐ (invFₐ g₁)                          ~[ ∘e full.pf full.pf ] /
                   (γ.⁻¹ Y₃ 𝔻.∘ g₂ 𝔻.∘ γ Y₂) 𝔻.∘ (γ.⁻¹ Y₂ 𝔻.∘ g₁ 𝔻.∘ γ Y₁)  ~[ assˢ ⊙ ∘e ass r ] /
                   γ.⁻¹ Y₃ 𝔻.∘ ((g₂ 𝔻.∘ γ Y₂) 𝔻.∘ γ.⁻¹ Y₂) 𝔻.∘ g₁ 𝔻.∘ γ Y₁  ~[ ∘e (∘e r (assˢ ⊙ ridgg r (γ.idcod Y₂))) r ] /
                   γ.⁻¹ Y₃ 𝔻.∘ g₂ 𝔻.∘ g₁ 𝔻.∘ γ Y₁                            ~[ ∘e ass r ⊙ full.pf ˢ ]∎
                   F.ₐ (invFₐ (g₂ 𝔻.∘ g₁))                             ∎)
             }
       }
       where open ecategory-aux-only 𝔻

  γnat : natural-transformation (F ○ invF) IdF
  γnat = record
    { fnc = λ {Y} → γ Y
    ; nat = λ {Y} {Y'} g → ~proof γ Y' 𝔻.∘ F.ₐ (invFₐ g)           ~[ ∘e full.pf r ⊙ ass ] /
                                   (γ Y' 𝔻.∘ γ.⁻¹ Y') 𝔻.∘ g 𝔻.∘ γ Y   ~[ lidgg r (γ.idcod Y') ]∎
                                   g 𝔻.∘ γ Y                      ∎
    }
    where open ecategory-aux-only 𝔻
  γ⁻¹nat : natural-transformation IdF (F ○ invF)
  γ⁻¹nat = record { fnc = λ {Y} → γ.⁻¹ Y
                  ;  nat = λ {Y} {Y'} g → 𝔻.iso-sq (γ.isisopair Y) (γ.isisopair Y') (nat g)
                  }
                 where open natural-transformation γnat

  δnat : natural-transformation (invF ○ F) IdF
  δnat = record
    { fnc = λ {X} → δ X
    ; nat = λ {X} {X'} f →
          faith-pf (~proof F.ₐ (δ X' ℂ.∘ invFₐ (F.ₐ f))                           ~[ F.∘ax-rfˢ ] /
                           F.ₐ (δ X') 𝔻.∘ F.ₐ (invFₐ (F.ₐ f))                     ~[ ∘e full.pf full.pf ] /
                           γ (F.ₒ X') 𝔻.∘ γ.⁻¹ (F.ₒ X') 𝔻.∘ F.ₐ f 𝔻.∘ γ (F.ₒ X)   ~[ ass ⊙ lidgg r (γ.idcod (F.ₒ X')) ] /
                           F.ₐ f 𝔻.∘ γ (F.ₒ X)                                   ~[ ∘e (full.pf ˢ) r ⊙ F.∘ax-rf ]∎
                           F.ₐ (f ℂ.∘ δ X)                                   ∎)
    }
    where open ecategory-aux-only 𝔻
  δ⁻¹nat : natural-transformation IdF (invF ○ F)
  δ⁻¹nat = record { fnc = λ {X} → δ⁻¹ X
                  ; nat = λ {X} {X'} f → ℂ.iso-sq (δ-isopair X) (δ-isopair X') (nat f)
                  }
                  where open natural-transformation δnat

  trid₁ : {X : ℂ.Obj} → γ (F.ₒ X) 𝔻.∘ F.ₐ (δ⁻¹ X) 𝔻.~ 𝔻.idar (F.ₒ X)
  trid₁ {X} = ~proof γ (F.ₒ X) 𝔻.∘ F.ₐ (δ⁻¹ X)     ~[ ∘e full.pf r ] /
                     γ (F.ₒ X) 𝔻.∘ γ.⁻¹ (F.ₒ X)    ~[ γ.idcod (F.ₒ X) ]∎
                     𝔻.idar (F.ₒ X) ∎
            where open ecategory-aux-only 𝔻
  trid₂ : {Y : 𝔻.Obj} → invFₐ (γ Y) ℂ.∘ δ⁻¹ (invFₒ Y) ℂ.~ ℂ.idar (invFₒ Y)
  trid₂ {Y} = faith-pf (~proof
    F.ₐ (invFₐ (γ Y) ℂ.∘ δ⁻¹ (invFₒ Y))           ~[ F.∘ax-rfˢ ⊙ (∘e full.pf (full.pf ⊙ ass) ⊙ assˢ) ] /
    (γ.⁻¹ Y 𝔻.∘ γ Y) 𝔻.∘ γ (F.ₒ (invFₒ Y)) 𝔻.∘ γ.⁻¹ (F.ₒ (invFₒ Y))  ~[ lidgg (γ.idcod (F.ₒ (invFₒ Y))) (γ.iddom Y) ⊙ F.idˢ ]∎
    F.ₐ (ℂ.idar (invFₒ Y)) ∎)
    where open ecategory-aux-only 𝔻

  adjeqv : is-adj-equivalence-pair F invF
  adjeqv = record
    { ι1 = record { natt = γnat
                  ; natt⁻¹ = γ⁻¹nat
                  ; isiso = record
                          { iddom = γ.iddom _
                          ; idcod = γ.idcod _
                          }
                  }
    ; ι2 = record { natt = δnat
                  ; natt⁻¹ = δ⁻¹nat
                  ; isiso = record
                          { iddom = δ⁻¹δ=id _
                          ; idcod = δδ⁻¹=id _
                          }
                  }
    ; trid₁ = trid₁
    ; trid₂ = trid₂
    }
-- end eeqv-is-eqv

esseqv-is-adjeqv : {ℂ 𝔻 : ecategory} {F : efunctor ℂ 𝔻}
                        → is-ess-equivalence F → is-adj-equivalence F
esseqv-is-adjeqv {F = F} eeqv = record
  { inv = invF
  ; isadjeqvp = adjeqv
  }
  where open esseqv-is-adjeqv eeqv

-- Some additional properties of (adjoint) equivalences

module equivalence-props {ℂ 𝔻 : ecategory}(F : efunctor ℂ 𝔻)(G : efunctor 𝔻 ℂ)
                         where
  private
    module ecat-macros (𝕏 : ecategory) where
      open ecategory 𝕏 public
      open iso-defs 𝕏 public
      open iso-props 𝕏 public
      open comm-shapes 𝕏 public
      open epi&mono-defs 𝕏 public
      open finite-limits-d&p 𝕏 public
    module ℂ = ecat-macros ℂ
    module 𝔻 = ecat-macros 𝔻
    module efctr-macros {𝕏 𝕐 : ecategory}(K : efunctor 𝕏 𝕐) where
      open efunctor-props K public
      --open efunctor-basic-props K public
    module F = efctr-macros F
    module G = efctr-macros G
    module G○F = efctr-macros (G ○ F)
    module F○G = efctr-macros (F ○ G)

  eqv-tr-post : is-equivalence-pair F G → {𝔼 : ecategory}{H : efunctor 𝔻 𝔼}{K : efunctor ℂ 𝔼}
                    → H ○ F ≅ₐ K → K ○ G ≅ₐ H
  eqv-tr-post iseqvp {𝔼} {H} {K} tr =
    natiso-vcmp (natiso-vcmp (natiso-vcmp {H = H} ○rid (natiso-hcmp (≅ₐrefl {F = H}) ep.ι1))
                             (○assˢ {F = G} {F} {H}))
                (natiso-hcmp tr⁻¹ (≅ₐrefl {F = G}))
    where module ep = is-equivalence-pair iseqvp
          module tr = natural-iso tr
          tr⁻¹ : K ≅ₐ H ○ F
          tr⁻¹ = ≅ₐsym tr

  eqv-tr-pre : is-equivalence-pair F G → {𝔹 : ecategory}{H : efunctor 𝔹 ℂ}{K : efunctor 𝔹 𝔻}
                   → F ○ H ≅ₐ K → G ○ K ≅ₐ H
  eqv-tr-pre iseqvp {𝔹} {H} {K} tr = 
    natiso-vcmp ○lid ( natiso-vcmp (natiso-hcmp ep.ι2 (≅ₐrefl {F = H}))
                                   (natiso-vcmp (○ass {F = H} {F} {G})
                                   (natiso-hcmp (≅ₐrefl {F = G}) tr⁻¹)) )
    where module ep = is-equivalence-pair iseqvp
          module tr = natural-iso tr
          tr⁻¹ : K ≅ₐ F ○ H
          tr⁻¹ = ≅ₐsym tr

  module eqv-is-adj-eqv (iseqv : is-equivalence-pair F G) where
    open is-equivalence-pair iseqv

    -- Here we keep ι1 as counit, and construct its unit.
    η-fnc : {A : ℂ.Obj} → || ℂ.Hom A (G.ₒ (F.ₒ A)) ||
    η-fnc {A} = ι2.fnc {G.ₒ (F.ₒ A)} ℂ.∘ G.ₐ (ι1.fnc⁻¹ {F.ₒ A}) ℂ.∘ ι2.fnc⁻¹ {A}
    η : natural-transformation IdF (G ○ F)
    η = record
       { fnc = η-fnc
       ; nat = λ {A} {B} f → ~proof
             η-fnc ℂ.∘ f              ~[ assˢ ⊙ ∘e (assˢ ⊙ ∘e (ι2.nat⁻¹ f) r) r ] /
             ι2.fnc {G.ₒ (F.ₒ B)} ℂ.∘ G.ₐ (ι1.fnc⁻¹ {F.ₒ B}) ℂ.∘ G○F.ₐ f ℂ.∘ ι2.fnc⁻¹ {A}
                                      ~[ ∘e (ass ⊙ ∘e r (G.∘∘ (ι1.nat⁻¹ (F.ₐ f))) ⊙ assˢ) r ] /
             ι2.fnc {G.ₒ (F.ₒ B)} ℂ.∘ G.ₐ (F○G.ₐ (F.ₐ f)) ℂ.∘ G.ₐ (ι1.fnc⁻¹ {F.ₒ A}) ℂ.∘ ι2.fnc⁻¹ {A}
                                      ~[ ass ⊙ ∘e r (ι2.nat (G○F.ₐ f)) ⊙ assˢ ]∎
             G○F.ₐ f ℂ.∘ η-fnc ∎
       }
       where open ecategory-aux-only ℂ
    module η = natural-transformation η

    {- η' consists also of 4 identity arrows corresponding to 2 lid and 2 ass.
    η' : natural-transformation IdF (G ○ F)
    η' = natt-vcmp ○lid.natt (natt-vcmp (G○F.⋆ₙₜ ι2.natt)
                                       (natt-vcmp ass-aux
                                                  (natt-vcmp (G.ₙₜ (F.⋆ₙₜ ι1.natt⁻¹))
                                                             (natt-vcmp (G.ₙₜ (○lid.natt⁻¹ {K = F}))
                                                                        ι2.natt⁻¹))))
      where module ○lid {𝕏 𝕐 : ecategory}{K : efunctor 𝕏 𝕐}
                           = natural-iso (○lid {𝕏} {𝕐} {K})
            module ○ass {𝕏 𝕐 𝕍 ℤ : ecategory}{K₁ : efunctor 𝕏 𝕐}{K₂ : efunctor 𝕐 𝕍}{K₃ : efunctor 𝕍 ℤ}
                           = natural-iso (○ass {𝕏} {𝕐} {𝕍} {ℤ} {K₁} {K₂} {K₃})
            ass-aux : G ○ (F ○ G) ○ F ⇒ (G ○ F) ○ G ○ F
            ass-aux = natt-vcmp (○ass.natt {K₁ = G ○ F} {K₂ = F} {K₃ = G})
                                (G.ₙₜ (○ass.natt⁻¹ {K₁ = F} {K₂ = G} {K₃ = F}))
    -}

    η⁻¹-fnc : {A : ℂ.Obj} → || ℂ.Hom (G.ₒ (F.ₒ A)) A ||
    η⁻¹-fnc {A} = ι2.fnc {A} ℂ.∘ G.ₐ (ι1.fnc {F.ₒ A}) ℂ.∘ ι2.fnc⁻¹ {G.ₒ (F.ₒ A)}
    ηiso : (A : ℂ.Obj) → ℂ.is-iso-pair (η.fnc {A}) (η⁻¹-fnc {A})
    ηiso A = ℂ.iso-pair-tricmp (ℂ.inv-iso-pair (ι2.isiso {A}))
                                 (G.ᵢₛₒ (𝔻.inv-iso-pair ι1.isiso))
                                 (ι2.isiso {G.ₒ (F.ₒ A)})

    η⁻¹ : natural-transformation (G ○ F) IdF
    η⁻¹ = record
      { fnc = η⁻¹-fnc
      ; nat = λ f → ℂ.iso-sq (ηiso _) (ηiso _) (η.nat f)
      }
    ιη : natural-iso (G ○ F) IdF
    ιη = record
       { natt = η⁻¹
       ; natt⁻¹ = η
       ; isiso = λ {A} → ℂ.inv-iso-pair (ηiso A)
       }
    module ιη = natural-iso ιη

    GεηG : {B : 𝔻.Obj} → G.ₐ ι1.fnc ℂ.∘ η.fnc {G.ₒ B} ℂ.~ ℂ.idar (G.ₒ B)
    GεηG {B} = ~proof
      G.ₐ ι1.fnc ℂ.∘ ι2.fnc {G○F.ₒ (G.ₒ B)} ℂ.∘ G.ₐ (ι1.fnc⁻¹ {F.ₒ (G.ₒ B)}) ℂ.∘ ι2.fnc⁻¹ {G.ₒ B}
                 ~[ ass ⊙ ∘e r (ι2.nat (G.ₐ ι1.fnc) ˢ) ⊙ assˢ ] /
      ι2.fnc {G.ₒ B} ℂ.∘ G.ₐ (F○G.ₐ ι1.fnc) ℂ.∘  G.ₐ (ι1.fnc⁻¹ {F.ₒ (G.ₒ B)}) ℂ.∘ ι2.fnc⁻¹ {G.ₒ B}
                 ~[ ∘e (ass ⊙ ∘e r (G.∘∘ (ι1.nat⁻¹ ι1.fnc) ˢ)) r ] /
      ι2.fnc {G.ₒ B} ℂ.∘ (G.ₐ (ι1.fnc⁻¹ {B}) ℂ.∘ G.ₐ ι1.fnc) ℂ.∘ ι2.fnc⁻¹ {G.ₒ B}
                 ~[ ∘e (lidgg r (G.∘ax ι1.iddom ⊙ G.id)) r ] /
      ι2.fnc {G.ₒ B} ℂ.∘ ι2.fnc⁻¹ {G.ₒ B}          ~[ ι2.idcod ]∎
      ℂ.idar (G.ₒ B) ∎
      where open ecategory-aux-only ℂ
    ηG-inv : {B : 𝔻.Obj} → η.fnc {G.ₒ B} ℂ.~ G.ₐ ι1.fnc⁻¹
    ηG-inv {B} = lidggˢ r Gι1.iddom ⊙ assˢ ⊙ ridgg r (GεηG {B})
               where open ecategory-aux-only ℂ
                     module Gι1 = ℂ.is-iso-pair (G.ᵢₛₒ ι1.isiso)
    εFFη : {A : ℂ.Obj} → ι1.fnc {F.ₒ A} 𝔻.∘ F.ₐ (η.fnc {A}) 𝔻.~ 𝔻.idar (F.ₒ A)
    εFFη {A} = ~proof
      ι1.fnc {F.ₒ A} 𝔻.∘ F.ₐ (η.fnc {A})
                     ~[ ∘e (lidggˢ r (F.∘ax (G○F.∘ax ι2.idcod) ⊙ F.idax G○F.id) ⊙ assˢ) r ] /
      ι1.fnc {F.ₒ A} 𝔻.∘ F.ₐ (G○F.ₐ ι2.fnc) 𝔻.∘ F.ₐ (G○F.ₐ ι2.fnc⁻¹) 𝔻.∘ F.ₐ (η.fnc {A})
                     ~[ ass ⊙ ∘e (F.∘∘ (η.nat ι2.fnc⁻¹) ˢ) r ] /
      (ι1.fnc {F.ₒ A} 𝔻.∘ F.ₐ (G○F.ₐ ι2.fnc)) 𝔻.∘ F.ₐ (η.fnc {G○F.ₒ A}) 𝔻.∘ F.ₐ ι2.fnc⁻¹
                     ~[ ∘e (∘e r (F.ext ηG-inv)) (ι1.nat (F.ₐ ι2.fnc)) ⊙ assˢ ] /
      F.ₐ ι2.fnc 𝔻.∘ ι1.fnc {F○G.ₒ (F.ₒ A)} 𝔻.∘ F○G.ₐ (ι1.fnc⁻¹ {F.ₒ A}) 𝔻.∘ F.ₐ ι2.fnc⁻¹
                     ~[ ∘e (ass ⊙ ∘e r (ι1.nat ι1.fnc⁻¹)) r ] /
      F.ₐ ι2.fnc 𝔻.∘ (ι1.fnc⁻¹ {F.ₒ A} 𝔻.∘ ι1.fnc {F.ₒ A}) 𝔻.∘ F.ₐ ι2.fnc⁻¹
                     ~[ ∘e (lidgg r ι1.iddom) r ] /
      F.ₐ ι2.fnc 𝔻.∘ F.ₐ ι2.fnc⁻¹ ~[ F.∘ax ι2.idcod ⊙ F.id ]∎
      𝔻.idar (F.ₒ A) ∎
      where open ecategory-aux-only 𝔻

    -- not needed here, but it can be used to derive GεηG
    η-unv-uq : {B : 𝔻.Obj}{A : ℂ.Obj}{f : || 𝔻.Hom (F.ₒ A) B ||}{u : || ℂ.Hom A (G.ₒ B) ||}
                  → ι1.fnc 𝔻.∘ F.ₐ u 𝔻.~ f → u ℂ.~ G.ₐ f ℂ.∘ η.fnc
    η-unv-uq {B} {A} {f} {u} utr = ~proof
      u                                                         ~[ lidggˢ r ι2.idcod ⊙ assˢ ] /
      ι2.fnc {G.ₒ B} ℂ.∘ ι2.fnc⁻¹ {G.ₒ B} ℂ.∘ u                    ~[ ∘e (ι2.nat⁻¹ u) r ] /
      ι2.fnc {G.ₒ B} ℂ.∘ G○F.ₐ u ℂ.∘ ι2.fnc⁻¹ {A}
                                  ~[ ∘e (∘e r (G.∘axˢ (𝔻.iso-trcod ι1.isiso utr)) ⊙ assˢ) r ] /
      ι2.fnc {G.ₒ B} ℂ.∘ G.ₐ (ι1.fnc⁻¹ {B}) ℂ.∘ G.ₐ f ℂ.∘ ι2.fnc⁻¹ {A}
                                       ~[ ∘e (ass ⊙ ∘e r (G.∘∘ (ι1.nat⁻¹ f)) ⊙ assˢ) r ] /
      ι2.fnc {G.ₒ B} ℂ.∘ G.ₐ (F○G.ₐ f) ℂ.∘  G.ₐ (ι1.fnc⁻¹ {F.ₒ A}) ℂ.∘ ι2.fnc⁻¹ {A}
                                                ~[ ass ⊙ ∘e r (ι2.nat (G.ₐ f)) ⊙ assˢ ]∎
      G.ₐ f ℂ.∘ ι2.fnc {G○F.ₒ A} ℂ.∘ G.ₐ (ι1.fnc⁻¹ {F.ₒ A}) ℂ.∘ ι2.fnc⁻¹ {A} ∎
      where open ecategory-aux-only ℂ
  -- end eqv-is-adj-eqv

  eqv-is-adj-eqv-ε : is-equivalence-pair F G → is-adj-equivalence-pair F G
  eqv-is-adj-eqv-ε eqvp = record
    { ι1 = ι1
    ; ι2 = ιη
    ; trid₁ = εFFη
    ; trid₂ = GεηG
    }
    where open is-equivalence-pair eqvp
          open eqv-is-adj-eqv eqvp


  -- Adjoint equivalences preserve stuff

  module adj-eqv-pres-fin-lim (adjeqv : is-adj-equivalence-pair F G) where
    open is-adj-equivalence-pair adjeqv
      
    module pres-term {X : ℂ.Obj}(Xtrm : ℂ.is-terminal X) where
      private module X = ℂ.is-terminal Xtrm
      istrm : 𝔻.is-terminal (F.ₒ X)
      istrm = record
        { ! = λ B → F.ₐ (X.! (G.ₒ B)) 𝔻.∘ ι1.fnc⁻¹ {B}
        ; !uniq = λ {B} f → ~proof
                f                                             ~[ lidggˢ r (trid⁻¹₁ {X}) ⊙ assˢ ] /
                F.ₐ (ι2.fnc {X}) 𝔻.∘ ι1.fnc⁻¹ {F.ₒ X} 𝔻.∘ f             ~[ ∘e (ι1.nat⁻¹ f) r ] /
                F.ₐ (ι2.fnc {X}) 𝔻.∘ F.ₐ (G.ₐ f) 𝔻.∘ ι1.fnc⁻¹ {B}   ~[ ass ⊙ ∘e r F.∘ax-rf ] /
                F.ₐ (ι2.fnc {X} ℂ.∘ G.ₐ f) 𝔻.∘ ι1.fnc⁻¹ {B}
                                              ~[ ∘e r (F.ext (X.!uniq (ι2.fnc {X} ℂ.∘ G.ₐ f))) ]∎
                F.ₐ (X.! (G.ₒ B)) 𝔻.∘ ι1.fnc⁻¹ {B} ∎
        }
        where open ecategory-aux-only 𝔻
    --end pres-term

    pres-term : preserves-terminal F
    pres-term = record
      { pres-!-pf = pres-term.istrm
      }

    module pres-bin-products {sp : ℂ.span}(isprd : ℂ.is-product sp) where
      private
        module ×sp = ℂ.bin-product (ℂ.mk× isprd)
        module Fsp = 𝔻.span (F.span sp)
      unv : {A : 𝔻.Obj} → || 𝔻.Hom A (𝔻.span.O1 (F.span sp)) ||
               → || 𝔻.Hom A (𝔻.span.O2 (F.span sp)) ||
                 → || 𝔻.Hom A (comm-shapes.span.O12 (F.span sp)) ||
      unv {A} f g = F.ₐ ×sp.< ι2.fnc ℂ.∘ G.ₐ f , ι2.fnc ℂ.∘ G.ₐ g > 𝔻.∘ ι1.fnc⁻¹ {A}
      tr₁ : {A : 𝔻.Obj}(f : || 𝔻.Hom A (𝔻.span.O1 (F.span sp)) ||)(g : || 𝔻.Hom A (𝔻.span.O2 (F.span sp)) ||)
                 → F.ₐ ×sp.π₁ 𝔻.∘ unv f g 𝔻.~ f
      tr₁ {A} f g = ~proof
        F.ₐ ×sp.π₁ 𝔻.∘ unv f g                   ~[ ass ⊙ ∘e r (F.∘∘ ×sp.×tr₁) ⊙ assˢ ] /
        F.ₐ ι2.fnc 𝔻.∘ F○G.ₐ f 𝔻.∘ ι1.fnc⁻¹ {A}  ~[ ∘e (ι1.nat⁻¹ f ˢ) r ] /
        F.ₐ ι2.fnc 𝔻.∘ ι1.fnc⁻¹ 𝔻.∘ f            ~[ ass ⊙ lidgg r trid⁻¹₁ ]∎
        f ∎
        where open ecategory-aux-only 𝔻
      tr₂ : {A : 𝔻.Obj}(f : || 𝔻.Hom A (𝔻.span.O1 (F.span sp)) ||)(g : || 𝔻.Hom A (𝔻.span.O2 (F.span sp)) ||)
                 → F.ₐ ×sp.π₂ 𝔻.∘ unv f g 𝔻.~ g
      tr₂ {A} f g = ~proof
        F.ₐ ×sp.π₂ 𝔻.∘ unv f g                   ~[ ass ⊙ ∘e r (F.∘∘ ×sp.×tr₂) ⊙ assˢ ] /
        F.ₐ ι2.fnc 𝔻.∘ F○G.ₐ g 𝔻.∘ ι1.fnc⁻¹ {A}  ~[ ∘e (ι1.nat⁻¹ g ˢ) r ] /
        F.ₐ ι2.fnc 𝔻.∘ ι1.fnc⁻¹ 𝔻.∘ g            ~[ ass ⊙ lidgg r trid⁻¹₁ ]∎
        g ∎
        where open ecategory-aux-only 𝔻
      uq : {A : 𝔻.Obj}{h h' : || 𝔻.Hom A Fsp.O12 ||}
              → Fsp.a1 𝔻.∘ h 𝔻.~ Fsp.a1 𝔻.∘ h' → Fsp.a2 𝔻.∘ h 𝔻.~ Fsp.a2 𝔻.∘ h'
                → h 𝔻.~ h'
      uq {A} {h} {h'} pf₁ pf₂ = Gfaith.pf (~proof
        G.ₐ h                            ~[ lidggˢ r ι2.iddom ⊙ assˢ ] /
        ι2.fnc⁻¹ ℂ.∘ ι2.fnc ℂ.∘ G.ₐ h    ~[ ∘e (×sp.×uq aux₁ aux₂) r ] /
        ι2.fnc⁻¹ ℂ.∘ ι2.fnc ℂ.∘ G.ₐ h'   ~[ ass ⊙ lidgg r ι2.iddom ]∎
        G.ₐ h' ∎)
        where Geqv : is-equivalence G
              Geqv = record { inv = F ; iseqvp = inv-is-eqv (adjeqvp2eqvp adjeqv) }
              module Gfaith = is-faithful (G.eqv-is-faith Geqv) renaming (faith-pf to pf)
              open ecategory-aux-only ℂ
              aux₁ : ×sp.π₁ ℂ.∘  ι2.fnc ℂ.∘ G.ₐ h ℂ.~ ×sp.π₁ ℂ.∘ ι2.fnc ℂ.∘ G.ₐ h'
              aux₁ = ~proof
                ×sp.π₁ ℂ.∘ ι2.fnc ℂ.∘ G.ₐ h          ~[ ass ⊙ ∘e r (ι2.nat ×sp.π₁ ˢ) ⊙ assˢ ] /
                ι2.fnc ℂ.∘ G○F.ₐ ×sp.π₁ ℂ.∘ G.ₐ h     ~[ ∘e (G.∘∘ pf₁) r ] /
                ι2.fnc ℂ.∘ G○F.ₐ ×sp.π₁ ℂ.∘ G.ₐ h'    ~[ ass ⊙ ∘e r (ι2.nat ×sp.π₁) ⊙ assˢ ]∎
                ×sp.π₁ ℂ.∘ ι2.fnc ℂ.∘ G.ₐ h' ∎
              aux₂ : ×sp.π₂ ℂ.∘  ι2.fnc ℂ.∘ G.ₐ h ℂ.~ ×sp.π₂ ℂ.∘ ι2.fnc ℂ.∘ G.ₐ h'
              aux₂ = ~proof
                ×sp.π₂ ℂ.∘ ι2.fnc ℂ.∘ G.ₐ h          ~[ ass ⊙ ∘e r (ι2.nat ×sp.π₂ ˢ) ⊙ assˢ ] /
                ι2.fnc ℂ.∘ G○F.ₐ ×sp.π₂ ℂ.∘ G.ₐ h     ~[ ∘e (G.∘∘ pf₂) r ] /
                ι2.fnc ℂ.∘ G○F.ₐ ×sp.π₂ ℂ.∘ G.ₐ h'    ~[ ass ⊙ ∘e r (ι2.nat ×sp.π₂) ⊙ assˢ ]∎
                ×sp.π₂ ℂ.∘ ι2.fnc ℂ.∘ G.ₐ h' ∎

      Fprd : 𝔻.is-product (F.span sp)
      Fprd = record
        { <_,_> = unv
        ; ×tr₁ = λ {_} {f} {g} → tr₁ f g
        ; ×tr₂ = λ {_} {f} {g} → tr₂ f g
        ; ×uq = uq
        }
        where open ecategory-aux-only 𝔻
    --end pres-bin-products

    pres-prods : preserves-bin-products F
    pres-prods = record
      { pres-×-pf = Fprd
      }
      where open pres-bin-products


    module pres-equalisers {A B E : ℂ.Obj}{f f' : || ℂ.Hom A B ||}{e : || ℂ.Hom E A ||}
                           {pfeq : f ℂ.∘ e ℂ.~ f' ℂ.∘ e}(iseql : ℂ.is-equaliser pfeq)
                           where
      private
        module eql = ℂ.is-equaliser iseql
        --module Fsq/ = 𝔻.square/cosp (F.sq/ sq/)

      unv-pf : {C : 𝔻.Obj}{h : || 𝔻.Hom C (F.FObj A) ||}
               → F.ₐ f 𝔻.∘ h 𝔻.~ F.ₐ f' 𝔻.∘ h → f ℂ.∘ ι2.fnc ℂ.∘ G.ₐ h ℂ.~ f' ℂ.∘ ι2.fnc ℂ.∘ G.ₐ h
      unv-pf {C} {h} pf = ~proof
        f ℂ.∘ ι2.fnc ℂ.∘ G.ₐ h           ~[ ass ⊙ ∘e r (ι2.nat f ˢ) ⊙ assˢ ] /
        ι2.fnc ℂ.∘ G○F.ₐ f ℂ.∘ G.ₐ h     ~[ ∘e (G.∘∘ pf) r ] /
        ι2.fnc ℂ.∘ G○F.ₐ f' ℂ.∘ G.ₐ h    ~[ ass ⊙ ∘e r (ι2.nat f') ⊙ assˢ ]∎
        f' ℂ.∘ ι2.fnc ℂ.∘ G.ₐ h ∎
                        where open ecategory-aux-only ℂ
      unv : {C : 𝔻.Obj}(h : || 𝔻.Hom C (F.FObj A) ||)
               → F.ₐ f 𝔻.∘ h 𝔻.~ F.ₐ f' 𝔻.∘ h → || 𝔻.Hom C (F.ₒ E) ||
      unv {C} h pf = F.ₐ ((ι2.fnc ℂ.∘ G.ₐ h) eql.|[ unv-pf pf ]) 𝔻.∘ ι1.fnc⁻¹ {C}

      tr : {C : 𝔻.Obj}{h : || 𝔻.Hom C (F.FObj A) ||}(pf : F.ₐ f 𝔻.∘ h 𝔻.~ F.ₐ f' 𝔻.∘ h)
              → F.ₐ e 𝔻.∘ unv h pf 𝔻.~ h
      tr {C} {h} pf = ~proof
        F.ₐ e 𝔻.∘ unv h pf             ~[ ass ⊙ ∘e r (F.∘∘ (eql.tr (unv-pf pf))) ⊙ assˢ ] /
        F.ₐ ι2.fnc 𝔻.∘ F○G.ₐ h 𝔻.∘ ι1.fnc⁻¹ {C}    ~[ ∘e (ι1.nat⁻¹ h ˢ) r ] /
        F.ₐ ι2.fnc 𝔻.∘ ι1.fnc⁻¹ 𝔻.∘ h              ~[ ass ⊙ lidgg r trid⁻¹₁ ]∎
        h ∎
        where open ecategory-aux-only 𝔻
      
      uq : {C : 𝔻.Obj}{h h' : || 𝔻.Hom C (F.ₒ E) ||} → F.ₐ e 𝔻.∘ h 𝔻.~ F.ₐ e 𝔻.∘ h'
              → h 𝔻.~ h'
      uq {C} {h} {h'} pf = Gfaith.pf (~proof
        G.ₐ h                            ~[ lidggˢ r ι2.iddom ⊙ assˢ ] /
        ι2.fnc⁻¹ ℂ.∘ ι2.fnc ℂ.∘ G.ₐ h    ~[ ∘e (eql.uq aux) r ] /
        ι2.fnc⁻¹ ℂ.∘ ι2.fnc ℂ.∘ G.ₐ h'   ~[ ass ⊙ lidgg r ι2.iddom ]∎
        G.ₐ h' ∎)
        where Geqv : is-equivalence G
              Geqv = record { inv = F ; iseqvp = inv-is-eqv (adjeqvp2eqvp adjeqv) }
              module Gfaith = is-faithful (G.eqv-is-faith Geqv) renaming (faith-pf to pf)
              open ecategory-aux-only ℂ
              aux : e ℂ.∘ ι2.fnc ℂ.∘ G.ₐ h ℂ.~ e ℂ.∘ ι2.fnc ℂ.∘ G.ₐ h'
              aux = ~proof
                e ℂ.∘  ι2.fnc ℂ.∘ G.ₐ h          ~[ ass ⊙ ∘e r (ι2.nat e ˢ) ⊙ assˢ ] /
                ι2.fnc ℂ.∘ G○F.ₐ e ℂ.∘ G.ₐ h     ~[ ∘e (G.∘∘ pf) r ] /
                ι2.fnc ℂ.∘ G○F.ₐ e ℂ.∘ G.ₐ h'    ~[ ass ⊙ ∘e r (ι2.nat e) ⊙ assˢ ]∎
                e ℂ.∘ ι2.fnc ℂ.∘ G.ₐ h' ∎
      Feql : 𝔻.is-equaliser (F.∘∘ pfeq)
      Feql = record
        { _|[_] = unv
        ; tr = tr
        ; uq = uq
        }
    --end pres-equalisers

    pres-eql : preserves-equalisers F
    pres-eql = record
      { pres-eql-pf = Feql
      }
      where open pres-equalisers



    module pres-pullbacks {I A B : ℂ.Obj} {a : || ℂ.Hom A I ||} {b : || ℂ.Hom B I ||}
                          {sq/ : ℂ.square/cosp a b}(ispb : ℂ.is-pb-square (ℂ.mksq sq/))
                          where
      private
        module ×/sq = ℂ.pullback-of-not (ℂ.mkpb-of ispb)
        module Fsq/ = 𝔻.square/cosp (F.sq/ sq/)

      unv-pf : {C : 𝔻.Obj}{h : || 𝔻.Hom C (F.FObj A) ||}{k : || 𝔻.Hom C (F.FObj B) ||}
               → F.ₐ a 𝔻.∘ h 𝔻.~ F.ₐ b 𝔻.∘ k → a ℂ.∘ ι2.fnc ℂ.∘ G.ₐ h ℂ.~ b ℂ.∘ ι2.fnc ℂ.∘ G.ₐ k
      unv-pf {C} {h} {k} pf = ~proof
        a ℂ.∘ ι2.fnc ℂ.∘ G.ₐ h          ~[ ass ⊙ ∘e r (ι2.nat a ˢ) ⊙ assˢ ] /
        ι2.fnc ℂ.∘ G○F.ₐ a ℂ.∘ G.ₐ h    ~[ ∘e (G.∘∘ pf) r ] /
        ι2.fnc ℂ.∘ G○F.ₐ b ℂ.∘ G.ₐ k    ~[ ass ⊙ ∘e r (ι2.nat b) ⊙ assˢ ]∎
        b ℂ.∘ ι2.fnc ℂ.∘ G.ₐ k ∎
                            where open ecategory-aux-only ℂ
      unv : {C : 𝔻.Obj}(h : || 𝔻.Hom C (F.FObj A) ||)(k : || 𝔻.Hom C (F.FObj B) ||)
               → F.ₐ a 𝔻.∘ h 𝔻.~ F.ₐ b 𝔻.∘ k → || 𝔻.Hom C Fsq/.ul ||
      unv {C} h k pf = F.ₐ ×/sq.⟨ ι2.fnc ℂ.∘ G.ₐ h , ι2.fnc ℂ.∘ G.ₐ k ⟩[ unv-pf pf ] 𝔻.∘ ι1.fnc⁻¹ {C}

      tr₁ : {C : 𝔻.Obj}{h : || 𝔻.Hom C (F.FObj A) ||}{k : || 𝔻.Hom C (F.FObj B) ||}
            (pf : F.ₐ a 𝔻.∘ h 𝔻.~ F.ₐ b 𝔻.∘ k) → F.ₐ ×/sq.π/₁ 𝔻.∘ unv h k pf 𝔻.~ h
      tr₁ {C} {h} {k} pf = ~proof
        F.ₐ ×/sq.π/₁ 𝔻.∘ unv h k pf             ~[ ass ⊙ ∘e r (F.∘∘ (×/sq.×/tr₁ (unv-pf pf))) ⊙ assˢ ] /
        F.ₐ ι2.fnc 𝔻.∘ F○G.ₐ h 𝔻.∘ ι1.fnc⁻¹ {C}    ~[ ∘e (ι1.nat⁻¹ h ˢ) r ] /
        F.ₐ ι2.fnc 𝔻.∘ ι1.fnc⁻¹ 𝔻.∘ h              ~[ ass ⊙ lidgg r trid⁻¹₁ ]∎
        h ∎
        where open ecategory-aux-only 𝔻
      tr₂ : {C : 𝔻.Obj}{h : || 𝔻.Hom C (F.FObj A) ||}{k : || 𝔻.Hom C (F.FObj B) ||}
            (pf : F.ₐ a 𝔻.∘ h 𝔻.~ F.ₐ b 𝔻.∘ k) → F.ₐ ×/sq.π/₂ 𝔻.∘ unv h k pf 𝔻.~ k
      tr₂ {C} {h} {k} pf = ~proof
        F.ₐ ×/sq.π/₂ 𝔻.∘ unv h k pf             ~[ ass ⊙ ∘e r (F.∘∘ (×/sq.×/tr₂ (unv-pf pf))) ⊙ assˢ ] /
        F.ₐ ι2.fnc 𝔻.∘ F○G.ₐ k 𝔻.∘ ι1.fnc⁻¹ {C}    ~[ ∘e (ι1.nat⁻¹ k ˢ) r ] /
        F.ₐ ι2.fnc 𝔻.∘ ι1.fnc⁻¹ 𝔻.∘ k              ~[ ass ⊙ lidgg r trid⁻¹₁ ]∎
        k ∎
        where open ecategory-aux-only 𝔻

      uq : {C : 𝔻.Obj}{h h' : || 𝔻.Hom C Fsq/.ul ||} → F.ₐ ×/sq.π/₁ 𝔻.∘ h 𝔻.~ F.ₐ ×/sq.π/₁ 𝔻.∘ h'
              → F.ₐ ×/sq.π/₂ 𝔻.∘ h 𝔻.~ F.ₐ ×/sq.π/₂ 𝔻.∘ h'
                → h 𝔻.~ h'
      uq {C} {h} {h'} pf₁ pf₂ = Gfaith.pf (~proof
        G.ₐ h                            ~[ lidggˢ r ι2.iddom ⊙ assˢ ] /
        ι2.fnc⁻¹ ℂ.∘ ι2.fnc ℂ.∘ G.ₐ h    ~[ ∘e (×/sq.×/uq aux₁ aux₂) r ] /
        ι2.fnc⁻¹ ℂ.∘ ι2.fnc ℂ.∘ G.ₐ h'   ~[ ass ⊙ lidgg r ι2.iddom ]∎
        G.ₐ h' ∎)
        where Geqv : is-equivalence G
              Geqv = record { inv = F ; iseqvp = inv-is-eqv (adjeqvp2eqvp adjeqv) }
              module Gfaith = is-faithful (G.eqv-is-faith Geqv) renaming (faith-pf to pf)
              open ecategory-aux-only ℂ
              aux₁ : ×/sq.π/₁ ℂ.∘ ι2.fnc ℂ.∘ G.ₐ h ℂ.~ ×/sq.π/₁ ℂ.∘ ι2.fnc ℂ.∘ G.ₐ h'
              aux₁ = ~proof
                ×/sq.π/₁ ℂ.∘  ι2.fnc ℂ.∘ G.ₐ h          ~[ ass ⊙ ∘e r (ι2.nat ×/sq.π/₁ ˢ) ⊙ assˢ ] /
                ι2.fnc ℂ.∘ G○F.ₐ ×/sq.π/₁ ℂ.∘ G.ₐ h     ~[ ∘e (G.∘∘ pf₁) r ] /
                ι2.fnc ℂ.∘ G○F.ₐ ×/sq.π/₁ ℂ.∘ G.ₐ h'    ~[ ass ⊙ ∘e r (ι2.nat ×/sq.π/₁) ⊙ assˢ ]∎
                ×/sq.π/₁ ℂ.∘ ι2.fnc ℂ.∘ G.ₐ h' ∎
              aux₂ : ×/sq.π/₂ ℂ.∘ ι2.fnc ℂ.∘ G.ₐ h ℂ.~ ×/sq.π/₂ ℂ.∘ ι2.fnc ℂ.∘ G.ₐ h'
              aux₂ = ~proof
                ×/sq.π/₂ ℂ.∘  ι2.fnc ℂ.∘ G.ₐ h          ~[ ass ⊙ ∘e r (ι2.nat ×/sq.π/₂ ˢ) ⊙ assˢ ] /
                ι2.fnc ℂ.∘ G○F.ₐ ×/sq.π/₂ ℂ.∘ G.ₐ h     ~[ ∘e (G.∘∘ pf₂) r ] /
                ι2.fnc ℂ.∘ G○F.ₐ ×/sq.π/₂ ℂ.∘ G.ₐ h'    ~[ ass ⊙ ∘e r (ι2.nat ×/sq.π/₂) ⊙ assˢ ]∎
                ×/sq.π/₂ ℂ.∘ ι2.fnc ℂ.∘ G.ₐ h' ∎

      Fpb : 𝔻.is-pb-square (𝔻.mksq (F.sq/ sq/))
      Fpb = record
          { ⟨_,_⟩[_] = unv
          ; ×/tr₁ = tr₁
          ; ×/tr₂ = tr₂
          ; ×/uq = uq
          }
          where open ecategory-aux-only 𝔻
    --end pres-pullbacks

    pres-pb : preserves-pullbacks F
    pres-pb = record
      { pres-pbsq-pf = Fpb
      }
      where open pres-pullbacks
  -- end adj-eqv-pres-fin-lim
  
  pres-fin-lim : is-adj-equivalence-pair F G → preserves-fin-limits F
  pres-fin-lim adjeqv = record
    { prestrm = pres-term
    ; presprd = pres-prods
    ; preseql = pres-eql
    ; prespb = pres-pb
    }
    where open adj-eqv-pres-fin-lim adjeqv


  module eqv-pres-reg-epis (adjeqv : is-adj-equivalence-pair F G)
                           {A B : ℂ.Obj}{f : || ℂ.Hom A B ||}(repi : ℂ.is-regular-epi f) where
    open is-adj-equivalence-pair adjeqv
    private module f = ℂ.is-regular-epi repi

    unv-pf : {C : 𝔻.Obj}{g : || 𝔻.Hom (F.FObj A) C ||}(pf : g 𝔻.∘ F.ₐ f.rel₁ 𝔻.~ g 𝔻.∘ F.ₐ f.rel₂)
                → (G.ₐ g ℂ.∘ ι2.fnc⁻¹) ℂ.∘ f.rel₁ ℂ.~ (G.ₐ g ℂ.∘ ι2.fnc⁻¹) ℂ.∘ f.rel₂
    unv-pf {C} {g} pf = ~proof
      (G.ₐ g ℂ.∘ ι2.fnc⁻¹) ℂ.∘ f.rel₁                 ~[ assˢ ⊙ ∘e (ι2.nat⁻¹ f.rel₁) r ] /
      G.ₐ g ℂ.∘ G○F.ₐ f.rel₁ ℂ.∘ ι2.fnc⁻¹ {f.relOb}   ~[ ass ⊙ ∘e r (G.∘∘ pf) ⊙ assˢ ] /
      G.ₐ g ℂ.∘ G○F.ₐ f.rel₂ ℂ.∘ ι2.fnc⁻¹ {f.relOb}   ~[ ∘e (ι2.nat⁻¹ f.rel₂ ˢ) r ⊙ ass ]∎
      (G.ₐ g ℂ.∘ ι2.fnc⁻¹) ℂ.∘ f.rel₂ ∎
                      where open ecategory-aux-only ℂ
    unv : {C : 𝔻.Obj}(g : || 𝔻.Hom (F.FObj A) C ||)
             → g 𝔻.∘ F.ₐ f.rel₁ 𝔻.~ g 𝔻.∘ F.ₐ f.rel₂
               → || 𝔻.Hom (F.FObj B) C ||
    unv {C} g pf = ι1.fnc 𝔻.∘ F.ₐ (f.univ (G.ₐ g ℂ.∘ ι2.fnc⁻¹ {A}) (unv-pf pf))

    tr : {C : 𝔻.Obj}{g : || 𝔻.Hom (F.FObj A) C ||}(pf : g 𝔻.∘ F.ₐ f.rel₁ 𝔻.~ g 𝔻.∘ F.ₐ f.rel₂)
                → unv g pf 𝔻.∘ F.ₐ f 𝔻.~ g
    tr {C} {g} pf = Gfaith.pf (~proof
      G.ₐ (unv g pf 𝔻.∘ F.ₐ f)                         ~[ G.ext 𝔻assˢ ⊙ G.∘ax-rfˢ ⊙ ∘e G.∘ax-rfˢ r ] /
      G.ₐ ι1.fnc ℂ.∘ G○F.ₐ (f.univ (G.ₐ g ℂ.∘ ι2.fnc⁻¹ {A}) (unv-pf pf)) ℂ.∘ G○F.ₐ f
                                                       ~[ ∘e (G○F.∘∘ (f.univ-eq (unv-pf pf))) r ] /
      G.ₐ ι1.fnc ℂ.∘ G○F.ₐ (G.ₐ g) ℂ.∘ G○F.ₐ (ι2.fnc⁻¹ {A})
                                                       ~[ ass ⊙ ∘e r (G.∘∘ (ι1.nat g)) ⊙ assˢ ] /
      G.ₐ g ℂ.∘ G.ₐ ι1.fnc ℂ.∘ G○F.ₐ (ι2.fnc⁻¹ {A})     ~[ ridgg r (G.∘ax trid₁ ⊙ G.id) ]∎
      G.ₐ g ∎)
                  where Geqv : is-equivalence G
                        Geqv = record { inv = F ; iseqvp = inv-is-eqv (adjeqvp2eqvp adjeqv) }
                        module Gfaith = is-faithful (G.eqv-is-faith Geqv) renaming (faith-pf to pf)
                        open ecategory-aux-only ℂ
                        open ecategory-aux-only 𝔻 using () renaming (assˢ to 𝔻assˢ)

    isepi : {C : 𝔻.Obj}{g g' : || 𝔻.Hom (F.FObj B) C ||}
               → g 𝔻.∘ F.ₐ f 𝔻.~ g' 𝔻.∘ F.ₐ f → g 𝔻.~ g'
    isepi {C} {g} {g'} pf = Gfaith.pf (~proof
      G.ₐ g                               ~[ ridggˢ r ι2.iddom ⊙ ass ] /
      (G.ₐ g ℂ.∘ ι2.fnc⁻¹) ℂ.∘ ι2.fnc      ~[ ∘e r aux ] /
      (G.ₐ g' ℂ.∘ ι2.fnc⁻¹) ℂ.∘ ι2.fnc     ~[ assˢ ⊙ ridgg r ι2.iddom ]∎
      G.ₐ g' ∎)
                          where Geqv : is-equivalence G
                                Geqv = record { inv = F ; iseqvp = inv-is-eqv (adjeqvp2eqvp adjeqv) }
                                module Gfaith = is-faithful (G.eqv-is-faith Geqv) renaming (faith-pf to pf)
                                open ecategory-aux-only ℂ
                                --open ecategory-aux-only  using () renaming (assˢ to 𝔻assˢ; _ˢ to _ˢ𝔻)
                                aux : G.ₐ g ℂ.∘ ι2.fnc⁻¹ ℂ.~ G.ₐ g' ℂ.∘ ι2.fnc⁻¹
                                aux = f.epi-pf (~proof
                                  (G.ₐ g ℂ.∘ ι2.fnc⁻¹) ℂ.∘ f        ~[ assˢ ⊙ ∘e (ι2.nat⁻¹ f) r ] /
                                  G.ₐ g ℂ.∘ G○F.ₐ f ℂ.∘ ι2.fnc⁻¹    ~[ ass ⊙ ∘e r (G.∘∘ pf) ⊙ assˢ ] /
                                  G.ₐ g' ℂ.∘ G○F.ₐ f ℂ.∘ ι2.fnc⁻¹   ~[ ∘e (ι2.nat⁻¹ f ˢ) r ⊙ ass ]∎
                                  (G.ₐ g' ℂ.∘ ι2.fnc⁻¹) ℂ.∘ f ∎)

    Frepi : 𝔻.is-regular-epi (F.ₐ f)
    Frepi = record
      { relOb = F.ₒ f.relOb
      ; rel₁ = F.ₐ f.rel₁
      ; rel₂ = F.ₐ f.rel₂
      ; coeq = record
             { eq = F.∘∘ f.eq
             ; univ = unv
             ; univ-eq = tr
             ; uniq = record
                    { epi-pf = isepi
                    }
             }
      }

  --end eqv-pres-reg-epis
  
  pres-repi : is-adj-equivalence-pair F G → preserves-regular-epis F
  pres-repi adjeqv = record
    { pres-repi-pf = Frepi
    }
    where open eqv-pres-reg-epis adjeqv

  isexact : is-adj-equivalence-pair F G → is-exact-functor F
  isexact adjeqv = record
    { presfl = pres-fin-lim adjeqv
    ; presre = pres-repi adjeqv
    }

-- end equivalence-props
