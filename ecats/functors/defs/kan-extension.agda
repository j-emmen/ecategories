{-# OPTIONS --without-K #-}

module ecats.functors.defs.kan-extension where

open import tt-basics.setoids hiding (||_||;_⇒_)
open import ecats.basic-defs.ecat-def&not
open import ecats.basic-defs.initial
open import ecats.functors.defs.efunctor-d&n
open import ecats.functors.defs.natural-transformation
open import ecats.functors.defs.natural-iso
open import ecats.functors.defs.adjunction
open import ecats.constructions.functor-ecat
open import ecats.constructions.comma-ecat

module local-kan-extension-defs {ℓₒ₁ ℓₐ₁ ℓ~₁}{𝔸 : ecategoryₗₑᵥ ℓₒ₁ ℓₐ₁ ℓ~₁}
                                {ℓₒ₂ ℓₐ₂ ℓ~₂}{𝔹 : ecategoryₗₑᵥ ℓₒ₂ ℓₐ₂ ℓ~₂}(K : efunctorₗₑᵥ 𝔸 𝔹)
                                {ℓₒ ℓₐ ℓ~}{𝕏 : ecategoryₗₑᵥ ℓₒ ℓₐ ℓ~}(F : efunctorₗₑᵥ 𝔸 𝕏)
                                where
  private
    module 𝔸 = ecat 𝔸
    module 𝔹 = ecat 𝔹
    module 𝕏 = ecat 𝕏
    module K = efctr K
    module F = efctr F
    module [𝔸,𝕏] = ecat [ 𝔸 , 𝕏 ]ᶜᵃᵗ
    module [𝔹,𝕏] = ecat [ 𝔹 , 𝕏 ]ᶜᵃᵗ

  record is-loc-left-kan-extension (Lan : efunctorₗₑᵥ 𝔹 𝕏)(η : F ⇒ Lan ○ K)
                                   : Set (𝔸.ℓₙₒ~ ⊔ 𝔹.ℓₐₗₗ ⊔ 𝕏.ℓₐₗₗ)
                                   where
    private
      module Lan = efctr Lan
      module η = natural-transformation η
    infix 90 _+η
    _+η : {G : efunctorₗₑᵥ 𝔹 𝕏} → Lan ⇒ G → F ⇒ G ○ K
    α +η = natt-vcmp (natt-hcmp α natt-id) η
    field
      nt : {G : efunctorₗₑᵥ 𝔹 𝕏} → F ⇒ G ○ K → Lan ⇒ G
      tr : {G : efunctorₗₑᵥ 𝔹 𝕏}(α : F ⇒ G ○ K) → nt {G} α +η [𝔸,𝕏].~ α
      +η-je : {G : efunctorₗₑᵥ 𝔹 𝕏}(β β' : Lan ⇒ G)
                  → β +η [𝔸,𝕏].~ β' +η → β [𝔹,𝕏].~ β'
    trˢ : {G : efunctorₗₑᵥ 𝔹 𝕏}(α : F ⇒ G ○ K) → α [𝔸,𝕏].~ nt {G} α +η
    trˢ α A = tr α A ˢ
            where open ecategory-aux-only 𝕏 using (_ˢ)
    uq :  {G : efunctorₗₑᵥ 𝔹 𝕏}{α : F ⇒ G ○ K}(β : Lan ⇒ G) → β +η [𝔸,𝕏].~ α → β [𝔹,𝕏].~ nt α
    uq {G} {α} β eq = +η-je β (nt α) ( λ A →
                            (β.fnc 𝕏.∘ Lan.ₐ (𝔹.idar (K.ₒ A))) 𝕏.∘ η.fnc {A}
                                                                               ~[ eq A ⊙ tr α A ˢ ]
                            (ntα.fnc {K.ₒ A} 𝕏.∘ Lan.ₐ (𝔹.idar (K.ₒ A))) 𝕏.∘ η.fnc {A} )
                    where module α = natural-transformation α
                          module β = natural-transformation β
                          module ntα = natural-transformation (nt {G} α)
                          open ecategory-aux-only 𝕏
    uqˢ :  {G : efunctorₗₑᵥ 𝔹 𝕏}{α : F ⇒ G ○ K}(β : Lan ⇒ G) → β +η [𝔸,𝕏].~ α → nt α [𝔹,𝕏].~ β
    uqˢ {G} {α} β eq = +η-je (nt α) β (λ A → tr α A ⊙ eq A ˢ)
                     where open ecategory-aux-only 𝕏 using (_⊙_; _ˢ)


  record is-loc-right-kan-extension (Ran : efunctorₗₑᵥ 𝔹 𝕏)(ε : Ran ○ K ⇒ F)
                                    : Set (𝔸.ℓₙₒ~ ⊔ 𝔹.ℓₐₗₗ ⊔ 𝕏.ℓₐₗₗ)
                                    where
    ε+ : {G : efunctorₗₑᵥ 𝔹 𝕏} → G ⇒ Ran → G ○ K ⇒ F
    ε+ α = natt-vcmp ε (natt-hcmp α natt-id)
    field
      nt : {G : efunctorₗₑᵥ 𝔹 𝕏} → G ○ K ⇒ F → G ⇒ Ran
      tr : {G : efunctorₗₑᵥ 𝔹 𝕏}(α : G ○ K ⇒ F) → ε+ (nt {G} α) [𝔸,𝕏].~ α
      ε+-je : {G : efunctorₗₑᵥ 𝔹 𝕏}(α α' : G ⇒ Ran)
                  → ε+ α [𝔸,𝕏].~ ε+ α' → α [𝔹,𝕏].~ α'
    trˢ : {G : efunctorₗₑᵥ 𝔹 𝕏}(α : G ○ K ⇒ F) → α [𝔸,𝕏].~ ε+ (nt {G} α)
    trˢ α A = tr α A ˢ
            where open ecategory-aux-only 𝕏 using (_ˢ)
    uq :  {G : efunctorₗₑᵥ 𝔹 𝕏}{α : G ○ K ⇒ F}(β : G ⇒ Ran) → ε+ β [𝔸,𝕏].~ α → β [𝔹,𝕏].~ nt α
    uq {α = α} β eq = ε+-je β (nt α) (λ A → eq A ⊙ tr α A ˢ)
                    where open ecategory-aux-only 𝕏 using (_⊙_; _ˢ)
    uqˢ : {G : efunctorₗₑᵥ 𝔹 𝕏}{α : G ○ K ⇒ F}(β : G ⇒ Ran) → ε+ β [𝔸,𝕏].~ α → nt α [𝔹,𝕏].~ β
    uqˢ {α = α} β eq = ε+-je (nt α) β (λ A → tr α A ⊙ eq A ˢ)
                     where open ecategory-aux-only 𝕏 using (_⊙_; _ˢ)
-- end local-kan-extension-defs



record has-loc-left-kan-extension {ℓₒ₁ ℓₐ₁ ℓ~₁}{𝔸 : ecategoryₗₑᵥ ℓₒ₁ ℓₐ₁ ℓ~₁}
                                  {ℓₒ₂ ℓₐ₂ ℓ~₂}{𝔹 : ecategoryₗₑᵥ ℓₒ₂ ℓₐ₂ ℓ~₂}(K : efunctorₗₑᵥ 𝔸 𝔹)
                                  {ℓₒ ℓₐ ℓ~}{𝕏 : ecategoryₗₑᵥ ℓₒ ℓₐ ℓ~}(F : efunctorₗₑᵥ 𝔸 𝕏)
                                  : Set (ecat.ℓₙₒ~ 𝔸 ⊔ ecat.ℓₐₗₗ 𝔹 ⊔ ecat.ℓₐₗₗ 𝕏)
                                  where
  open local-kan-extension-defs K F
  field
    Lan : efunctorₗₑᵥ 𝔹 𝕏
    η : F ⇒ Lan ○ K
    isllke : is-loc-left-kan-extension Lan η
  open is-loc-left-kan-extension isllke using (_+η) public
  module unv = is-loc-left-kan-extension isllke hiding (_+η)


record has-loc-right-kan-extension {ℓₒ₁ ℓₐ₁ ℓ~₁}{𝔸 : ecategoryₗₑᵥ ℓₒ₁ ℓₐ₁ ℓ~₁}
                                   {ℓₒ₂ ℓₐ₂ ℓ~₂}{𝔹 : ecategoryₗₑᵥ ℓₒ₂ ℓₐ₂ ℓ~₂}(K : efunctorₗₑᵥ 𝔸 𝔹)
                                   {ℓₒ ℓₐ ℓ~}{𝕏 : ecategoryₗₑᵥ ℓₒ ℓₐ ℓ~}(F : efunctorₗₑᵥ 𝔸 𝕏)
                                   : Set (ecat.ℓₙₒ~ 𝔸 ⊔ ecat.ℓₐₗₗ 𝔹 ⊔ ecat.ℓₐₗₗ 𝕏)
                                   where
  open local-kan-extension-defs K F
  field
    Ran : efunctorₗₑᵥ 𝔹 𝕏
    ε : Ran ○ K ⇒ F
    islrke : is-loc-right-kan-extension Ran ε
  module unv = is-loc-right-kan-extension islrke


record has-glob-left-kan-extension {ℓₒ₁ ℓₐ₁ ℓ~₁}{𝔸 : ecategoryₗₑᵥ ℓₒ₁ ℓₐ₁ ℓ~₁}
                                   {ℓₒ₂ ℓₐ₂ ℓ~₂}{𝔹 : ecategoryₗₑᵥ ℓₒ₂ ℓₐ₂ ℓ~₂}
                                   (K : efunctorₗₑᵥ 𝔸 𝔹){ℓₒ ℓₐ ℓ~}(𝕏 : ecategoryₗₑᵥ ℓₒ ℓₐ ℓ~)
                                   : Set (ecat.ℓₐₗₗ 𝔸 ⊔ ecat.ℓₐₗₗ 𝔹 ⊔ ecat.ℓₐₗₗ 𝕏)
                                   where
  field
    Lan : efunctorₗₑᵥ [ 𝔸 , 𝕏 ]ᶜᵃᵗ [ 𝔹 , 𝕏 ]ᶜᵃᵗ
    isadj : Lan ⊣ fctr-precmp K 𝕏
  open adjunction-εη isadj public


record has-glob-right-kan-extension {ℓₒ₁ ℓₐ₁ ℓ~₁}{𝔸 : ecategoryₗₑᵥ ℓₒ₁ ℓₐ₁ ℓ~₁}
                                    {ℓₒ₂ ℓₐ₂ ℓ~₂}{𝔹 : ecategoryₗₑᵥ ℓₒ₂ ℓₐ₂ ℓ~₂}
                                    (K : efunctorₗₑᵥ 𝔸 𝔹){ℓₒ ℓₐ ℓ~}(𝕏 : ecategoryₗₑᵥ ℓₒ ℓₐ ℓ~)
                                    : Set (ecat.ℓₐₗₗ 𝔸 ⊔ ecat.ℓₐₗₗ 𝔹 ⊔ ecat.ℓₐₗₗ 𝕏)
                                    where
  field
    Ran : efunctorₗₑᵥ [ 𝔸 , 𝕏 ]ᶜᵃᵗ [ 𝔹 , 𝕏 ]ᶜᵃᵗ
    isadj : fctr-precmp K 𝕏 ⊣ Ran
  open adjunction-εη isadj public


module everywhere-local-is-global-kan-extension {ℓₒ₁ ℓₐ₁ ℓ~₁}{𝔸 : ecategoryₗₑᵥ ℓₒ₁ ℓₐ₁ ℓ~₁}
                                                {ℓₒ₂ ℓₐ₂ ℓ~₂}{𝔹 : ecategoryₗₑᵥ ℓₒ₂ ℓₐ₂ ℓ~₂}
                                                (K : efunctorₗₑᵥ 𝔸 𝔹)
                                                {ℓₒ ℓₐ ℓ~}(𝕏 : ecategoryₗₑᵥ ℓₒ ℓₐ ℓ~)
                                                where
  private
    module 𝔸 = ecat 𝔸
    module 𝔹 = ecat 𝔹
    module 𝕏 = ecat 𝕏
    module [𝔸,𝕏] = ecat [ 𝔸 , 𝕏 ]ᶜᵃᵗ
    module [𝔹,𝕏] = ecat [ 𝔹 , 𝕏 ]ᶜᵃᵗ
    module K = efctr K
    K* : efunctorₗₑᵥ [ 𝔹 , 𝕏 ]ᶜᵃᵗ [ 𝔸 , 𝕏 ]ᶜᵃᵗ
    K* = fctr-precmp K 𝕏
    module K* = efctr K*
    module [𝔹,𝕏]↓K* (F : [𝔸,𝕏].Obj) where
      open ecat (F ₒ↓ K*) public
      open slice-funct-ecat K* F public
      open initial-defs (F ₒ↓ K*) public

  module left-adjoint-from-locLan (locLan : (F : efunctorₗₑᵥ 𝔸 𝕏) → has-loc-left-kan-extension K F)
                                  where
    private
      module lL (F : efunctorₗₑᵥ 𝔸 𝕏) where
        open has-loc-left-kan-extension (locLan F) public
        module Lan = efunctor-aux Lan
        module η = natural-transformation η

    module gLar {F G : [𝔸,𝕏].Obj}(γ : F ⇒ G) where
      fill : F ⇒ (lL.Lan G) ○ K
      fill = natt-vcmp (lL.η G) γ
      module fill = natural-transformation fill
      nt : lL.Lan F ⇒ lL.Lan G
      nt = lL.unv.nt F {lL.Lan G} fill
      module nt = natural-transformation nt
    -- end gLar

    gL : efunctorₗₑᵥ [ 𝔸 , 𝕏 ]ᶜᵃᵗ [ 𝔹 , 𝕏 ]ᶜᵃᵗ
    gL = record
      { FObj = lL.Lan
      ; FHom = gLar.nt
      ; isF = record
            { ext = λ {F} {G} {γ} {γ'} eq → lL.unv.uq F (gLar.nt γ) (ext-aux γ γ' eq)
            ; id = λ {F} → lL.unv.uqˢ F ([𝔹,𝕏].idar (lL.Lan F)) (id-aux F)
            ; cmp = λ {F} γ γ' → lL.unv.uq F (gLar.nt γ' [𝔹,𝕏].∘ gLar.nt γ) (cmp-aux γ γ')
            }
      }
      where ext-aux : {F G : [𝔸,𝕏].Obj}(γ γ' : || [𝔸,𝕏].Hom F G ||)
                         → γ [𝔸,𝕏].~ γ' → lL._+η F (gLar.nt γ) [𝔸,𝕏].~ gLar.fill γ'
            ext-aux {F} {G} γ γ' eq A = ~proof
              Lγ+η.fnc                     ~[ F.unv.tr (gLar.fill γ) A ] /
              G.η.fnc 𝕏.∘ γ.fnc           ~[ ∘e (eq A) r ]∎
              G.η.fnc 𝕏.∘ γ'.fnc ∎
                                      where module F where
                                              open efctr F public
                                              open lL F public
                                            module G where
                                              open efctr G public
                                              open lL G public
                                            module γ = natural-transformation γ
                                            module γ' = natural-transformation γ'
                                            module Lγ = natural-transformation (gLar.nt γ)
                                            module Lγ+η = natural-transformation (gLar.nt γ F.+η)
                                            open ecategory-aux-only 𝕏

            id-aux : (F : [𝔸,𝕏].Obj)
                        → lL._+η F ([𝔹,𝕏].idar (lL.Lan F)) NatTr.~ gLar.fill ([𝔸,𝕏].idar F)
            id-aux F A = lidgg ridˢ (lidgen F.Lan.id)
                       where open ecategory-aux-only 𝕏
                             module F where
                               open efctr F public
                               open lL F public

            cmp-aux : {F G H : [𝔸,𝕏].Obj}(γ : || [𝔸,𝕏].Hom F G ||)(γ' : || [𝔸,𝕏].Hom G H ||)
                         → lL._+η F (gLar.nt γ' [𝔹,𝕏].∘ gLar.nt γ) NatTr.~ gLar.fill (γ' [𝔸,𝕏].∘ γ)
            cmp-aux {F} {G} {H} γ γ' A = ~proof
              F[LγLγ']η.fnc {A}
                          ~[ ∘e r assˢ ⊙ assˢ ] /
              Lγ'.fnc {K.ₒ A} 𝕏.∘ (Lγ.fnc {K.ₒ A} 𝕏.∘ F.Lan.ₐ (𝔹.idar (K.ₒ A))) 𝕏.∘ F.η.fnc {A}
                          ~[ ∘e (lidggˢ (F.unv.tr (gLar.fill γ) A) G.Lan.id ⊙ ass) r ⊙ ass ] /
              (Lγ'.fnc {K.ₒ A} 𝕏.∘ G.Lan.ₐ (𝔹.idar (K.ₒ A)) 𝕏.∘ G.η.fnc {A}) 𝕏.∘ γ.fnc {A}
                          ~[ ∘e r (ass ⊙ G.unv.tr (gLar.fill γ') A) ⊙ assˢ ]∎
              H.η.fnc 𝕏.∘ γ'.fnc 𝕏.∘ γ.fnc {A} ∎
                                      where open ecategory-aux-only 𝕏
                                            module F where
                                              open efctr F public
                                              open lL F public
                                            module G where
                                              open efctr G public
                                              open lL G public
                                            module H where
                                              open efctr H public
                                              open lL H public
                                            module γ = natural-transformation γ
                                            module γ' = natural-transformation γ'
                                            module Lγ = natural-transformation (gLar.nt γ)
                                            module Lγ' = natural-transformation (gLar.nt γ')
                                            module F[LγLγ']η = natural-transformation (lL._+η F (gLar.nt γ' [𝔹,𝕏].∘ gLar.nt γ))
            open ecategory-aux-only [ 𝔹 , 𝕏 ]ᶜᵃᵗ

    private
      module gL where
        open efunctor-aux gL public
        module ₒ (F : [𝔸,𝕏].Obj) = efctr (ₒ F)
        module ₐ {F G : [𝔸,𝕏].Obj}(γ : F ⇒ G) = natural-transformation (ₐ γ)
    open adjunction-as-universal-props gL K*
    
    ηnt : natural-transformation IdF (K* ○ gL)
    ηnt = record
      { fnc = λ {F} → lL.η F
      ; nat = nat
      }
      where open natural-trans-defs IdF (K* ○ gL)
            nat : is-natural (λ {F} → lL.η F)
            nat {F} {G} γ A = ~proof
              G.η.fnc 𝕏.∘ γ.fnc {A}                           ~[ F.unv.trˢ (gLar.fill γ) A ⊙ assˢ ] /
              gL.ₐ.fnc γ {K.ₒ A} 𝕏.∘ F.Lan.ₐ (𝔹.idar (K.ₒ A)) 𝕏.∘ F.η.fnc {A}
                                                               ~[ ∘e (lidgg r F.Lan.id) r ]∎
              gL.ₐ.fnc γ {K.ₒ A} 𝕏.∘ F.η.fnc {A} ∎
                            where module F = lL F
                                  module G = lL G
                                  module γ = natural-transformation γ
                                  open ecategory-aux-only 𝕏

    ηin : (F : [𝔸,𝕏].Obj) → [𝔹,𝕏]↓K*.is-initial F (RLnt2sl ηnt F)
    ηin F = record
      { ø = un
      ; øuq = unuq
      }
      where module F = lL F
            module F↓K* = [𝔹,𝕏]↓K* F
            module η = F↓K*.ₒ (RLnt2sl ηnt F)
            un : (Gγ : F↓K*.Obj) → || F↓K*.Hom (RLnt2sl ηnt F) Gγ ||
            un Gγ = record
              { arR = uar -- F.unv.tr Gγ.ar A
              ; tr = λ A → ~proof
                   uar.fnc {K.ₒ A} 𝕏.∘ F.η.fnc {A}      ~[ ∘e (lidggˢ r F.Lan.id) r ] /
                   uar.fnc {K.ₒ A} 𝕏.∘ F.Lan.ₐ (𝔹.idar (K.ₒ A)) 𝕏.∘ F.η.fnc {A}
                                                         ~[ ass ⊙ F.unv.tr Gγ.ar A ]∎
                   Gγ.ar.fnc {A} ∎
              }
              where module Gγ where
                      open F↓K*.ₒ Gγ public
                      module ar = natural-transformation ar
                    uar : || [𝔹,𝕏].Hom F.Lan Gγ.R ||
                    uar = F.unv.nt Gγ.ar
                    module uar = natural-transformation uar
                    open ecategory-aux-only 𝕏
            unuq : {Gγ : F↓K*.Obj}(φ : || F↓K*.Hom (RLnt2sl ηnt F) Gγ ||)
                      → φ F↓K*.~  un Gγ
            unuq {Gγ} φ = F.unv.uq {α = Gγ.ar}
                                   φ.arR
                                   (λ A → ~proof
                                        φ.+η.fnc {A}                 ~[ ∘e r (ridgg r F.Lan.id) ] /
                                        φ.arR.fnc 𝕏.∘ F.η.fnc {A}    ~[ φ.tr A ]∎
                                        Gγ.ar.fnc {A} ∎)
                        where module Gγ where
                                open F↓K*.ₒ Gγ public
                                module ar = natural-transformation ar
                              module φ where
                                open F↓K*.ₐ φ public
                                module arR = natural-transformation arR
                                module +η = natural-transformation (arR F.+η)
                              open ecategory-aux-only 𝕏

    isladj : gL ⊣ K*
    isladj = unvη→adj ηnt ηin
  -- end left-adjoint-from-locLan


  evwh-loc→glob : (locLan : (F : efunctorₗₑᵥ 𝔸 𝕏) → has-loc-left-kan-extension K F)
                          → has-glob-left-kan-extension K 𝕏
  evwh-loc→glob locLan = record
    { Lan = gL
    ; isadj = isladj
    }
    where open left-adjoint-from-locLan locLan
-- end everywhere-local-is-global-kan-extension



evwh-local-is-global-kan-ext : {ℓₒ₁ ℓₐ₁ ℓ~₁ : Level}{𝔸 : ecategoryₗₑᵥ ℓₒ₁ ℓₐ₁ ℓ~₁}
                               {ℓₒ₂ ℓₐ₂ ℓ~₂ : Level}{𝔹 : ecategoryₗₑᵥ ℓₒ₂ ℓₐ₂ ℓ~₂}(K : efunctorₗₑᵥ 𝔸 𝔹)
                               {ℓₒ ℓₐ ℓ~ : Level}(𝕏 : ecategoryₗₑᵥ ℓₒ ℓₐ ℓ~)
                               (locLan : (F : efunctorₗₑᵥ 𝔸 𝕏) → has-loc-left-kan-extension K F)
                                 → has-glob-left-kan-extension K 𝕏
evwh-local-is-global-kan-ext K 𝕏 = evwh-loc→glob
                                  where open everywhere-local-is-global-kan-extension K 𝕏
