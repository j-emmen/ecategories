{-# OPTIONS --without-K #-}

module ecats.constructions.kleisli where

open import ecats.basic-defs.ecat-def&not
open import ecats.functors.defs.efunctor-d&n
open import ecats.functors.defs.basic-defs
open import ecats.functors.defs.natural-transformation
open import ecats.functors.defs.natural-iso
open import ecats.basic-defs.isomorphism
open import ecats.basic-props.isomorphism
open import ecats.functors.defs.adjunction
open import ecats.functors.defs.monad
open import ecats.functors.props.monad


----------------------------
-- Klesli category
----------------------------

KlCat : {ℓₒ ℓₐ ℓ~ : Level}{ℂ : ecategoryₗₑᵥ ℓₒ ℓₐ ℓ~}
            → monad-on ℂ → ecategoryₗₑᵥ (ecat.ℓₒ ℂ) (ecat.ℓₐᵣᵣ ℂ) (ecat.ℓ~ ℂ)
KlCat {ℂ = ℂ} M = record
  { Obj = ℂ.Obj
  ; Hom = λ X Y → ℂ.Hom X (M.ₒ Y)
  ; isecat = record
               { _∘_ = kl-cmp
               ; idar = kl-id
               ; ∘ext = λ f f' g g' eqf eqg →
               M.μ.ar ∘ M.ₐ g ∘ f             ~[ ∘e (∘e eqf (M.fc.ext eqg)) r ]
               M.μ.ar ℂ.∘ M.ₐ g' ℂ.∘ f'
               ; lidax = λ {_} {Y} f →
               M.μ.ar ∘ M.ₐ M.η.ar ∘ f        ~[ ass ⊙ lidgg r (M.ax-Tη Y) ]
               f
               ; ridax = λ {_} {Y} f → ~proof
               M.μ.ar ∘ M.ₐ f ∘ M.η.ar        ~[ ∘e (M.η.natˢ f) r ] /
               M.μ.ar ∘ M.η.ar ∘ f            ~[ ass ⊙ lidgg r (M.ax-ηT Y) ]∎
               f ∎
               ; assoc = λ {X} {Y} {Z} {W} f g h → ~proof
           M.μ.ar ∘ M.ₐ h ∘ M.μ.ar ∘ M.ₐ g ∘ f               ~[ ∘e (ass ⊙ ∘e r (M.μ.natˢ h) ⊙ assˢ) r ] /
           M.μ.ar ∘ M.μ.ar ∘ M.ₐ (M.ₐ h) ∘ M.ₐ g ∘ f          ~[ ass ⊙ ∘e r (M.ax-μ W) ⊙ assˢ ] /
           M.μ.ar ∘ M.ₐ M.μ.ar ∘ M.ₐ (M.ₐ h) ∘ M.ₐ g ∘ f      ~[ ∘e (∘e (ass ⊙ ∘e r M.fc.∘ax-rf) r) r ] /
           M.μ.ar ∘ M.ₐ M.μ.ar ∘ M.ₐ (M.ₐ h ∘ g) ∘ f          ~[ ∘e (ass ⊙ ∘e r M.fc.∘ax-rf) r ]∎
           M.μ.ar ∘ M.ₐ (M.μ.ar ∘ M.ₐ h ∘ g) ∘ f ∎
               }
  }
  where open ecategory-aux ℂ
        module ℂ where
          open ecat ℂ public
          open iso-defs ℂ public
          open iso-props ℂ public
        module M where
          open monad-on M public
          open efunctorₗₑᵥ fc using (ₒ ; ₐ) public
        kl-cmp : {X Y Z : ℂ.Obj} → || ℂ.Hom Y (M.ₒ Z) || → || ℂ.Hom X (M.ₒ Y) ||
                    → || ℂ.Hom X (M.ₒ Z) ||
        kl-cmp {X} {Y} {Z} g f = M.μ.ar ℂ.∘ M.ₐ g ℂ.∘ f
        kl-id : (X : ℂ.Obj) → || ℂ.Hom X (M.ₒ X) ||
        kl-id X = M.η.ar {X}


-----------------
-- Right functor
-----------------

Kl-U : {ℓₒ ℓₐ ℓ~ : Level}{ℂ : ecategoryₗₑᵥ ℓₒ ℓₐ ℓ~}(M : monad-on ℂ)
           → efunctorₗₑᵥ (KlCat M) ℂ
Kl-U {ℂ = ℂ} M = record
  { FObj = M.ₒ
  ; FHom = λ f → M.μ.ar ℂ.∘ M.ₐ f
  ; isF = record
        { ext = λ {_} {_} {f} {f'} eq →
        M.μ.ar ∘ M.ₐ f     ~[ ∘e (M.fc.ext eq) r ]
        M.μ.ar ∘ M.ₐ f'
        ; id = λ {X} →
        M.μ.ar ∘ M.ₐ M.η.ar         ~[ M.ax-Tη X ]
        ℂ.idar (M.ₒ X)
        ; cmp = λ f g → ~proof
        (M.μ.ar ∘ M.ₐ g) ∘ M.μ.ar ∘ M.ₐ f       ~[ assˢ ⊙ ∘e (ass ⊙ ∘e r (M.μ.natˢ g) ⊙ assˢ) r ] /
        M.μ.ar ∘ M.μ.ar ∘ M.².ₐ g ∘ M.ₐ f       ~[ ass ⊙ ∘e M.fc.∘ax-rf (M.ax-μ _) ⊙ assˢ ] /
        M.μ.ar ∘ M.ₐ M.μ.ar ∘ M.ₐ (M.ₐ g ∘ f)   ~[ ∘e M.fc.∘ax-rf r ]∎
        M.μ.ar ∘ M.ₐ (M.μ.ar ∘ M.ₐ g ∘ f) ∎
        }
  }
  where open ecategory-aux ℂ
        module ℂ = ecat ℂ
        module M where
          open monad-on M public
          open efunctorₗₑᵥ fc using (ₒ ; ₐ) public


----------------
-- Left functor
----------------

Kl-F : {ℓₒ ℓₐ ℓ~ : Level}{ℂ : ecategoryₗₑᵥ ℓₒ ℓₐ ℓ~}(M : monad-on ℂ)
           → efunctorₗₑᵥ ℂ (KlCat M)
Kl-F {ℂ = ℂ} M = record
  { FObj = λ X → X
  ; FHom = λ f → M.η.ar ℂ.∘ f
  ; isF = record
        { ext = λ {_} {_} {f} {f'} eq →
  M.η.ar ∘ f      ~[ ∘e eq r ]      M.η.ar ∘ f'
        ; id = λ {X} →
  M.η.ar ∘ ℂ.idar X     ~[ rid ]     M.η.ar
        ; cmp = λ f g → ~proof
  M.μ.ar ∘ M.ₐ (M.η.ar ∘ g) ∘ M.η.ar ℂ.∘ f      ~[ ∘e (∘e r M.fc.∘ax-rfˢ ⊙ assˢ) r ⊙ ass ] /
  (M.μ.ar ∘ M.ₐ M.η.ar) ∘ M.ₐ g ∘ M.η.ar ℂ.∘ f  ~[ lidgg (ass ⊙ ∘e r (M.η.natˢ g) ⊙ assˢ) (M.ax-Tη _) ]∎
  M.η.ar ∘ g ∘ f ∎
        }
  }
  where open ecategory-aux ℂ
        module ℂ = ecat ℂ
        module M where
          open monad-on M public
          open efunctorₗₑᵥ fc using (ₒ ; ₐ) public


--------------
-- Adjunction
--------------

module Kleisli-adjunction {ℓₒ ℓₐ ℓ~ : Level}{ℂ : ecategoryₗₑᵥ ℓₒ ℓₐ ℓ~}(M : monad-on ℂ) where
  private
    module ℂ = ecat ℂ
    module M where
      open monad-on M public
      open efctr fc using (ₒ; ₐ) public
    module Kl = ecat (KlCat M)
    U = Kl-U M
    F = Kl-F M
    module U = efunctor-aux U
    module F = efunctor-aux F

  η : IdF ⇒ Kl-U M ○ Kl-F M
  η = record
    { fnc = M.η.ar 
    ; nat = λ f → ~proof
    M.η.ar ∘ f                              ~[ lidggˢ (M.η.nat f) (M.ax-Tη _) ⊙ assˢ ] /
    M.μ.ar ∘ M.ₐ M.η.ar ∘ M.ₐ f ∘ M.η.ar     ~[ ∘e (ass ⊙ ∘e r M.fc.∘ax-rf) r ⊙ ass ]∎
    U.ₐ (F.ₐ f) ∘ M.η.ar ∎
    }
    where open ecategory-aux ℂ

  ε : Kl-F M ○ Kl-U M ⇒ IdF
  ε = record
    { fnc = λ {X} → ℂ.idar (M.ₒ X)
    ; nat = λ f → ~proof
    M.μ.ar ∘ M.ₐ (ℂ.idar (M.ₒ _)) ∘ M.η.ar ∘ M.μ.ar ∘ M.ₐ f
                                            ~[ ∘e (lidgg r M.fc.id) r ⊙ ass ⊙ lidgg r (M.ax-ηT _) ] /
    M.μ.ar ∘ M.ₐ f                           ~[ ridˢ ⊙ assˢ ]∎
    M.μ.ar ∘ M.ₐ f ∘ ℂ.idar (M.ₒ _) ∎
    }
    where open ecategory-aux ℂ

  private
    module η = natural-transformation η
    module ε = natural-transformation ε
  εFFη : (X : ℂ.Obj) → ε.ar {F.ₒ X}  Kl.∘ F.ₐ η.ar Kl.~ Kl.idar (F.ₒ X)
  εFFη X = M.μ.ar ∘ M.ₐ (ε.ar {X}) ∘ M.η.ar ∘ η.ar
                                            ~[ ∘e (lidgg r M.fc.id) r ⊙ ass ⊙ lidgg r (M.ax-ηT _) ]
           M.η.ar {X}
         where open ecategory-aux ℂ
  UεηU : (X : ℂ.Obj) → U.ₐ (ε.ar {X}) ℂ.∘ η.ar {U.ₒ X} ℂ.~ ℂ.idar (M.ₒ X)
  UεηU X = (M.μ.ar ∘ M.ₐ (ε.ar {X})) ∘ η.ar {M.ₒ X}
                                            ~[ (assˢ ⊙ ∘e (lidgg r M.fc.id) r ⊙ M.ax-ηT _) ]
           ℂ.idar (M.ₒ X)
         where open ecategory-aux ℂ
-- end Kleisli-adjunction


Kl-adj : {ℓₒ ℓₐ ℓ~ : Level}{ℂ : ecategoryₗₑᵥ ℓₒ ℓₐ ℓ~}(M : monad-on ℂ)
             → Kl-F M ⊣ Kl-U M
Kl-adj {ℂ = ℂ} M = record
  { ηnt = η
  ; εnt = ε
  ; trid₁ = λ {X} → εFFη X
  ; trid₂ = λ {X} → UεηU X
  }
  where open Kleisli-adjunction M




----------------------
-- Comparison functor
----------------------

module Kleisli-comparison {ℓₒ₁ ℓₐ₁ ℓ~₁ : Level}{ℂ : ecategoryₗₑᵥ ℓₒ₁ ℓₐ₁ ℓ~₁}
                          {ℓₒ₂ ℓₐ₂ ℓ~₂ : Level}{𝔻 : ecategoryₗₑᵥ ℓₒ₂ ℓₐ₂ ℓ~₂}
                          {L : efunctorₗₑᵥ ℂ 𝔻}{R : efunctorₗₑᵥ 𝔻 ℂ}
                          (L⊣R : adjunction-εη L R)
                          where
  private
    module ℂ = ecat ℂ
    module 𝔻 = ecat 𝔻
    module L = efunctor-aux L
    module R = efunctor-aux R
    module L⊣R = adjunction-εη L⊣R
    LR : efunctorₗₑᵥ 𝔻 𝔻
    LR = L ○ R
    module LR = efunctor-aux LR
    RL : monad-on ℂ
    RL = adjunction2monad-on-cat L⊣R
    module RL where
      open monad-on RL public
      open efctr fc using (ₒ; ₐ) public
    η : IdF ⇒ RL.fc
    η = L⊣R.ηnt
    module η = natural-transformation η
    ε : LR ⇒ IdF
    ε = L⊣R.εnt
    module ε = natural-transformation ε
    Kl[RL] : ecategoryₗₑᵥ ℂ.ℓₒ ℂ.ℓₐᵣᵣ ℂ.ℓ~
    Kl[RL] = KlCat RL
    module Kl[RL] = ecat Kl[RL]
    U : efunctorₗₑᵥ Kl[RL] ℂ
    U = Kl-U RL
    F : efunctorₗₑᵥ ℂ Kl[RL]
    F = Kl-F RL
    F⊣U : F ⊣ U
    F⊣U = Kl-adj RL
    module F = efunctor-aux F
    module U = efunctor-aux U
    module F⊣U = adjunction-εη F⊣U
    module UF = efunctor-aux (U ○ F)

  K : efunctorₗₑᵥ Kl[RL] 𝔻
  K = record
    { FObj = L.ₒ
    ; FHom = λ f → ε.ar {L.ₒ _} 𝔻.∘ L.ₐ f
    ; isF = record
          { ext = λ eq → ∘e (L.ext eq) r
          ; id = L⊣R.trid₁
          ; cmp = λ f g → ~proof
          (ε.ar ∘ L.ₐ g) ∘ ε.ar ∘ L.ₐ f           ~[ assˢ ⊙ ∘e (ass ⊙ ∘e r (ε.natˢ (L.ₐ g)) ⊙ assˢ) r ] /
          ε.ar ∘ ε.ar ∘ LR.ₐ (L.ₐ g) ∘ L.ₐ f      ~[ ass ⊙ ∘e L.∘ax-rf (ε.natˢ ε.ar) ⊙ assˢ ] /
          ε.ar ∘ LR.ₐ ε.ar ∘ L.ₐ (RL.ₐ g ℂ.∘ f)   ~[ ∘e L.∘ax-rf r ]∎
          ε.ar ∘ L.ₐ (g Kl[RL].∘ f) ∎
          }
    }
    where open ecategory-aux 𝔻
  private module K = efunctor-aux K

  triangR : R ○ K ≅ₐ U
  triangR = record
    { natt = record
           { fnc = λ {X} → ℂ.idar (RL.ₒ X)
           ; nat = λ _ → lidgen (ridgenˢ R.∘ax-rfˢ)
           }
    ; natt⁻¹ = record
             { fnc = λ {X} → ℂ.idar (RL.ₒ X)
             ; nat = λ _ → lidgen (ridgenˢ R.∘ax-rf)
             }
    ; isiso = λ {X} → idar-is-isopair (RL.ₒ X)
    }
    where open ecategory-aux-only ℂ
          open iso-props ℂ

  triangL : K ○ F ≅ₐ L
  triangL = record
    { natt = record
           { fnc = λ {X} → 𝔻.idar (L.ₒ X)
           ; nat = λ f → lidgen (ridgenˢ (ε.ar {L.ₒ _} ∘ L.ₐ (η.ar ℂ.∘ f)
                                                    ~[ (∘e L.∘ax-rfˢ r ⊙ ass ⊙  lidgg r L⊣R.trid₁) ]
                                          L.ₐ f))
           }
    ; natt⁻¹ = record
           { fnc = λ {X} → 𝔻.idar (L.ₒ X)
           ; nat = λ f → lidgen (ridgenˢ (L.ₐ f
                                                    ~[ ( lidggˢ r L⊣R.trid₁ ⊙ assˢ ⊙ ∘e L.∘ax-rf r) ]
                                          ε.ar {L.ₒ _} ∘ L.ₐ (η.ar ℂ.∘ f)))
           }
    ; isiso = λ {X} → record
            { iddom = lid
            ; idcod = lid
            }
    }
    where open ecategory-aux 𝔻

-- end Kleisli-comparison
