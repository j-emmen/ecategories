{-# OPTIONS --without-K #-}

module ecats.constructions.eilenberg-moore where

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
--open import ecats.constructions.functor-ecat

module algebras-for-monad-defs {ℓₒ ℓₐ ℓ~}{ℂ : ecategoryₗₑᵥ ℓₒ ℓₐ ℓ~}(M : monad-on ℂ) where
  private
    module ℂ where
      open ecat ℂ public
      open iso-defs ℂ public
      open iso-props ℂ public
    module M where
      open monad-on M public
      open efunctor-aux fc public

  record is-algebra {A : ℂ.Obj}(a : || ℂ.Hom (M.fc.ₒ A) A ||) : Set ℂ.ℓ~ where
    field
      ηeq : a ℂ.∘ M.η.ar ℂ.~ ℂ.idar A
      μeq : a ℂ.∘ M.μ.ar ℂ.~ a ℂ.∘ M.fc.ₐ a
    open ecategory-aux-only ℂ using (_ˢ)
    ηeqˢ : ℂ.idar A ℂ.~ a ℂ.∘ M.η.ar
    ηeqˢ = ηeq ˢ
    μeqˢ : a ℂ.∘ M.fc.ₐ a ℂ.~ a ℂ.∘ M.μ.ar
    μeqˢ = μeq ˢ

  record algebra-on (A : ℂ.Obj) : Set ℂ.ℓₕₒₘ where
    field
      ar : || ℂ.Hom (M.fc.ₒ A) A ||
      isalg : is-algebra ar
    open is-algebra isalg public

  record algebra : Set ℂ.ℓₐₗₗ where
    constructor mk-alg
    field
      {ob} : ℂ.Obj
      algon : algebra-on ob
    open algebra-on algon public

  is-algebra-morphism : {A : ℂ.Obj}(aa : algebra-on A){B : ℂ.Obj}(bb : algebra-on B)
                           → (ar : || ℂ.Hom A B ||)
                             → Set ℂ.ℓ~
  is-algebra-morphism aa bb ar = ar ℂ.∘ aa.ar ℂ.~ bb.ar ℂ.∘ M.fc.ₐ ar
                               where module aa = algebra-on aa
                                     module bb = algebra-on bb

  record algebra-morphism {A : ℂ.Obj}(aa : algebra-on A){B : ℂ.Obj}(bb : algebra-on B)
                          : Set ℂ.ℓₕₒₘ where
    constructor mk-alg-mor
    field
      {ar} : || ℂ.Hom A B ||
      sq : is-algebra-morphism aa bb ar
    open ecategory-aux-only ℂ using (_ˢ)
    private
      module aa = algebra-on aa
      module bb = algebra-on bb
    sqˢ :  bb.ar ℂ.∘ M.fc.ₐ ar ℂ.~ ar ℂ.∘ aa.ar
    sqˢ = sq ˢ


  id-is-alg-mor : {A : ℂ.Obj}(aa : algebra-on A) → is-algebra-morphism aa aa (ℂ.idar A)
  id-is-alg-mor aa = lidgen (ridggˢ r M.fc.id)
                   where open ecategory-aux-only ℂ


  inv-is-alg-mor : {A B : ℂ.Obj}(aa : algebra-on A)(bb : algebra-on B){f : || ℂ.Hom A B ||}
                   (ff : is-algebra-morphism aa bb f){f' : || ℂ.Hom B A ||}
                     → ℂ.is-iso-pair f f' → is-algebra-morphism bb aa f'
  inv-is-alg-mor aa bb ff isop = ℂ.iso-sq (M.ᵢₛₒ isop)
                                          isop
                                          (algebra-morphism.sq {aa = aa}
                                                               {bb = bb}
                                                               (mk-alg-mor ff))


  cmp-is-alg-mor : {A B C : ℂ.Obj}{aa : algebra-on A}{bb : algebra-on B}{cc : algebra-on C}
                   (f : || ℂ.Hom A B ||)(g : || ℂ.Hom B C ||)(h : || ℂ.Hom A C ||)
                     → is-algebra-morphism aa bb f → is-algebra-morphism bb cc g
                       → g ℂ.∘ f ℂ.~ h →  is-algebra-morphism aa cc h
  cmp-is-alg-mor {aa = aa} {bb} {cc} f g h falg galg eq = ~proof
    h ℂ.∘ aa.ar                        ~[ ∘e r (eq ˢ) ⊙ assˢ ] /
    g ℂ.∘ f ℂ.∘ aa.ar                  ~[ ∘e falg r ] /
    g ℂ.∘ bb.ar ℂ.∘ M.fc.ₐ f           ~[ ass ⊙ ∘e r galg ⊙ assˢ ] /
    cc.ar ℂ.∘ M.fc.ₐ g ℂ.∘ M.fc.ₐ f    ~[ ∘e (M.fc.∘ax eq) r ]∎
    cc.ar ℂ.∘ M.fc.ₐ h ∎
    where open ecategory-aux-only ℂ
          module aa = algebra-on aa
          module bb = algebra-on bb
          module cc = algebra-on cc

  cmp-is-alg-mor-str : {A B C : ℂ.Obj}{aa : algebra-on A}{bb : algebra-on B}{cc : algebra-on C}
                       (f : || ℂ.Hom A B ||)(g : || ℂ.Hom B C ||)
                         → is-algebra-morphism aa bb f → is-algebra-morphism bb cc g
                           →  is-algebra-morphism aa cc (g ℂ.∘ f)
  cmp-is-alg-mor-str {aa = aa} {bb} {cc} f g falg galg = ~proof
    (g ℂ.∘ f) ℂ.∘ aa.ar                ~[ assˢ ⊙ ∘e falg r ] /
    g ℂ.∘ bb.ar ℂ.∘ M.fc.ₐ f           ~[ ass ⊙ ∘e r galg ⊙ assˢ ] /
    cc.ar ℂ.∘ M.fc.ₐ g ℂ.∘ M.fc.ₐ f    ~[ ∘e (M.fc.cmp f g) r ]∎
    cc.ar ℂ.∘ M.fc.ₐ (g ℂ.∘ f) ∎
    where open ecategory-aux-only ℂ
          module aa = algebra-on aa
          module bb = algebra-on bb
          module cc = algebra-on cc


  free-alg-on : (A : ℂ.Obj) → algebra-on (M.fc.ₒ A)
  free-alg-on A = record
    { ar = M.μ.ar {A}
    ; isalg = record
            { ηeq = M.ax-ηT A
            ; μeq =  M.ax-μ A ⊙ ass ⊙ rid
            }
    }
    where open ecategory-aux-only ℂ

  free-alg-lift : {A B : ℂ.Obj}(bb : algebra-on B)
                     → || ℂ.Hom A B || → algebra-morphism (free-alg-on A) bb
  free-alg-lift bb f = record
    { ar = bb.ar ℂ.∘ M.fc.ₐ f
    ; sq = ~proof (bb.ar ℂ.∘ M.fc.ₐ f) ℂ.∘ M.μ.ar          ~[ assˢ ⊙ ∘e (M.μ.natˢ f) r ] /
                   bb.ar ℂ.∘ M.μ.ar ℂ.∘ M.².ₐ f            ~[ ass ⊙ ∘e r bb.μeq ⊙ assˢ ] /
                   bb.ar ℂ.∘ M.fc.ₐ bb.ar ℂ.∘ M.².ₐ f      ~[ ∘e (M.fc.cmp (M.fc.ₐ f) bb.ar) r ]∎
                   bb.ar ℂ.∘ M.fc.ₐ (bb.ar ℂ.∘ M.fc.ₐ f) ∎
    }
    where open ecategory-aux-only ℂ
          module bb = algebra-on bb

  free-alg-mor : {A B : ℂ.Obj}
                     → || ℂ.Hom A B || → algebra-morphism (free-alg-on A) (free-alg-on B)
  free-alg-mor f = record
    { ar = M.fc.ₐ f
    ; sq = M.μ.natˢ f
    }
-- end algebras-for-monad-defs


----------------------------
-- Eilenberg-Moore category
----------------------------

EMCat : {ℓₒ ℓₐ ℓ~ : Level}{ℂ : ecategoryₗₑᵥ ℓₒ ℓₐ ℓ~}
            → monad-on ℂ → ecategoryₗₑᵥ (ecat.ℓₐₗₗ ℂ) (ecat.ℓₕₒₘ ℂ) (ecat.ℓ~ ℂ)
EMCat {ℂ = ℂ} M = record
  { Obj = algebra
  ; Hom = λ aa bb → sub-setoid {X = algebra-morphism (alg.algon aa) (alg.algon bb)}
                                (ℂ.Hom (alg.ob aa) (alg.ob bb))
                                algebra-morphism.ar
  ; isecat = record
           { _∘_   = λ {aa} {bb} {cc} gg ff → record
                   { ar = algm.ar gg ℂ.∘ algm.ar ff
                   ; sq = cmp-is-alg-mor-str {aa = alg.algon aa} {alg.algon bb} {alg.algon cc}
                                             (algm.ar ff) (algm.ar gg) (algm.sq ff) (algm.sq gg)
                   }
           ; idar  = λ aa → record
                   { ar = ℂ.idar (alg.ob aa)
                   ; sq = id-is-alg-mor (alg.algon aa)
                   }
           ; ∘ext  = λ ff ff' gg gg' → ℂ.∘ext (algm.ar ff) (algm.ar ff') (algm.ar gg) (algm.ar gg')
           ; lidax = λ ff → ℂ.lidax (algm.ar ff)
           ; ridax = λ ff → ℂ.ridax (algm.ar ff)
           ; assoc = λ ff gg hh → ℂ.assoc (algm.ar ff) (algm.ar gg) (algm.ar hh)
           }
  }
  where module ℂ = ecat ℂ
        open algebras-for-monad-defs M
        open import tt-basics.setoids using (sub-setoid)
        module alg = algebra
        module algm = algebra-morphism
        

---------------------
-- Forgetful functor
---------------------

EM-U : {ℓₒ ℓₐ ℓ~ : Level}{ℂ : ecategoryₗₑᵥ ℓₒ ℓₐ ℓ~}(M : monad-on ℂ)
           → efunctorₗₑᵥ (EMCat M) ℂ
EM-U {ℂ = ℂ} M = record
  { FObj = alg.ob
  ; FHom = λ ff → algm.ar ff
  ; isF = record
        { ext = λ eq → eq
        ; id = λ {_} → ℂ.r
        ; cmp = λ f g → ℂ.r
        }
  }
  where module ℂ where
          open ecat ℂ public
          open ecategory-aux-only ℂ using (r) public
        open algebras-for-monad-defs M
        module alg = algebra
        module algm = algebra-morphism

EM-U-faithful : {ℓₒ ℓₐ ℓ~ : Level}{ℂ : ecategoryₗₑᵥ ℓₒ ℓₐ ℓ~}(M : monad-on ℂ)
                    → is-faithful (EM-U M)
EM-U-faithful {ℂ = ℂ} M = record
  { faith-pf = λ eq → eq
  }

EM-U-conserv : {ℓₒ ℓₐ ℓ~ : Level}{ℂ : ecategoryₗₑᵥ ℓₒ ℓₐ ℓ~}(M : monad-on ℂ)
                   → is-conservative (EM-U M)
EM-U-conserv {ℂ = ℂ} M = record
  { refl-iso = λ {aa} {bb} {ff} Uffiso → Alg.mkis-iso {invf = inv-alg-mor ff Uffiso}
                                                       (record
                                           { iddom = ℂ.is-iso.iddom Uffiso
                                           ; idcod = ℂ.is-iso.idcod Uffiso
                                           })
  }
  where module Alg where
          open ecat (EMCat M) public
          open iso-defs (EMCat M) public
        module ℂ where
          open ecat ℂ public
          open iso-defs ℂ public
        module U = efctr (EM-U M)
        open algebras-for-monad-defs M
        inv-alg-mor : {aa bb : Alg.Obj}(ff : || Alg.Hom aa bb ||)
                          → ℂ.is-iso (U.ₐ ff) → || Alg.Hom bb aa ||
        inv-alg-mor {aa} {bb} ff Uffiso = mk-alg-mor (inv-is-alg-mor aa.algon
                                                                     bb.algon
                                                                     ff.sq
                                                                     ff.isisopair)
          where module aa = algebra aa
                module bb = algebra bb
                module ff where
                  open algebra-morphism ff public
                  open ℂ.is-iso Uffiso public


------------------------
-- Free algebra functor
------------------------

EM-F : {ℓₒ ℓₐ ℓ~ : Level}{ℂ : ecategoryₗₑᵥ ℓₒ ℓₐ ℓ~}(M : monad-on ℂ)
           → efunctorₗₑᵥ ℂ (EMCat M)
EM-F {ℂ = ℂ} M = record
  { FObj = λ A → mk-alg (free-alg-on A)
  ; FHom = free-alg-mor
  ; isF = record
        { ext = M.fc.ext
        ; id = M.fc.id
        ; cmp = M.fc.cmp
        }
  }
  where module M = monad-on M
        open algebras-for-monad-defs M


--------------
-- Adjunction
--------------

module Eilenberg-Moore-adjunction {ℓₒ ℓₐ ℓ~ : Level}{ℂ : ecategoryₗₑᵥ ℓₒ ℓₐ ℓ~}(M : monad-on ℂ) where
  open algebras-for-monad-defs M
  private
    module ℂ = ecat ℂ
    module M = monad-on M
    module EM = ecat (EMCat M)
    U = EM-U M
    F = EM-F M
    module U = efunctor-aux U
    module F = efunctor-aux F
    module alg/ = algebra-on
    module alg = algebra
    module algm = algebra-morphism

  η : IdF ⇒ U ○ F
  η = record
    { fnc = M.η.ar
    ; nat = M.η.nat
    }

  alg-is-alg-mor : {A : ℂ.Obj}(aa : algebra-on A)
                      → is-algebra-morphism (free-alg-on A) aa (alg/.ar aa)
  alg-is-alg-mor = alg/.μeq

  ε : F ○ U ⇒ IdF
  ε = record
    { fnc = λ {aa} → mk-alg-mor (alg-is-alg-mor (alg.algon aa))
    ; nat = λ ff → algm.sqˢ ff
    }

  private
    module η = natural-transformation η
    module ε = natural-transformation ε
  εFFη : (X : ℂ.Obj) → ε.ar {F.ₒ X}  EM.∘ F.ₐ η.ar EM.~ EM.idar (F.ₒ X)
  εFFη X = M.ax-Tη X
  UεηU : {A : ℂ.Obj}(aa : algebra-on A) → U.ₐ (ε.ar {mk-alg aa}) ℂ.∘ η.ar ℂ.~ ℂ.idar A
  UεηU aa = aa.ηeq
          where module aa = algebra-on aa
-- end Eilenberg-Moore-adjunction


EM-adj : {ℓₒ ℓₐ ℓ~ : Level}{ℂ : ecategoryₗₑᵥ ℓₒ ℓₐ ℓ~}(M : monad-on ℂ)
             → EM-F M ⊣ EM-U M
EM-adj {ℂ = ℂ} M = record
  { ηnt = η
  ; εnt = ε
  ; trid₁ = λ {X} → εFFη X
  ; trid₂ = λ {aa} → UεηU (algebra.algon aa)
  }
  where open Eilenberg-Moore-adjunction M
        open algebras-for-monad-defs M


-- Comparison functor


module Eilenberg-Moore-comparison {ℓₒ₁ ℓₐ₁ ℓ~₁ : Level}{ℂ : ecategoryₗₑᵥ ℓₒ₁ ℓₐ₁ ℓ~₁}
                                  {ℓₒ₂ ℓₐ₂ ℓ~₂ : Level}{𝔻 : ecategoryₗₑᵥ ℓₒ₂ ℓₐ₂ ℓ~₂}
                                  {L : efunctorₗₑᵥ ℂ 𝔻}{R : efunctorₗₑᵥ 𝔻 ℂ}
                                  (L⊣R : adjunction-εη L R)
                                  where
  private
    module ℂ = ecat ℂ
    module 𝔻 = ecat 𝔻
    --module [ℂ,𝔻] = ecat [ ℂ , 𝔻 ]ᶜᵃᵗ
    --module [ℂ,ℂ] = ecat [ ℂ , ℂ ]ᶜᵃᵗ
    module L = efunctor-aux L
    module R = efunctor-aux R
    module L⊣R = adjunction-εη L⊣R
    RL RL² : efunctorₗₑᵥ ℂ ℂ
    RL = R ○ L
    RL² = RL ○ RL
    LR : efunctorₗₑᵥ 𝔻 𝔻
    LR = L ○ R
    η : IdF ⇒ RL
    η = L⊣R.ηnt
    module η = natural-transformation η
    ε : LR ⇒ IdF
    ε = L⊣R.εnt
    module ε = natural-transformation ε
    module LR = efunctor-aux LR
    module RL where
      open efunctor-aux (R ○ L) public
      ismnd : monad-struct-on RL
      ismnd = adjunction2monad-on-cmp L⊣R
      mndon : monad-on ℂ
      mndon = adjunction2monad-on-cat L⊣R
      open monad-struct-on ismnd public
      module μaux = monad-from-adjunction.μ-aux L⊣R
    module Alg[RL] = ecat (EMCat RL.mndon)
    Alg[RL] : ecategoryₗₑᵥ Alg[RL].ℓₒ Alg[RL].ℓₐᵣᵣ Alg[RL].ℓ~
    Alg[RL] = EMCat RL.mndon
    U : efunctorₗₑᵥ Alg[RL] ℂ
    U = EM-U RL.mndon
    F : efunctorₗₑᵥ ℂ Alg[RL]
    F = EM-F RL.mndon
    F⊣U : F ⊣ U
    F⊣U = EM-adj RL.mndon
    module U = is-conservative (EM-U-conserv RL.mndon)
  open algebras-for-monad-defs RL.mndon

  -- counit gives algebras

  Rε-is-alg : (A : 𝔻.Obj) → is-algebra (R.ₐ (ε.ar {A}))
  Rε-is-alg A = record
    { ηeq = L⊣R.trid₂ {A}
    ; μeq = ~proof R.ₐ (ε.ar {A}) ∘ RL.μ.ar {R.ₒ A}         ~[ ∘e RL.μaux.~RεL r ] /
                    R.ₐ (ε.ar {A}) ∘ R.ₐ (ε.ar {LR.ₒ A})    ~[ R.∘∘ (ε.natˢ (ε.ar {A})) ]∎
                    R.ₐ (ε.ar {A}) ∘ RL.ₐ (R.ₐ (ε.ar {A})) ∎
    }
    where open ecategory-aux ℂ

  Rε : R ○ L ○ R ⇒ R ○ IdF
  Rε = R ·ₙₜ ε

  private module Rε (A : 𝔻.Obj) where
            open natural-transformation Rε public
            module alg (A : 𝔻.Obj) = is-algebra (Rε-is-alg A)

  Rε-alg : (A : 𝔻.Obj) → algebra-on (R.ₒ A)
  Rε-alg A = record
    { ar = Rε.ar A
    ; isalg = Rε-is-alg A
    }

  Rε-arr : {A B : 𝔻.Obj}(f : || 𝔻.Hom A B ||) → is-algebra-morphism (Rε-alg A) (Rε-alg B) (R.ₐ f)
  Rε-arr f = R.∘∘ (ε.natˢ f)

  K : efunctorₗₑᵥ 𝔻 Alg[RL]
  K = record
    { FObj = λ A → mk-alg (Rε-alg A)
    ; FHom = λ f → mk-alg-mor {ar = R.ₐ f} (Rε-arr f)
    ; isF = record
          { ext = R.ext
          ; id = R.id
          ; cmp = R.cmp
          }
    }

  private module K = efunctor-aux K

  triangR : U ○ K ≅ₐ R
  triangR = record
    { natt = record
           { fnc = λ {A} → ℂ.idar (R.ₒ A)
           ; nat = λ _ → lidgen ridˢ
           }
    ; natt⁻¹ = record
             { fnc = λ {A} → ℂ.idar (R.ₒ A)
             ; nat = λ _ → lidgen ridˢ
             }
    ; isiso = λ {A} → idar-is-isopair (R.ₒ A)
    }
    where open ecategory-aux-only ℂ
          open iso-props ℂ

  triangL : K ○ L ≅ₐ F
  triangL = record
    { natt = record
           { fnc = λ {X} → mk-alg-mor {ar = ℂ.idar (RL.ₒ X)}
                                       (~proof ℂ.idar (RL.ₒ X) ∘ R.ₐ (ε.ar {L.ₒ X})
                                                                            ~[ lidgen RL.μaux.RεL~ ] /
                                               RL.μ.ar {X}                  ~[ ridggˢ r RL.id ]∎
                                               RL.μ.ar {X} ∘ RL.ₐ (ℂ.idar (RL.ₒ X)) ∎)
           ; nat = λ _ → lidgen ridˢ
           }
    ; natt⁻¹ = record
           { fnc = λ {X} → mk-alg-mor {ar = ℂ.idar (RL.ₒ X)}
                                       (~proof ℂ.idar (RL.ₒ X) ∘ RL.μ.ar {X}   ~[ lid ] /
                                               RL.μ.ar {X}             ~[ ridggˢ RL.μaux.~RεL RL.id ]∎
                                               R.ₐ (ε.ar {L.ₒ X}) ∘ RL.ₐ (ℂ.idar (RL.ₒ X)) ∎)
           ; nat = λ _ → lidgen ridˢ
           }
    ; isiso = λ {X} → record
            { iddom = lid
            ; idcod = lid
            }
    }
    where open ecategory-aux ℂ

-- end Eilenberg-Moore-comparison
