{-# OPTIONS --without-K #-}

module ecats.concr-ecats.monads where

open import tt-basics.setoids using (setoid)
open import tt-basics.basics
open import ecats.basic-defs.ecat-def&not
open import ecats.functors.defs.efunctor-d&n
open import ecats.functors.defs.basic-defs
open import ecats.functors.defs.natural-transformation
open import ecats.functors.defs.natural-iso
open import ecats.basic-defs.isomorphism
open import ecats.basic-props.isomorphism
open import ecats.functors.defs.monad


-----------------------
-- Moprhisms of monads
-----------------------

private
  module mnd-aux {ℓₒ ℓₐ ℓ~ : Level}{ℂ : ecategoryₗₑᵥ ℓₒ ℓₐ ℓ~}(M : monad-on ℂ) where
    open monad-on M public
    open efctr fc using (ₒ; ₐ) public


record is-lax-monad-morphism {ℓₒ₁ ℓₐ₁ ℓ~₁ : Level}{ℂ : ecategoryₗₑᵥ ℓₒ₁ ℓₐ₁ ℓ~₁}
                             {ℓₒ₂ ℓₐ₂ ℓ~₂ : Level}{𝔻 : ecategoryₗₑᵥ ℓₒ₂ ℓₐ₂ ℓ~₂}
                             (M : monad-on ℂ)(N : monad-on 𝔻)
                             (F : efunctorₗₑᵥ ℂ 𝔻)(ϕ : monad-on.fc N ○ F ⇒ F ○ monad-on.fc M)
                             : Set (ecat.ℓₒ ℂ ⊔ ecat.ℓ~ 𝔻) where
    private
      module ℂ =  ecat ℂ
      module 𝔻 =  ecat 𝔻
      module M = mnd-aux M
      module N = mnd-aux N
      module F = efunctor-aux F
      module ϕ = natural-transformation ϕ
    field
      ηax : (X : ℂ.Obj) → ϕ.ar {X} 𝔻.∘ N.η.ar {F.ₒ X} 𝔻.~ F.ₐ (M.η.ar {X})
      μax : (X : ℂ.Obj) → ϕ.ar {X} 𝔻.∘ N.μ.ar {F.ₒ X}
                               𝔻.~ F.ₐ (M.μ.ar {X}) 𝔻.∘ ϕ.ar {M.ₒ X} 𝔻.∘ N.ₐ (ϕ.ar {X})

record lax-monad-morphism {ℓₒ₁ ℓₐ₁ ℓ~₁ : Level}{ℂ : ecategoryₗₑᵥ ℓₒ₁ ℓₐ₁ ℓ~₁}
                          {ℓₒ₂ ℓₐ₂ ℓ~₂ : Level}{𝔻 : ecategoryₗₑᵥ ℓₒ₂ ℓₐ₂ ℓ~₂}
                          (M : monad-on ℂ)(N : monad-on 𝔻)
                          : Set (ecat.ℓₐₗₗ ℂ ⊔ ecat.ℓₐₗₗ 𝔻) where
    private
      module ℂ =  ecat ℂ
      module 𝔻 =  ecat 𝔻
      module M = mnd-aux M
      module N = mnd-aux N
    field
      fc : efunctorₗₑᵥ ℂ 𝔻
      nt : N.fc ○ fc ⇒ fc ○ M.fc
      islaxmor : is-lax-monad-morphism M N fc nt
    open is-lax-monad-morphism islaxmor public
    open efctr fc using (ₒ; ₐ) public
    module fc = efunctor-aux fc
    open natural-transformation nt public

id-laxmndmorph : {ℓₒ ℓₐ ℓ~ : Level}{ℂ : ecategoryₗₑᵥ ℓₒ ℓₐ ℓ~}(M : monad-on ℂ)
                     → lax-monad-morphism M M
id-laxmndmorph {ℂ = ℂ} M = record
  { fc = IdF
  ; nt = natt-vcmp IdM-M.natt⁻¹ MId-M.natt 
  ; islaxmor = record
             { ηax = λ X → assˢ ⊙ lidgen lid
             ; μax = λ X → lidgg (ridggˢ (ridgenˢ ridˢ ⊙ assˢ) (M.fc.idax lid) ⊙ assˢ) lid
             }
  }
  where open ecategory-aux ℂ --module ℂ = ecat ℂ
        module M = monad-on M
        module MId-M = natural-iso (○rid {F = M.fc})
        module IdM-M = natural-iso (○lid {F = M.fc})
        -- underlying arrows are identities

module cat-monads-defs (ℓₒ ℓₐ ℓ~ : Level) where
  record Obj : Set (sucₗₑᵥ (ℓₒ ⊔ ℓₐ ⊔ ℓ~)) where
    field
      ct : ecategoryₗₑᵥ ℓₒ ℓₐ ℓ~
      mnd : monad-on ct
    module ct = ecat ct
    module mnd where
      open monad-on mnd public
      open efctr fc using (ₒ; ₐ) public
    open mnd public

  morph-eq : (A B : Obj) → lax-monad-morphism (Obj.mnd A) (Obj.mnd B)
                → lax-monad-morphism (Obj.mnd A) (Obj.mnd B) → Set (ℓₒ ⊔ ℓₐ ⊔ ℓ~)
  morph-eq A B m n = Σ (m.fc ≅ₐ n.fc) nt-eq
                   where module A = Obj A
                         module B = Obj B
                         module m = lax-monad-morphism m
                         module n = lax-monad-morphism n
                         nt-eq : (ξ : m.fc ≅ₐ n.fc) → Set (A.ct.ℓₒ ⊔ B.ct.ℓ~)
                         nt-eq ξ = {X : A.ct.Obj}
                                      → ξ.ar {A.ₒ X} B.ct.∘ m.ar {X}
                                                          B.ct.~ n.ar {X} B.ct.∘ B.ₐ (ξ.ar {X})
                                 where module ξ = natural-iso ξ
  module morph-eq {A B : Obj}{m n : lax-monad-morphism (Obj.mnd A) (Obj.mnd B)}
                  (eq : morph-eq A B m n)
                  where
    private
      module A = Obj A
      module B = Obj B
      module m = lax-monad-morphism m
      module n = lax-monad-morphism n
    fc~ : m.fc ≅ₐ n.fc
    fc~ = pj1 eq
    module fc~ = natural-iso fc~
    nt~ : {X : A.ct.Obj}
             → fc~.ar {A.ₒ X} B.ct.∘ m.ar {X} B.ct.~ n.ar {X} B.ct.∘ B.ₐ (fc~.ar {X})
    nt~ = pj2 eq
    nt~ˢ : {X : A.ct.Obj}
             → n.ar {X} B.ct.∘ B.ₐ (fc~.ar {X}) B.ct.~ fc~.ar {A.ₒ X} B.ct.∘ m.ar {X}
    nt~ˢ {X} = nt~ {X} ˢ
             where open ecategory-aux-only B.ct using (_ˢ)
  -- end morph-eq

  laxMndMor : (A B : Obj) → setoid {ℓₒ ⊔ ℓₐ ⊔ ℓ~} {ℓₒ ⊔ ℓₐ ⊔ ℓ~}
  laxMndMor A B = record
    { object = lax-monad-morphism A.mnd B.mnd
    ; _∼_ = morph-eq A B
    ; istteqrel = record
                { refl = λ m → ≅ₐrefl
                                , λ {X} → 
                idar (lm.ₒ m (A.ₒ X)) ∘ lm.ar m {X}    ~[ ridggˢ lid B.fc.id ]
                lm.ar m {X} ∘ B.ₐ (idar (lm.ₒ m X))
                ; sym = λ {m} {n} eq → ≅ₐsym (lm~.fc~ {m} {n} eq)
                                        , λ {X} → 
                lm~.fc~.ar⁻¹ {m} {n} eq {A.ₒ X} ∘ lm.ar n {X}
                                                    ~[ iso-sq (B.fc.ᵢₛₒ (lm~.fc~.isiso {m} {n} eq)) (lm~.fc~.isiso {m} {n} eq) (lm~.nt~ {m} {n} eq {X}) ]
                lm.ar m {X} ∘ B.ₐ (lm~.fc~.ar⁻¹ {m} {n} eq {X})
                ; tra = λ {m} {n} {l} eq₁ eq₂ → natiso-vcmp (lm~.fc~ {n} {l} eq₂)
                                                              (lm~.fc~ {m} {n} eq₁)
                                                 , λ {X} → ~proof
                (lm~.fc~.ar {n} {l} eq₂ ∘ lm~.fc~.ar {m} {n} eq₁) ∘ lm.ar m {X}
                                                         ~[ assˢ   ⊙ ∘e (lm~.nt~ {m} {n} eq₁ {X}) r ] /
                lm~.fc~.ar {n} {l} eq₂ ∘ lm.ar n {X} ∘ B.ₐ (lm~.fc~.ar {m} {n} eq₁)
                               ~[ ass ⊙ ∘e r (lm~.nt~ {n} {l} eq₂ {X}) ⊙ assˢ ⊙ ∘e B.fc.∘ax-rf r ]∎
                lm.ar l {X} ∘ B.ₐ (lm~.fc~.ar {n} {l} eq₂ ∘ lm~.fc~.ar {m} {n} eq₁) ∎
                }
    }
    where module A = Obj A
          module B = Obj B
          module lm = lax-monad-morphism
          module lm~ = morph-eq {A} {B}
          open ecategory-aux B.ct
          open iso-props B.ct

  morph-cmp : {A B C : Obj} → lax-monad-morphism (Obj.mnd A) (Obj.mnd B)
                 → lax-monad-morphism (Obj.mnd B) (Obj.mnd C)
                   → lax-monad-morphism (Obj.mnd A) (Obj.mnd C)
  morph-cmp {A} {B} {C} m n = record
    { fc = n.fc ○ m.fc
    ; nt = nt
    ; islaxmor = record
               { ηax = λ X → ~proof
               nt.ar ∘ C.η.ar {n.ₒ (m.ₒ X)}                 ~[ assˢ ⊙ ∘e (n.ηax (m.ₒ X)) r ] /
               n.ₐ (m.ar {X}) C.ct.∘ n.ₐ (B.η.ar {m.ₒ X})   ~[ n.fc.∘ax (m.ηax X) ]∎
               n.ₐ (m.ₐ (A.η.ar {X})) ∎
               ; μax = λ X → ~proof
    nt.ar ∘ C.μ.ar                                                  ~[ assˢ ⊙ ∘e (n.μax (m.ₒ X)) r ] /
    n.ₐ (m.ar {X}) C.ct.∘ n.ₐ B.μ.ar C.ct.∘ n.ar C.ct.∘ C.ₐ n.ar
                                      ~[ ass ⊙ ∘e r (n.fc.∘∘ (m.μax X) ⊙ ∘e n.fc.∘ax-rfˢ r) ⊙ assˢ ] /
    n.ₐ (m.ₐ A.μ.ar) C.ct.∘ (n.ₐ m.ar C.ct.∘ n.ₐ (B.ₐ m.ar)) C.ct.∘ n.ar C.ct.∘ C.ₐ n.ar
                   ~[ ∘e (assˢ ⊙ ∘e (ass ⊙ ∘e r (n.natˢ m.ar) ⊙ assˢ) r ⊙ ass ⊙ ∘e C.fc.∘ax-rf r) r ]∎
    n.ₐ (m.ₐ A.μ.ar) ∘ nt.ar ∘ C.ₐ nt.ar ∎
               }
    }
    where module A = Obj A
          module B = Obj B
          module C = Obj C
          module m = lax-monad-morphism m -- m.nt : B m.fc ⇒ m.fc A
          module n = lax-monad-morphism n -- n.nt : C n.fc ⇒ n.fc B
          open ecategory-aux C.ct
          nt : C.fc ○ n.fc ○ m.fc ⇒ (n.fc ○ m.fc) ○ A.fc
          nt = record
            { fnc = λ {X} → n.ₐ (m.ar {X}) C.ct.∘ n.ar {m.fc.ₒ X}
            ; nat = λ f → ~proof
            (n.ₐ m.ar C.ct.∘ n.ar) C.ct.∘ C.ₐ (n.ₐ (m.ₐ f))  ~[ assˢ ⊙ ∘e (n.nat (m.ₐ f)) r ] /
            n.ₐ m.ar C.ct.∘ n.ₐ (B.ₐ (m.ₐ f)) C.ct.∘ n.ar
                                                         ~[ ass ⊙ ∘e r (n.fc.∘∘ (m.nat f)) ⊙ assˢ ]∎
            n.ₐ (m.ₐ (A.ₐ f)) C.ct.∘ n.ₐ m.ar C.ct.∘ n.ar ∎
            }
          module nt = natural-transformation nt

  morph-cmp-ext : {A B C : Obj}(m m' : || laxMndMor A B ||)(n n' : || laxMndMor B C ||)
                     → morph-eq A B m m' → morph-eq B C n n'
                       → morph-eq A C (morph-cmp m n) (morph-cmp m' n')
  morph-cmp-ext {A} {B} {C} m m' n n' eqm eqn = natiso-hcmp eqn.fc~ eqm.fc~
                                              , λ {X} → ~proof
    eqmn.ar ∘ nm.ar                            ~[ assˢ ⊙ ∘e (ass ⊙ ∘e r (n.fc.∘∘ eqm.nt~) ⊙ assˢ) r ] /
    eqn.fc~.ar ∘ n.ₐ m'.ar ∘ n.ₐ (B.ₐ eqm.fc~.ar) ∘ n.ar
                                        ~[ ass ⊙ ∘e (n.natˢ eqm.fc~.ar) (eqn.fc~.nat m'.ar) ⊙ assˢ ] /
    n'.ₐ m'.ar ∘ eqn.fc~.ar ∘ n.ar ∘ C.ₐ (n.ₐ eqm.fc~.ar)        ~[ ∘e (ass ⊙ ∘e r eqn.nt~ ⊙ assˢ) r ] /
    n'.ₐ m'.ar ∘ n'.ar ∘ C.ₐ eqn.fc~.ar ∘ C.ₐ (n.ₐ eqm.fc~.ar)              ~[ ass ⊙ ∘e C.fc.∘ax-rf r ]∎
    nm'.ar ∘ C.ₐ eqmn.ar ∎
                         where module ℂ = ecat (Obj.ct C)
                               module A = Obj A
                               module B = Obj B
                               module C = Obj C
                               module m = lax-monad-morphism m -- m.nt : B m ⇒ m A
                               module n = lax-monad-morphism n -- n.nt : C n ⇒ n B
                               module m' = lax-monad-morphism m'
                               module n' = lax-monad-morphism n'
                               module nm = lax-monad-morphism (morph-cmp m n) -- nm.nt : C nm ⇒ nm A
                               module nm' = lax-monad-morphism (morph-cmp m' n')
                               module eqn = morph-eq {B} {C} {n} {n'} eqn -- n.fc ~ n'.fc
                               module eqm = morph-eq {A} {B} {m} {m'} eqm
                               module eqmn = natural-iso (natiso-hcmp eqn.fc~ eqm.fc~)
                               open ecategory-aux C.ct

  lidax : {A B : Obj} (m : || laxMndMor A B ||)
             → morph-eq A B (morph-cmp m (id-laxmndmorph (Obj.mnd B))) m
  lidax {A} {B} m = (○lid {F = m.fc}) , (λ {X} → ~proof
                  lid.ar ∘ id∘m.ar             ~[ lidgen (ridgg r lid) ] /
                  m.ar                        ~[ ridggˢ r B.fc.id ]∎
                  m.ar ∘ B.ₐ lid.ar ∎)
                  where module B = Obj B
                        module m = lax-monad-morphism m -- m.nt : B m ⇒ m A
                        module id∘m = lax-monad-morphism (morph-cmp m (id-laxmndmorph (Obj.mnd B)))
                        module lid = natural-iso (○lid {F = m.fc})
                        open ecategory-aux B.ct

  
  ridax : {A B : Obj} (m : || laxMndMor A B ||)
             → morph-eq A B (morph-cmp (id-laxmndmorph (Obj.mnd A)) m) m
  ridax {A} {B} m = (○rid {F = m.fc}) , (λ {X} → ~proof
                  rid.ar ∘ m∘id.ar         ~[ lidgen (lidgg r (m.fc.idax (A.ct.lidax _))) ] /
                  m.ar                    ~[ ridggˢ r B.fc.id ]∎
                  m.ar ∘ B.ₐ rid.ar ∎)
                  where module A = Obj A
                        module B = Obj B
                        module m = lax-monad-morphism m -- m.nt : B m ⇒ m A
                        module m∘id = lax-monad-morphism (morph-cmp (id-laxmndmorph (Obj.mnd A)) m)
                        module rid = natural-iso (○rid {F = m.fc})
                        open ecategory-aux B.ct

  ass : {A B C D : Obj}(m : || laxMndMor A B ||)(n : || laxMndMor B C ||)(l : || laxMndMor C D ||)
           → morph-eq A D (morph-cmp (morph-cmp m n) l) (morph-cmp m (morph-cmp n l))
  ass {A} {B} {C} {D} m n l = ○ass {F =  m.fc} {n.fc} {l.fc} , (λ {X} → ~proof
    ○ass.ar ∘ l-nm.ar {X}                                            ~[ lid ] /
    l.ₐ (n.ₐ m.ar C.ct.∘ n.ar {m.fc.ₒ X}) ∘ l.ar {nm.ₒ X}             ~[ ∘e r l.fc.∘ax-rfˢ ⊙ assˢ ] /
    l.ₐ (n.ₐ m.ar) ∘ l.ₐ n.ar ∘ l.ar {nm.ₒ X}                         ~[ ridggˢ r D.fc.id ]∎
    ln-m.ar ∘ D.ₐ ○ass.ar ∎)
    where module C = Obj C
          module D = Obj D
          module m = lax-monad-morphism m -- m.nt : B m ⇒ m A
          module n = lax-monad-morphism n -- n.nt : C n ⇒ n B
          module l = lax-monad-morphism l
          module ln = lax-monad-morphism (morph-cmp n l) -- ln.nt : D ln ⇒ ln B
          module nm = lax-monad-morphism (morph-cmp m n) -- nm.nt : C nm ⇒ nm A
          module l-nm = lax-monad-morphism (morph-cmp (morph-cmp m n) l)
          module ln-m = lax-monad-morphism (morph-cmp m (morph-cmp n l))
          module ○ass = natural-iso (○ass {F =  m.fc} {n.fc} {l.fc})
          open ecategory-aux D.ct


-- end cat-monads-defs



-----------------------
-- Category of monads
-----------------------

Mndₗₑᵥ : (ℓₒ ℓₐ ℓ~ : Level) → ecategoryₗₑᵥ (sucₗₑᵥ (ℓₒ ⊔ ℓₐ ⊔ ℓ~)) (ℓₒ ⊔ ℓₐ ⊔ ℓ~) (ℓₒ ⊔ ℓₐ ⊔ ℓ~)
Mndₗₑᵥ ℓₒ ℓₐ ℓ~ = record
  { Obj = Obj
  ; Hom = laxMndMor
  ; isecat = record
               { _∘_ = λ n m → morph-cmp m n
               ; idar = λ A → id-laxmndmorph (Obj.mnd A)
               ; ∘ext = morph-cmp-ext
               ; lidax = lidax
               ; ridax = ridax
               ; assoc = ass
               }
  }
  where open cat-monads-defs ℓₒ ℓₐ ℓ~

