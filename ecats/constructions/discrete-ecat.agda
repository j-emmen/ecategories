
{-# OPTIONS --without-K #-}

module ecats.constructions.discrete-ecat where

open import tt-basics.all-basics hiding (||_||)
open import ecats.basic-defs.ecat-def&not
open import ecats.basic-defs.isomorphism
open import ecats.basic-props.isomorphism
open import ecats.functors.defs.efunctor-d&n
open import ecats.functors.defs.natural-transformation
open import ecats.functors.defs.natural-iso

discrete-ecat' : {ℓ : Level} → Set ℓ → ecategoryₗₑᵥ ℓ ℓ 0ₗₑᵥ
-- ℓ₁ ≤ ℓ₂ ; 0ₗₑᵥ ≤ ℓ₃
discrete-ecat' A = record
  { Obj = A
  ; Hom = λ x y → codisc-std (x == y)
  ; isecat = record
           { _∘_ = λ q p → =tra p q
           ; idar = λ _ → =rf
           ; ∘ext = λ f f' g g' _ _ → 0₁
           ; lidax = λ f → 0₁
           ; ridax = λ f → 0₁
           ; assoc = λ f g h → 0₁
           }
  }

discrete-ecat : {ℓ : Level} → Set ℓ → ecategoryₗₑᵥ ℓ ℓ ℓ
-- ℓ₁ ≤ ℓ₂ ; 0ₗₑᵥ ≤ ℓ₃
discrete-ecat A = record
  { Obj = A
  ; Hom = λ x y → Freestd (x == y)
  ; isecat = record
           { _∘_ = λ q p → p ■ q
           ; idar = λ _ → =rf
           ; ∘ext = λ p p' q q' → ■ext p q'
           ; lidax = ■idr
           ; ridax = ■idl
           ; assoc = ■ass⁻¹
           }
  }

small-disc-ecat : Set 0ₗₑᵥ → small-ecategory
small-disc-ecat = discrete-ecat {0ₗₑᵥ}

-- there is no discrete locally small category


-- part of the universal property of discrete ecategories:

disc-ecat-lift-efctr : {ℓ : Level}{A : Set ℓ}{ℓ₁ ℓ₂ ℓ₃ : Level}(ℂ : ecategoryₗₑᵥ ℓ₁ ℓ₂ ℓ₃)
                          → (A → ecat.Obj ℂ) → efunctorₗₑᵥ (discrete-ecat A) ℂ
disc-ecat-lift-efctr {A = A} ℂ F = record
  { FObj = F
  ; FHom = FH 
  ; isF = record
        { ext = λ {_} {_} {p} {_} → =J (λ q _ → FH p ℂ.~ FH q) ℂ.r
        ; id = λ {x} → ℂ.r
        ; cmp = FHcmp
        }
  }
  where module ℂ = ecategory-aux ℂ
        FH : {x y : A} → x == y → || ℂ.Hom (F x) (F y) ||
        FH {x} {_} = =J (λ u _ → || ℂ.Hom (F x) (F u) ||) (ℂ.idar (F x))
        FHcmp : {x y z : A}(p : x == y)(q : y == z)
                   → FH q ℂ.∘ FH p ℂ.~ FH (p ■ q)
        FHcmp p q = =J (λ _ v → ∀ u → FH v ℂ.∘ FH u ℂ.~ FH (u ■ v)) (λ _ → ℂ.lid) q p

disc-ecat-lift-transf : {ℓ : Level}{A : Set ℓ}{ℓ₁ ℓ₂ ℓ₃ : Level}(ℂ : ecategoryₗₑᵥ ℓ₁ ℓ₂ ℓ₃)
                        {F G : A → ecat.Obj ℂ} (t : (a : A) → || ecat.Hom ℂ (F a) (G a) ||)
                             → natural-transformation (disc-ecat-lift-efctr ℂ F)
                                                       (disc-ecat-lift-efctr ℂ G)
disc-ecat-lift-transf ℂ {F} {G} t = record
  { fnc = λ {a} → t a
  ; nat = λ {a} → =J (λ b ab → t b ℂ.∘ F.ₐ ab ℂ.~ G.ₐ ab ℂ.∘ t a) (ridgen lidˢ)
  }
  where module ℂ = ecat ℂ
        module F = efctr (disc-ecat-lift-efctr ℂ F)
        module G = efctr (disc-ecat-lift-efctr ℂ G)
        open ecategory-aux-only ℂ using (ridgen; lidˢ)

disc-ecat-lift-full : {ℓ : Level}{A : Set ℓ}{ℓ₁ ℓ₂ ℓ₃ : Level}(ℂ : ecategoryₗₑᵥ ℓ₁ ℓ₂ ℓ₃)
                      {F G : efunctorₗₑᵥ (discrete-ecat A) ℂ}
                           → ((a : A) → || ecat.Hom ℂ (efctr.ₒ F a) (efctr.ₒ G a) ||)
                             → natural-transformation F G
disc-ecat-lift-full ℂ {F} {G} t = record
  { fnc = λ {a} → t a
  ; nat = λ {a} → =J (λ b ab → (t b ℂ.∘ F.ₐ ab) ℂ.~ (G.ₐ ab ℂ.∘ t a)) (ridgg (lidggˢ r G.id) F.id)
  }
  where module ℂ = ecat ℂ
        module F = efctr F
        module G = efctr G
        open ecategory-aux-only ℂ using (r; ridgg; lidggˢ)

disc-ecat-tr : {ℓ : Level}{A : Set ℓ}{ℓ₁ ℓ₂ ℓ₃ : Level}{ℂ : ecategoryₗₑᵥ ℓ₁ ℓ₂ ℓ₃}(G : A → ecat.Obj ℂ)
               {ℓ₄ ℓ₅ ℓ₆ : Level}{𝔻 : ecategoryₗₑᵥ ℓ₄ ℓ₅ ℓ₆}(F : efunctorₗₑᵥ ℂ 𝔻)
                 → F ○ disc-ecat-lift-efctr ℂ G ≅ₐ disc-ecat-lift-efctr 𝔻 (λ a → efctr.ₒ F (G a))
disc-ecat-tr {A = A} {ℂ = ℂ} G {𝔻 = 𝔻} F =
  mk-natiso {λ {a} → 𝔻.idar (F.ₒ (G a))}
            {λ {a} → 𝔻.idar (F.ₒ (G a))}
            (λ {a} → 𝔻.idar-is-isopair (F.ₒ (G a)))
            ( λ {a} → =J (λ b eq → (𝔻.idar (F.ₒ (G b)) 𝔻.∘ F.ₐ (↑G.ₐ eq)) 𝔻.~
                                                          (↑FG.ₐ eq 𝔻.∘ 𝔻.idar (F.ₒ (G a))))
                          (lidgen (ridgenˢ F.id)) )
                                           where open natural-iso-defs (F ○ disc-ecat-lift-efctr ℂ G) (disc-ecat-lift-efctr 𝔻 (λ a → efctr.ₒ F (G a)))
                                                 module ℂ = ecat ℂ
                                                 module 𝔻 where
                                                   open ecat 𝔻 public
                                                   open iso-defs 𝔻 public
                                                   open iso-props 𝔻 public
                                                 module F = efctr F
                                                 module ↑G = efctr (disc-ecat-lift-efctr ℂ G)
                                                 module ↑FG = efctr (disc-ecat-lift-efctr 𝔻 (λ a → efctr.ₒ F (G a)))
                                                 open ecategory-aux-only 𝔻 using (lidgen; ridgenˢ)



-- codiscrete ecategories

codiscrete-ecat : {ℓ : Level} → Set ℓ → ecategoryₗₑᵥ ℓ 0ₗₑᵥ 0ₗₑᵥ
-- ℓ₁ ≤ ℓ₂ ; 0ₗₑᵥ ≤ ℓ₃
codiscrete-ecat A = record
  { Obj = A
  ; Hom = λ x y → Freestd N₁
  ; isecat = record
           { _∘_ = λ g f → f
           ; idar = λ a → 0₁
           ; ∘ext = λ f f' g g' f~f' _ → f~f'
           ; lidax = λ f → =rf
           ; ridax = λ f → =sym (contr= N₁-isContr f)
           ; assoc = λ f g h → =rf
           }
  }


small-codisc-ecat : Set 0ₗₑᵥ → small-ecategory
small-codisc-ecat = codiscrete-ecat {0ₗₑᵥ}

codisc-ecat : Set 1ₗₑᵥ → ecategory
codisc-ecat = codiscrete-ecat {1ₗₑᵥ}
