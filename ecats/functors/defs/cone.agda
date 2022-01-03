
{-# OPTIONS --without-K #-}

module ecats.functors.defs.cone where

open import Agda.Primitive
open import ecats.basic-defs.ecat-def&not
open import ecats.basic-defs.isomorphism
open import ecats.basic-props.isomorphism
open import ecats.functors.defs.efunctor-d&n
open import ecats.functors.defs.natural-transformation
open import ecats.functors.defs.natural-iso
open import ecats.functors.defs.basic-defs
open import ecats.constructions.functor-ecat
open import ecats.constructions.comma-ecat
open import ecats.constructions.discrete-ecat

-- Category of cones over a diagram
Cone/ : {ℓ₁ ℓ₂ ℓ₃ : Level}{ℂ : ecategoryₗₑᵥ ℓ₁ ℓ₂ ℓ₃}{𝕀 : small-ecategory}(D : 𝕀 diag-in ℂ)
          → ecategoryₗₑᵥ (ecat.ℓₐₗₗ ℂ) (ecat.ℓₕₒₘ ℂ) (ecat.ℓ~ ℂ)
Cone/ {ℂ = ℂ} {𝕀} D = (const-Diagr 𝕀 ℂ) ↓ₒ D

-- The category of cones over a diagram in a locally-small ecategory is locally-small
Cone/lc : {ℂ : ecategory}{𝕀 : small-ecategory}(D : 𝕀 diag-in ℂ)
             → ecategory
Cone/lc {ℂ} {𝕀} D = Cone/ {ℂ = ℂ} {𝕀} D

module Cone/ {ℓ₁ ℓ₂ ℓ₃ : Level}{ℂ : ecategoryₗₑᵥ ℓ₁ ℓ₂ ℓ₃}{𝕀 : small-ecategory}(D : 𝕀 diag-in ℂ)
             where
  private
    module 𝕀 = ecat 𝕀
    module ℂ = ecat ℂ
    module D = diagram D
    module Cn/D = ecat (Cone/ D)
  --tr→sq : (f : ∀ i → || ℂ.Hom Vx (D.ₒ i) ||){i j : 𝕀.Obj}(ij : || 𝕀.Hom i j ||)
    --         → D.ₐ ij ℂ.∘ f i ℂ.~ f j → D.ₐ ij ℂ.∘ f i ℂ.~ f j ℂ.∘ ℂ.idar Vx
  -- renaming the components of the natural transformation
  module ₒ (cone : Cn/D.Obj) where
    open funct-slice-ecat.ₒ (const-Diagr 𝕀 ℂ) D cone renaming (L to Vx; ar to sides) public
    module sides = natural-transformation sides
    leg : (i : 𝕀.Obj) → || ℂ.Hom Vx (D.ₒ i) ||
    leg = λ i → sides.fnc {i}
    tr : {i j : 𝕀.Obj}(ij : || 𝕀.Hom i j ||) → D.ₐ ij ℂ.∘ leg i ℂ.~ leg j
    tr = λ ij → sides.nat ij ˢ ⊙ rid
       where open ecategory-aux-only ℂ using (_⊙_; _ˢ; rid)
  module ₐ {cone cone' : Cn/D.Obj}(cone-ar : || Cn/D.Hom cone cone' ||) where
    open funct-slice-ecat.ₐ (const-Diagr 𝕀 ℂ) D cone-ar renaming (arL to ar) public
  if-tr-then-ob : {A : ℂ.Obj}{f : (I : 𝕀.Obj) → || ℂ.Hom A (D.ₒ I) ||}
                      → (∀ {i} {j} ij → D.ₐ ij ℂ.∘ f i ℂ.~ f j)
                        → Cn/D.Obj
  if-tr-then-ob {A} {f} tr = record
    { L = A
    ; ar = record
         { fnc = λ {I} → f I
         ; nat = λ {I} {J} IJ → ridgen (tr IJ ˢ)
         }
    }
    where open ecategory-aux-only ℂ using (ridgen; _ˢ)
  if-tr-then-ar : (cn cn' : Cn/D.Obj){f : || ℂ.Hom (ₒ.Vx cn) (ₒ.Vx cn') ||}
                      → (∀ i → ₒ.leg cn' i ℂ.∘ f ℂ.~ ₒ.leg cn i)
                        → || Cn/D.Hom cn cn' ||
  if-tr-then-ar cn cn' {f} pf = record { arL = f ; tr = pf }
  ar-is-mor-dom : (cn : Cn/D.Obj){A : ℂ.Obj}
                      → || ℂ.Hom A (ₒ.Vx cn) || → Cn/D.Obj
  ar-is-mor-dom cn {A} f = if-tr-then-ob {f = λ I → leg I ℂ.∘ f}
                                         λ {I} {J} IJ → ass ⊙ ∘e r (tr IJ)
                         where open ecategory-aux-only ℂ using (_⊙_; ∘e; ass; r)
                               open ₒ cn
  ar-is-mor : (cn : Cn/D.Obj){A : ℂ.Obj}(f : || ℂ.Hom A (ₒ.Vx cn) ||)
                  → || Cn/D.Hom (ar-is-mor-dom cn f) cn ||
  ar-is-mor cn f = if-tr-then-ar ((ar-is-mor-dom cn f)) cn (λ I → r)
                 where open ecategory-aux-only ℂ using (r)                       
  open ecat (Cone/ D) public
  --open ecategory-aux (Cone/ D) public
-- end Cone/

{- not sure it's useful stuff
module cone-defs {ℓ₁ ℓ₂ ℓ₃ : Level}(ℂ : ecategoryₗₑᵥ ℓ₁ ℓ₂ ℓ₃) where
  private
    module ℂ = ecat ℂ
    module nt = natural-transformation
  _is-vertex-over_ : (Vx : ℂ.Obj){𝕀 : small-ecategory}(D : 𝕀 diag-in ℂ) → Set (ℓ₂ ⊔ ℓ₃)
  _is-vertex-over_ Vx {𝕀} D = Vx ₒis-over
                             where open funct-slice-ecat-defs (const-Diagr 𝕀 ℂ) D
  _is-cone-mor/_[_,_] : {Vx Vx' : ℂ.Obj}(f : || ℂ.Hom Vx Vx' ||)
                        {𝕀 : small-ecategory}(D : 𝕀 diag-in ℂ)
                          → Vx is-vertex-over D → Vx' is-vertex-over D
                      --{x : Vx is-vertex-over D}{x' : Vx' is-vertex-over D}
                        --→ 
                            → Set ℓ₃
  _is-cone-mor/_[_,_] f {𝕀} D x x' = f ₐis-over[ x , x' ]
                                  where open funct-slice-ecat-defs (const-Diagr 𝕀 ℂ) D
{-
  is-cone-mor-pf : {Vx Vx' : ℂ.Obj}{f : || ℂ.Hom Vx Vx' ||}
                   {𝕀 : small-ecategory}(D : 𝕀 diag-in ℂ)
                   {x : Vx is-vertex-over D}{x' : Vx' is-vertex-over D}
                     → ((I : 𝕀.Obj) → nt.fnc x' {I} ℂ.∘ f ℂ.~ nt.fnc x {I})
                       → f is-cone-mor/ D [ x , x' ]
  is-cone-mor-pf D pf = pf
-}

  mk-cone : {𝕀 : small-ecategory}(D : 𝕀 diag-in ℂ){Vx : ℂ.Obj}
               → Vx is-vertex-over D → Cone/.Obj D
  mk-cone D {Vx} isVx = record
    { L = Vx
    ; ar = isVx
    }
  mk-cone-mor : {𝕀 : small-ecategory}(D : 𝕀 diag-in ℂ)(cn cn' : Cone/.Obj D)
                {f : || ℂ.Hom (Cone/.ₒ.Vx cn) (Cone/.ₒ.Vx cn') ||}
                  → f is-cone-mor/ D [ Cone/.ₒ.sides cn , Cone/.ₒ.sides cn' ]
                    → || Cone/.Hom D cn cn' ||
  mk-cone-mor D cn cn' {f} pf = record
    { arL = f
    ; tr = pf
    }
-- end cone-defs
-}

-- An efunctor maps cones into cones
Fcone : {ℓ₁ ℓ₂ ℓ₃ : Level}{ℂ : ecategoryₗₑᵥ ℓ₁ ℓ₂ ℓ₃}{ℓ₄ ℓ₅ ℓ₆ : Level}{𝔻 : ecategoryₗₑᵥ ℓ₄ ℓ₅ ℓ₆}
        (F : efunctorₗₑᵥ ℂ 𝔻){𝕀 : small-ecategory}(D : 𝕀 diag-in ℂ)
            → Cone/.Obj D → Cone/.Obj (F ○ D)
Fcone F {𝕀} D C = Cn/FD.if-tr-then-ob {f = λ I → F.ₐ (C.leg I)} (λ IJ → F.∘ax (C.tr IJ))
                where module F = efunctor-aux F
                      module Cn/FD = Cone/ (F ○ D)
                      module C = Cone/.ₒ D C


module cone-pushforward-defs {ℓ₁ ℓ₂ ℓ₃ : Level}{ℂ : ecategoryₗₑᵥ ℓ₁ ℓ₂ ℓ₃}
                             {𝕀 : small-ecategory}{D D' : 𝕀 diag-in ℂ}(α : D ⇒ D')
                             where
  private
    module ℂ = ecat ℂ
    module 𝕀 = ecat 𝕀
    module D = efctr D
    module D' = efctr D'
    module α = natural-transformation α
    module Cn/D = Cone/ D
    module Cn/D' = Cone/ D'

  pushf-ob : Cn/D.Obj → Cn/D'.Obj
  pushf-ob cn = record
    { L = cn.Vx
    ; ar = natt-vcmp α cn.sides
    }
    where module cn = Cn/D.ₒ cn
  pushf-ar : {cn₁ cn₂ : Cn/D.Obj} → || Cn/D.Hom cn₁ cn₂ ||
                      → || Cn/D'.Hom (pushf-ob cn₁) (pushf-ob cn₂) ||
  pushf-ar {cn₁} {cn₂} f = record
    { arL = f.ar
    ; tr = λ I → ~proof
         Cn/D'.ₒ.leg (pushf-ob cn₂) I ℂ.∘ f.ar   ~[ assˢ ] /
         α.fnc ℂ.∘ Cn/D.ₒ.leg cn₂ I ℂ.∘ f.ar      ~[ ∘e (f.tr I) r ]∎
         Cn/D'.ₒ.leg (pushf-ob cn₁) I ∎
    }
    where open ecategory-aux-only ℂ
          module f = Cn/D.ₐ f
-- end cone-pushforward-defs

cone-pushforward : {ℓ₁ ℓ₂ ℓ₃ : Level}{ℂ : ecategoryₗₑᵥ ℓ₁ ℓ₂ ℓ₃}
                   {𝕀 : small-ecategory}{D D' : 𝕀 diag-in ℂ}
                     → D ⇒ D' → efunctorₗₑᵥ (Cone/ D) (Cone/ D')
cone-pushforward {ℂ = ℂ} α = record
    { FObj = pushf-ob
    ; FHom = pushf-ar
    ; isF = record
          { ext = λ eq → eq
          ; id = λ {_} → r
          ; cmp = λ _ _ → r
          }
    }
    where open cone-pushforward-defs α
          open ecategory-aux-only ℂ using (r)

module cone-iso-trsp-defs {ℓ₁ ℓ₂ ℓ₃ : Level}{ℂ : ecategoryₗₑᵥ ℓ₁ ℓ₂ ℓ₃}
                          {𝕀 : small-ecategory}{D D' : 𝕀 diag-in ℂ}(D≅D' : D ≅ₐ D')
                          where
  private
    module 𝕀 = ecat 𝕀
    module ℂ where
      open ecat ℂ public
      open iso-defs ℂ public
      open iso-props ℂ public
    module D = efctr D
    module D' = efctr D'
    module D≅D' = natural-iso D≅D'
    module Cn/D where
      open Cone/ D public
      open iso-defs (Cone/ D) public
      open iso-props (Cone/ D) public
    module Cn/D' where
      open Cone/ D' public
      open iso-defs (Cone/ D') public
      open iso-props (Cone/ D') public
  trsp : efunctorₗₑᵥ (Cone/ D) (Cone/ D')
  trsp = cone-pushforward D≅D'.natt
  trsp⁻¹ : efunctorₗₑᵥ (Cone/ D') (Cone/ D)
  trsp⁻¹ = cone-pushforward D≅D'.natt⁻¹
  private
    module trsp = efctr trsp
    module trsp⁻¹ = efctr trsp⁻¹
    module tt⁻¹ = efctr (trsp ○ trsp⁻¹)
    module t⁻¹t = efctr (trsp⁻¹ ○ trsp)

  idcod : trsp ○ trsp⁻¹ ≅ₐ IdF
  idcod = mk-natiso {a} {b} aisob anat
        where open natural-iso-defs (trsp ○ trsp⁻¹) IdF
              a : {cn' : Cn/D'.Obj} → || Cn/D'.Hom (tt⁻¹.ₒ cn') cn' ||
              a {cn'} = record
                { arL = ℂ.idar cn'.Vx
                ; tr = λ I → ~proof
                     cn'.leg I ℂ.∘ ℂ.idar cn'.Vx               ~[ ridgen (lidggˢ r D≅D'.idcod) ] /
                     (D≅D'.fnc ℂ.∘ D≅D'.fnc⁻¹) ℂ.∘ cn'.leg I   ~[ assˢ ]∎
                     tt⁻¹cn'.leg I ∎
                }
                where open ecategory-aux-only ℂ
                      module cn' = Cn/D'.ₒ cn'
                      module tt⁻¹cn' = Cn/D'.ₒ (tt⁻¹.ₒ cn')
              b : {cn' : Cn/D'.Obj} → || Cn/D'.Hom cn' (tt⁻¹.ₒ cn') ||
              b {cn'} = record
                { arL = ℂ.idar cn'.Vx
                ; tr = λ I → ~proof
                     tt⁻¹cn'.leg I ℂ.∘ ℂ.idar cn'.Vx            ~[ ridgen ass ] /
                     (D≅D'.fnc ℂ.∘ D≅D'.fnc⁻¹) ℂ.∘ cn'.leg I   ~[ lidgg r D≅D'.idcod ]∎
                     cn'.leg I ∎
                }
                where open ecategory-aux-only ℂ
                      module cn' = Cn/D'.ₒ cn'
                      module tt⁻¹cn' = Cn/D'.ₒ (tt⁻¹.ₒ cn')
              aisob : {cn' : Cn/D'.Obj} → Cn/D'.is-iso-pair (a {cn'}) (b {cn'})
              aisob {cn'} = record
                { iddom = rid
                ; idcod = rid
                }
                where open ecategory-aux-only ℂ
              anat : {cn'₁ cn'₂ : Cn/D'.Obj}(f : || Cn/D'.Hom cn'₁ cn'₂ ||)
                           → ℂ.idar (Cn/D'.ₒ.Vx cn'₂) ℂ.∘ Cn/D'.ₐ.ar f
                                    ℂ.~ Cn/D'.ₐ.ar f ℂ.∘ ℂ.idar (Cn/D'.ₒ.Vx cn'₁)
              anat f = lidgen ridˢ
                     where open ecategory-aux-only ℂ

  iddom : trsp⁻¹ ○ trsp ≅ₐ IdF
  iddom = mk-natiso {a} {b} aisob anat
        where open natural-iso-defs (trsp⁻¹ ○ trsp) IdF
              a : {cn : Cn/D.Obj} → || Cn/D.Hom (t⁻¹t.ₒ cn) cn ||
              a {cn} = record
                { arL = ℂ.idar cn.Vx
                ; tr = λ I → ~proof
                     cn.leg I ℂ.∘ ℂ.idar cn.Vx               ~[ ridgen (lidggˢ r D≅D'.iddom) ] /
                     (D≅D'.fnc⁻¹ ℂ.∘ D≅D'.fnc) ℂ.∘ cn.leg I   ~[ assˢ ]∎
                     t⁻¹tcn.leg I ∎
                }
                where open ecategory-aux-only ℂ
                      module cn = Cn/D.ₒ cn
                      module t⁻¹tcn = Cn/D.ₒ (t⁻¹t.ₒ cn)
              b : {cn : Cn/D.Obj} → || Cn/D.Hom cn (t⁻¹t.ₒ cn) ||
              b {cn} = record
                { arL = ℂ.idar cn.Vx
                ; tr = λ I → ~proof
                     t⁻¹tcn.leg I ℂ.∘ ℂ.idar cn.Vx            ~[ ridgen ass ] /
                     (D≅D'.fnc⁻¹ ℂ.∘ D≅D'.fnc) ℂ.∘ cn.leg I   ~[ lidgg r D≅D'.iddom ]∎
                     cn.leg I ∎
                }
                where open ecategory-aux-only ℂ
                      module cn = Cn/D.ₒ cn
                      module t⁻¹tcn = Cn/D.ₒ (t⁻¹t.ₒ cn)
              aisob : {cn : Cn/D.Obj} → Cn/D.is-iso-pair (a {cn}) (b {cn})
              aisob {cn} = record
                { iddom = rid
                ; idcod = rid
                }
                where open ecategory-aux-only ℂ
              anat : {cn₁ cn₂ : Cn/D.Obj}(f : || Cn/D.Hom cn₁ cn₂ ||)
                           → ℂ.idar (Cn/D.ₒ.Vx cn₂) ℂ.∘ Cn/D.ₐ.ar f
                                    ℂ.~ Cn/D.ₐ.ar f ℂ.∘ ℂ.idar (Cn/D.ₒ.Vx cn₁)
              anat f = lidgen ridˢ
                     where open ecategory-aux-only ℂ    
-- end cone-iso-trsp-defs


cone-iso-trsp : {ℓ₁ ℓ₂ ℓ₃ : Level}{ℂ : ecategoryₗₑᵥ ℓ₁ ℓ₂ ℓ₃}
                {𝕀 : small-ecategory}{D D' : 𝕀 diag-in ℂ}
                  → D ≅ₐ D' → Cone/ D ≡ᶜᵃᵗ Cone/ D'
cone-iso-trsp D≅D = record
  { a12 = trsp
  ; a21 = trsp⁻¹
  ; iseqvpair = record
              { ι1 = idcod
              ; ι2 = iddom
              }
  }
  where open cone-iso-trsp-defs D≅D




-- Category of spans over a family of objects
Span/ : {I : Set}{ℓ₁ ℓ₂ ℓ₃ : Level}(ℂ : ecategoryₗₑᵥ ℓ₁ ℓ₂ ℓ₃)(D : I → ecat.Obj ℂ)
             → ecategoryₗₑᵥ (ecat.ℓₙₒ~ ℂ) (ecat.ℓₕₒₘ ℂ) (ecat.ℓ~ ℂ)
Span/ {I} ℂ D = (const-discDiagr I ℂ) ↓ₒ D

module Span/ {I : Set}{ℓ₁ ℓ₂ ℓ₃ : Level}(ℂ : ecategoryₗₑᵥ ℓ₁ ℓ₂ ℓ₃)(D : I → ecat.Obj ℂ) where
  private
    module ℂ = ecat ℂ
    module Sp/D = ecat (Span/ ℂ D)
  -- renaming the components of the natural transformation
  module ₒ (span : Sp/D.Obj) = funct-slice-ecat.ₒ (const-discDiagr I ℂ) D span
                             renaming (L to Vx; ar to leg)
  if-tr-then-ar : (cn cn' : Sp/D.Obj){f : || ℂ.Hom (ₒ.Vx cn) (ₒ.Vx cn') ||}
                      → (∀ i → ₒ.leg cn' i ℂ.∘ f ℂ.~ ₒ.leg cn i)
                        → || Sp/D.Hom cn cn' ||
  if-tr-then-ar cn cn' {f} pf = record { arL = f ; tr = pf }
  module ₐ {span span' : Sp/D.Obj}(span-ar : || Sp/D.Hom span span' ||)
         = funct-slice-ecat.ₐ (const-discDiagr I ℂ) D span-ar
         renaming (arL to ar)
  open ecategory-aux (Span/ ℂ D) public

-- an efunctor maps spans into spans
Fspan : {ℓ₁ ℓ₂ ℓ₃ : Level}{ℂ : ecategoryₗₑᵥ ℓ₁ ℓ₂ ℓ₃}{ℓ₄ ℓ₅ ℓ₆ : Level}{𝔻 : ecategoryₗₑᵥ ℓ₄ ℓ₅ ℓ₆}
        (F : efunctorₗₑᵥ ℂ 𝔻){I : Set}(D : I → ecat.Obj ℂ)
            → Span/.Obj ℂ D → Span/.Obj 𝔻 (λ i → efctr.ₒ F (D i))
Fspan F {𝕀} D C = record
  { L = F.ₒ C.Vx
  ; ar = λ i → F.ₐ (C.leg i)
  }
  where module F = efunctor-aux F
        module C = Span/.ₒ _ D C

-- underlying family of a cone
cone→span : {𝕀 : small-ecategory}{ℓ₁ ℓ₂ ℓ₃ : Level}{ℂ : ecategoryₗₑᵥ ℓ₁ ℓ₂ ℓ₃}{D : 𝕀 diag-in ℂ}
                     → Cone/.Obj D → Span/.Obj ℂ (efctr.ₒ D)
cone→span {D = D} cone = record
         { L = cone.Vx
         ; ar = cone.leg
         }
         where module cone = Cone/.ₒ D cone


-- a span is a cone over a discrete diagram
span→cone : {I : Set}{ℓ₁ ℓ₂ ℓ₃ : Level}(ℂ : ecategoryₗₑᵥ ℓ₁ ℓ₂ ℓ₃){D : I → ecat.Obj ℂ}
               → Span/.Obj ℂ D → Cone/.Obj (disc-ecat-lift-efctr ℂ D)
span→cone {I} ℂ {D} sp = record
  { L = sp.Vx
  ; ar = disc-ecat-lift-full ℂ {cnstDg.ₒ sp.Vx} {disc-ecat-lift-efctr ℂ D} sp.leg
  }
  where module sp = Span/.ₒ ℂ D sp
        module D = efctr (disc-ecat-lift-efctr ℂ D)
        module cnstDg = efctr (const-Diagr (discrete-ecat I) ℂ)
