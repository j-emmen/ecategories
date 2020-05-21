 
-- disable the K axiom:

{-# OPTIONS --without-K #-}

-- Agda version 2.5.4.1

module ecats.finite-limits.not.pullback where

open import ecats.basic-defs.ecat-def&not
open import ecats.basic-defs.commut-shapes
open import ecats.finite-limits.defs.pullback




-- notation for and basic properties of pullback squares

module pullback-squares-not (ℂ : ecategory) where
  open ecategory-aux ℂ
  open comm-shapes ℂ
  open pullback-defs ℂ


  module pullback-sq-not-only (pbsq : pb-square) where
    open pb-square pbsq

    ×/pbsq : pb-square
    ×/pbsq = pbsq

    ×/of : pullback-of down right
    ×/of = mkpb-of ×/ispbsq

    ×/tr₁g : {C : Obj} {h h' : || Hom C dl ||} {k : || Hom C ur ||} (pf : down ∘ h ~ right ∘ k)
                → h ~ h' → π/₁ ∘ ⟨ h , k ⟩[ pf ] ~ h'
    ×/tr₁g pf pfdl = ×/tr₁ pf ⊙ pfdl

    ×/tr₂g : {C : Obj} {h : || Hom C dl ||} {k k' : || Hom C ur ||} (pf : down ∘ h ~ right ∘ k)
                → k ~ k' → π/₂ ∘ ⟨ h , k ⟩[ pf ] ~ k'
    ×/tr₂g pf pfur = ×/tr₂ pf ⊙ pfur

    ⟨⟩uq : {C : Obj} {f : || Hom C dl ||} {g : || Hom C ur ||} {h : || Hom C ul ||} {pf : down ∘ f ~ right ∘ g}
              → π/₁ ∘ h ~ f → π/₂ ∘ h ~ g → ⟨ f , g ⟩[ pf ] ~ h
    ⟨⟩uq {pf = pf} pf1 pf2 = ×/uq (×/tr₁ pf ⊙ pf1 ˢ) (×/tr₂ pf ⊙ pf2 ˢ)

    ⟨⟩uq⟨⟩ : {C : Obj} {f f' : || Hom C dl ||} {g g' : || Hom C ur ||}
            {pf : down ∘ f ~ right ∘ g} {pf' : down ∘ f' ~ right ∘ g'}
              → f ~ f' → g ~ g' → ⟨ f , g ⟩[ pf ] ~ ⟨ f' , g' ⟩[ pf' ]
    ⟨⟩uq⟨⟩ {pf = pf} {pf'} pff pfg = ⟨⟩uq (×/tr₁ pf' ⊙ pff ˢ) (×/tr₂ pf' ⊙ pfg ˢ)

  -- end pullback-sq-not

  module pullback-sq-not (pbsq : pb-square) where
    open pb-square pbsq public
    open pullback-sq-not-only pbsq public
  -- end module pullback-sq-not

  module pullback-of-not {I A B : Obj} {a : || Hom A I ||} {b : || Hom B I ||} (pbof : pullback-of a b) where
    open pullback-of pbof public
    open pullback-sq-not-only (mkpb-sq ×/ispbsq) public
  -- end module pullback-of-not


  module ×/ₐdef {I A₁ B₁ : Obj} {a₁ : || Hom A₁ I ||} {b₁ : || Hom B₁ I ||} {A₂ B₂ : Obj} {a₂ : || Hom A₂ I ||} {b₂ : || Hom B₂ I ||}
                 (pbsq₁ : pullback-of a₁ b₁) (pbsq₂ : pullback-of a₂ b₂) where
    private
      module ₁ = pullback-sq-not (mkpb-sq (pullback-of.×/ispbsq pbsq₁))
      module ₂ = pullback-sq-not (mkpb-sq (pullback-of.×/ispbsq pbsq₂))

    ×/ₐcanpf : {f : || Hom A₂ A₁ ||} {g : || Hom B₂ B₁ ||}
                   → a₁ ∘ f ~ a₂ → b₁ ∘ g ~ b₂
                     → a₁ ∘ f ∘ ₂.π/₁ ~ b₁ ∘ g ∘ ₂.π/₂
    ×/ₐcanpf {f} {g} pff pfg = ~proof a₁ ∘ f ∘ ₂.π/₁      ~[ ass ⊙ ∘e r pff ] /
                                      a₂ ∘ ₂.π/₁        ~[ ₂.×/sqpf ] /
                                      b₂ ∘ ₂.π/₂       ~[ ∘e r (pfg ˢ) ⊙ assˢ ]∎
                                      b₁ ∘ g ∘ ₂.π/₂ ∎

    infixr 6 _×/ₐ_[_,_]
    _×/ₐ_[_,_] : (f : || Hom A₂ A₁ ||) (g : || Hom B₂ B₁ ||)
                     → a₁ ∘ f ~ a₂ → b₁ ∘ g ~ b₂
                       → || Hom ₂.ul ₁.ul ||
    f ×/ₐ g [ pff , pfg ] = ₁.⟨ f ∘ ₂.π/₁ , g ∘ ₂.π/₂ ⟩[ ×/ₐcanpf pff pfg ]


    ×/ₐtr₁ : {f : || Hom A₂ A₁ ||} {g : || Hom B₂ B₁ ||}
             {pfdl : a₁ ∘ f ~ a₂} {pfur : b₁ ∘ g ~ b₂}
                       → ₁.π/₁ ∘ f ×/ₐ g [ pfdl , pfur ] ~ f ∘ ₂.π/₁
    ×/ₐtr₁ {pfdl = pfdl} {pfur}  = ₁.×/tr₁ (×/ₐcanpf pfdl pfur)

    ×/ₐtr₁ˢ : {f : || Hom A₂ A₁ ||} {g : || Hom B₂ B₁ ||}
             {pfdl : a₁ ∘ f ~ a₂} {pfur : b₁ ∘ g ~ b₂}
                       → f ∘ ₂.π/₁ ~ ₁.π/₁ ∘ f ×/ₐ g [ pfdl , pfur ]
    ×/ₐtr₁ˢ {pfdl = pfdl} {pfur}  = ₁.×/tr₁ (×/ₐcanpf pfdl pfur) ˢ

    ×/ₐtr₂ : {f : || Hom A₂ A₁ ||} {g : || Hom B₂ B₁ ||}
             {pfdl : a₁ ∘ f ~ a₂} {pfur : b₁ ∘ g ~ b₂}
                       → ₁.π/₂ ∘ f ×/ₐ g [ pfdl , pfur ] ~ g ∘ ₂.π/₂
    ×/ₐtr₂ {pfdl = pfdl} {pfur}  = ₁.×/tr₂ (×/ₐcanpf pfdl pfur)

    ×/ₐtr₂ˢ : {f : || Hom A₂ A₁ ||} {g : || Hom B₂ B₁ ||}
             {pfdl : a₁ ∘ f ~ a₂} {pfur : b₁ ∘ g ~ b₂}
                       → g ∘ ₂.π/₂ ~ ₁.π/₂ ∘ f ×/ₐ g [ pfdl , pfur ]
    ×/ₐtr₂ˢ {pfdl = pfdl} {pfur}  = ₁.×/tr₂ (×/ₐcanpf pfdl pfur) ˢ

    ×/ₐe : {f f' : || Hom A₂ A₁ ||} {g g' : || Hom B₂ B₁ ||} {pff : a₁ ∘ f ~ a₂} {pfg : b₁ ∘ g ~ b₂} {pff' : a₁ ∘ f' ~ a₂} {pfg' : b₁ ∘ g' ~ b₂}
              → f ~ f' → g ~ g' → (f ×/ₐ g [ pff , pfg ]) ~ (f' ×/ₐ g' [ pff' , pfg' ])
    ×/ₐe pf₁ pf₂ = ₁.×/uq (₁.×/tr₁ (×/ₐcanpf _ _) ⊙ ∘e r pf₁ ⊙ ₁.×/tr₁ (×/ₐcanpf _ _) ˢ)
                          (₁.×/tr₂ (×/ₐcanpf _ _) ⊙ ∘e r pf₂ ⊙ ₁.×/tr₂ (×/ₐcanpf _ _) ˢ)

  -- end ×/ₐdef


  module ×/ₐnot-only {I A₁ B₁ : Obj} {a₁ : || Hom A₁ I ||} {b₁ : || Hom B₁ I ||} {A₂ B₂ : Obj} {a₂ : || Hom A₂ I ||} {b₂ : || Hom B₂ I ||}
                       (pbsq₁ : pullback-of a₁ b₁) (pbsq₂ : pullback-of a₂ b₂) where
    private
      module ₁ = pullback-sq-not (mkpb-sq (pullback-of.×/ispbsq pbsq₁))
      module ₂ = pullback-sq-not (mkpb-sq (pullback-of.×/ispbsq pbsq₂))
      module ₂₁ = ×/ₐdef pbsq₁ pbsq₂


    module ×/ₐnot-cmp {A₃ B₃ : Obj} {a₃ : || Hom A₃ I ||} {b₃ : || Hom B₃ I ||} (pbsq₃ : pullback-of a₃ b₃) where
      private
        module ₃ = pullback-sq-not (mkpb-sq (pullback-of.×/ispbsq pbsq₃))
        module ₃₁ = ×/ₐdef pbsq₁ pbsq₃
        module ₃₂ = ×/ₐdef pbsq₂ pbsq₃

      ×/ₐcmp : {f₂₁ : || Hom A₂ A₁ ||} {g₂₁ : || Hom B₂ B₁ ||} {f₃₂ : || Hom A₃ A₂ ||} {g₃₂ : || Hom B₃ B₂ ||}
               --(pff₂₁ : a₁ ∘ f₂₁ ~ a₂) (pfg₂₁ : b₁ ∘ g₂₁ ~ b₂) (pff₃₂ : a₂ ∘ f₃₂ ~ a₃) (pfg₃₂ : b₂ ∘ g₃₂ ~ b₃)
               {pff₂₁ : a₁ ∘ f₂₁ ~ a₂} {pfg₂₁ : b₁ ∘ g₂₁ ~ b₂} {pff₃₂ : a₂ ∘ f₃₂ ~ a₃} {pfg₃₂ : b₂ ∘ g₃₂ ~ b₃}
                 → f₂₁ ₂₁.×/ₐ g₂₁ [ pff₂₁ , pfg₂₁ ] ∘ f₃₂ ₃₂.×/ₐ g₃₂ [ pff₃₂ , pfg₃₂ ]
                                  ~ (f₂₁ ∘ f₃₂) ₃₁.×/ₐ (g₂₁ ∘ g₃₂) [ ass ⊙ (∘e r pff₂₁ ⊙ pff₃₂) , ass ⊙ (∘e r pfg₂₁ ⊙ pfg₃₂) ]

      ×/ₐcmp = ₁.×/uq (ass ⊙ ∘e r ₂₁.×/ₐtr₁ ⊙ assˢ ⊙ ∘e ₃₂.×/ₐtr₁ r ⊙ ass ⊙ ₃₁.×/ₐtr₁ˢ)
                      (ass ⊙ ∘e r ₂₁.×/ₐtr₂ ⊙ assˢ ⊙ ∘e ₃₂.×/ₐtr₂ r ⊙ ass ⊙ ₃₁.×/ₐtr₂ˢ)

      ×/ₐ×/ₐ~×/ₐ : {f₂₁ : || Hom A₂ A₁ ||} {g₂₁ : || Hom B₂ B₁ ||} {f₃₂ : || Hom A₃ A₂ ||} {g₃₂ : || Hom B₃ B₂ ||}
                   {f₃₁ : || Hom A₃ A₁ ||} {g₃₁ : || Hom B₃ B₁ ||} {pff₂₁ : a₁ ∘ f₂₁ ~ a₂} {pfg₂₁ : b₁ ∘ g₂₁ ~ b₂}
                   {pff₃₂ : a₂ ∘ f₃₂ ~ a₃} {pfg₃₂ : b₂ ∘ g₃₂ ~ b₃} {pff₃₁ : a₁ ∘ f₃₁ ~ a₃} {pfg₃₁ : b₁ ∘ g₃₁ ~ b₃}
                     → f₂₁ ∘ f₃₂ ~ f₃₁ → g₂₁ ∘ g₃₂ ~ g₃₁
                       → f₂₁ ₂₁.×/ₐ g₂₁ [ pff₂₁ , pfg₂₁ ] ∘ f₃₂ ₃₂.×/ₐ g₃₂ [ pff₃₂ , pfg₃₂ ] ~ f₃₁ ₃₁.×/ₐ g₃₁ [ pff₃₁ , pfg₃₁ ]
      ×/ₐ×/ₐ~×/ₐ pff pfg = ×/ₐcmp ⊙ ₃₁.×/ₐe pff pfg

      ×/ₐ×/ₐ~×/ₐˢ : {f₂₁ : || Hom A₂ A₁ ||} {g₂₁ : || Hom B₂ B₁ ||} {f₃₂ : || Hom A₃ A₂ ||} {g₃₂ : || Hom B₃ B₂ ||}
                   {f₃₁ : || Hom A₃ A₁ ||} {g₃₁ : || Hom B₃ B₁ ||} {pff₂₁ : a₁ ∘ f₂₁ ~ a₂} {pfg₂₁ : b₁ ∘ g₂₁ ~ b₂}
                   {pff₃₂ : a₂ ∘ f₃₂ ~ a₃} {pfg₃₂ : b₂ ∘ g₃₂ ~ b₃} {pff₃₁ : a₁ ∘ f₃₁ ~ a₃} {pfg₃₁ : b₁ ∘ g₃₁ ~ b₃}
                     → f₂₁ ∘ f₃₂ ~ f₃₁ → g₂₁ ∘ g₃₂ ~ g₃₁
                       → f₃₁ ₃₁.×/ₐ g₃₁ [ pff₃₁ , pfg₃₁ ] ~ f₂₁ ₂₁.×/ₐ g₂₁ [ pff₂₁ , pfg₂₁ ] ∘ f₃₂ ₃₂.×/ₐ g₃₂ [ pff₃₂ , pfg₃₂ ]
      ×/ₐ×/ₐ~×/ₐˢ pff pfg = ×/ₐ×/ₐ~×/ₐ pff pfg ˢ

    -- end ×/ₐnot-cmp    
  -- end ×/ₐnot-only

  module ×/ₐnot {I A₁ B₁ : Obj} {a₁ : || Hom A₁ I ||} {b₁ : || Hom B₁ I ||} {A₂ B₂ : Obj} {a₂ : || Hom A₂ I ||} {b₂ : || Hom B₂ I ||}
                  (pbsq₁ : pullback-of a₁ b₁) (pbsq₂ : pullback-of a₂ b₂) where
    open ×/ₐdef pbsq₁ pbsq₂ public
    open ×/ₐnot-only pbsq₁ pbsq₂ public
  -- end ×/ₐnot

-- end pullback-squares-not





module pullbacks-aux-only {ℂ : ecategory} (pb : has-pullbacks ℂ) where
  open ecategory-aux ℂ
  open comm-shapes ℂ
  open has-pullbacks pb
  open pullback-defs ℂ
  open pullback-squares-not ℂ


  module ×/ᶜ-not-only {I A B : Obj} {a : || Hom A I ||} {b : || Hom B I ||}  = pullback-sq-not-only (mkpb-sq (×/ispbsq {a = a} {b}))
  open ×/ᶜ-not-only public

  module ×/ₐᶜdef {I A₁ B₁ : Obj} {a₁ : || Hom A₁ I ||} {b₁ : || Hom B₁ I ||} {A₂ B₂ : Obj} {a₂ : || Hom A₂ I ||} {b₂ : || Hom B₂ I ||}
                 = ×/ₐdef (pb-of a₁ b₁) (pb-of a₂ b₂)
  open ×/ₐᶜdef public

  module ×/ₐᶜnot-only {I A₁ B₁ : Obj} {a₁ : || Hom A₁ I ||} {b₁ : || Hom B₁ I ||} {A₂ B₂ : Obj} {a₂ : || Hom A₂ I ||} {b₂ : || Hom B₂ I ||}
                 = ×/ₐnot-only (pb-of a₁ b₁) (pb-of a₂ b₂)
  open ×/ₐᶜnot-only public

  module ×/ₐᶜnot-cmp {I A₁ B₁ : Obj} {a₁ : || Hom A₁ I ||} {b₁ : || Hom B₁ I ||} {A₂ B₂ : Obj} {a₂ : || Hom A₂ I ||} {b₂ : || Hom B₂ I ||}
                       {A₃ B₃ : Obj} {a₃ : || Hom A₃ I ||} {b₃ : || Hom B₃ I ||}
                       = ×/ₐnot-cmp {a₁ = a₁} {b₁} {a₂ = a₂} {b₂} (pb-of a₃ b₃)
  open ×/ₐᶜnot-cmp public


  ×/ₐidcan : {I A B : Obj} {a : || Hom A I ||} {b : || Hom B I ||}
                → idar A ×/ₐ idar B [ rid , rid ] ~ idar (a ×/ₒ b)
  ×/ₐidcan {B = B} {a = a} {b} = ×/uq (×/ₐtr₁ ⊙ lidgen ridˢ) (×/ₐtr₂ ⊙ lidgen ridˢ)

  ×/ₐid : {I A B : Obj} {a : || Hom A I ||} {b : || Hom B I ||} {f : || Hom A A ||} {g : || Hom B B ||}
          {pfdl : a ∘ f ~ a} {pfur : b ∘ g ~ b}
            → f ~ idar A → g ~ idar B → f ×/ₐ g [ pfdl , pfur ] ~ idar (a ×/ₒ b)
  ×/ₐid pff pfg =  ⟨⟩uq (lidggˢ rid pff) (lidggˢ rid pfg)

-- end module pullbacks-aux-only

module pullbacks-aux {ℂ : ecategory} (pb : has-pullbacks ℂ) where
  open has-pullbacks pb public
  open pullbacks-aux-only pb public
-- end pullbacks-aux

