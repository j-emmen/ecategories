
{-# OPTIONS --without-K #-}

module ecats.basic-props.initial where

open import tt-basics.all-basics hiding (||_||)
open import ecats.basic-defs.ecat-def&not
open import ecats.basic-defs.initial
open import ecats.functors.defs.efunctor
open import ecats.small-limits.defs.small-limit
open import ecats.concr-ecats.finite-ecat


-- the limit of all endomorphisms of a weakly initial object is initial
module weak-init2init {ℓₒ : Level}{ℂ : ecategoryₗₑᵥ ℓₒ 0ₗₑᵥ 0ₗₑᵥ}(limℂ : has-small-limits ℂ) where
  private
    module ℂ where
      open ecat ℂ public
      open initial-defs ℂ public
      open small-limit-defs ℂ public
      open Eql-in-ecat ℂ public
      open has-small-limits limℂ using (lim-of) public

  module proof {X : ℂ.Obj}(win : ℂ.is-weak-initial X) where
    private
      module X = ℂ.is-weak-initial win

    EndX : small-ecategory
    EndX = record
      { Obj = N₁ + N₁
      ; Hom = H
      ; isecat = record
                     { _∘_ = λ {i} {j} {k} → cmp {i} {j} {k}
                     ; idar = idar
                     ; ∘ext = λ {i} {j} {k} → ext {i} {j} {k}
                     ; lidax = λ {i} {j} → lid {i} {j}
                     ; ridax = λ {i} {j} → rid {i} {j}
                     ; assoc = λ {i} {j} {k} {l} → ass {i} {j} {k} {l}
                     }
      }
      where H : N₁ + N₁ → N₁ + N₁ → setoid
            H (inl x₁) (inl x) = Freestd N₁
            H (inr x₁) (inl x) = Freestd N₀
            H (inl x₁) (inr x) = ℂ.Hom X X
            H (inr x₁) (inr x) = Freestd N₁
            cmp : {i j k : N₁ + N₁} → || H j k || → || H i j || → || H i k ||
            cmp {i} {inl 0₁} {inl 0₁} = λ _ f → f
            cmp {i} {inr x₁} {inl x} = N₀rec
            cmp {inl 0₁} {inl 0₁} {inr x} = λ g _ → g
            cmp {inr x₂} {inl x₁} {inr x} = λ g → N₀rec
            cmp {i} {inr 0₁} {inr 0₁} = λ _ f → f
            idar : (i : N₁ + N₁) → || H i i ||
            idar = sumrec {C = λ i → || H i i ||} (λ x → x) (λ x → x)
            ext : {a b c : N₁ + N₁} (f f' : || H a b ||) (g g' : || H b c ||)
                     → < H a b > f ~ f' → < H b c > g ~ g' → < H a c > cmp {a} {b} {c} g f ~ cmp {a} {b} {c} g' f'
            ext {a} {inl 0₁} {inl 0₁} f f' g g' eqf eqg = eqf
            ext {inl 0₁} {inl 0₁} {inr x} f f' g g' eqf eqg = eqg
            ext {a} {inr 0₁} {inr 0₁} f f' g g' eqf eqg = eqf
            lid : {a b : N₁ + N₁}(f : || H a b ||)
                     → < H a b > cmp {a} {b} {b} (idar b) f ~ f
            lid {a} {inl 0₁} = λ _ → setoid-aux.r (H a (inl 0₁))
            lid {a} {inr 0₁} = λ _ → setoid-aux.r (H a (inr 0₁))
            rid : {a b : N₁ + N₁}(f : || H a b ||)
                     → < H a b > cmp {a} {a} {b} f (idar a) ~ f
            rid {inl 0₁} {inl 0₁} = λ f → pj2 N₁-isContr f ⁻¹
            rid {inr x₁} {inl x} = N₀rec
            rid {inl 0₁} {inr x} = λ f → ecategory-aux.r ℂ
            rid {inr 0₁} {inr 0₁} = λ f → pj2 N₁-isContr f ⁻¹
            ass : {a b c d : N₁ + N₁}(f : || H a b ||)(g : || H b c ||)(h : || H c d ||)
                     → < H a d > cmp {a} {c} {d} h (cmp {a} {b} {c} g f)
                                     ~ cmp {a} {b} {d} (cmp {b} {c} {d} h g) f
            ass {a} {b} {inl 0₁} {inl 0₁} = λ _ _ _ → setoid-aux.r (H a (inl 0₁))
            ass {a} {b} {inr x₁} {inl x} = λ _ _ → N₀rec
            ass {a} {inl 0₁} {inl 0₁} {inr x} = λ _ _ _ → setoid-aux.r (H a (inr x))
            ass {a} {inr x₂} {inl x₁} {inr x} = λ _ → N₀rec
            ass {a} {b} {inr 0₁} {inr 0₁} = λ _ _ _ → setoid-aux.r (H a (inr 0₁))
    private
      module EndX where
        open ecat EndX public
        l r : Obj
        l = inl 0₁
        r = inr 0₁

    EndX-Dg : EndX diag-in ℂ
    EndX-Dg = record
      { FObj = λ _ → X
      ; FHom = λ {i} {j} → FH {i} {j}
      ; isF = record
            { ext = λ {i} {j} → ext {i} {j}
            ; id = λ {i} → id {i}
            ; cmp = λ {i} {j} {k} → cmp {i} {j} {k}
            }
      }
      where FH : {i j : EndX.Obj} → || EndX.Hom i j || → || ℂ.Hom X X ||
            FH {inl 0₁} {inl 0₁} = λ _ → ℂ.idar X
            FH {inr x₁} {inl x} = N₀rec
            FH {inl x₁} {inr x} = λ f → f
            FH {inr x₁} {inr x} = λ _ → ℂ.idar X
            ext : {i j : EndX.Obj}{f f' : || EndX.Hom i j ||}
                     → < EndX.Hom i j > f ~ f' → FH {i} {j} f ℂ.~ FH {i} {j} f'
            ext {inl 0₁} {inl 0₁} = λ _ → ecategory-aux.r ℂ
            ext {inl 0₁} {inr x} = λ eq → eq
            ext {inr x₁} {inr x} = λ _ → ecategory-aux.r ℂ
            id : {i : EndX.Obj} → FH {i} {i} (EndX.idar i) ℂ.~ ℂ.idar X
            id {inl 0₁} = ecategory-aux.r ℂ
            id {inr x} = ecategory-aux.r ℂ
            cmp : {i j k : EndX.Obj}(f : || EndX.Hom i j ||)(g : || EndX.Hom j k ||)
                     → FH {j} {k} g ℂ.∘ FH {i} {j} f ℂ.~ FH {i} {k} (EndX._∘_ {i} {j} {k} g f)
            cmp {i} {inl 0₁} {inl 0₁} = λ _ _ → ecategory-aux.lid ℂ
            cmp {i} {inr x₁} {inl x} = λ _ → N₀rec
            cmp {inl 0₁} {inl 0₁} {inr x} = λ _ _ → ecategory-aux.rid ℂ
            cmp {inr x₂} {inl x₁} {inr x} = N₀rec
            cmp {i} {inr 0₁} {inr 0₁} = λ _ _ → ecategory-aux.lid ℂ

    LimEnX : ℂ.limit-of EndX-Dg
    LimEnX = ℂ.lim-of EndX-Dg
    --private
    module LimEnX where
      open ℂ.limit-of LimEnX public
      πl πr : || ℂ.Hom Vx X ||
      πl = π EndX.l
      πr = π EndX.r
      πl~πr : πl ℂ.~ πr
      πl~πr = lidˢ ⊙ tr {EndX.l} {EndX.r} (ℂ.idar X)
            where open ecategory-aux-only ℂ using (_⊙_; lidˢ)
      oneπ : (I : EndX.Obj) → π I ℂ.~ πr
      oneπ (inl 0₁) = πl~πr
      oneπ (inr 0₁) = r
                    where open ecategory-aux-only ℂ using (r)

    LimEnX-uq : {Y : ℂ.Obj}(f f' : || ℂ.Hom LimEnX.Vx Y ||) → f ℂ.~ f'
    LimEnX-uq f f' = ~proof f                        ~[ ridggˢ r sct-pf ] /
                            f ℂ.∘ e.ar ℂ.∘ sct    ~[ ass ⊙ ∘e r e.eq ⊙ assˢ ] /
                            f' ℂ.∘ e.ar ℂ.∘ sct   ~[ ridgg r sct-pf ]∎
                            f' ∎
                  where open ecategory-aux-only ℂ
                        module e where
                          open ℂ.limit-of (ℂ.lim-of (ℂ.arr2diag f f')) public
                          ar : || ℂ.Hom Vx LimEnX.Vx ||
                          ar = π Eql-cat.dom
                          eq : f ℂ.∘ ar ℂ.~ f' ℂ.∘ ar
                          eq = tr {Eql-cat.dom} {Eql-cat.cod} Eql-cat.a₁0
                               ⊙ (tr {Eql-cat.dom} {Eql-cat.cod} Eql-cat.a₂0 ˢ)
                        sct : || ℂ.Hom LimEnX.Vx e.Vx ||
                        sct = X.ar e.Vx ℂ.∘ LimEnX.πl
                        sct-pf : e.ar ℂ.∘ sct ℂ.~ ℂ.idar LimEnX.Vx
                        sct-pf = LimEnX.π-jm (λ I → ridgenˢ (aux I))
                               where xe : (I : EndX.Obj) → || ℂ.Hom X X ||
                                     xe I = LimEnX.π I ℂ.∘ e.ar ℂ.∘ X.ar e.Vx
                                     aux : (I : EndX.Obj)
                                              → LimEnX.π I ℂ.∘ e.ar ℂ.∘ sct ℂ.~ LimEnX.π I
                                     aux I = ~proof
                                       LimEnX.π I ℂ.∘ e.ar ℂ.∘ sct    ~[ ∘e ass r ⊙ ass ] /
                                       xe I ℂ.∘ LimEnX.πl
                                         ~[ LimEnX.tr {EndX.l} {EndX.r} (xe I) ⊙ LimEnX.oneπ I ˢ ]∎
                                       LimEnX.π I ∎


    LimEnX-init : ℂ.is-initial LimEnX.Vx
    LimEnX-init = record
      { ø = λ Y → X.ar Y ℂ.∘ LimEnX.π EndX.l
      ; øuq = λ {Y} f → LimEnX-uq f (X.ar Y ℂ.∘ LimEnX.π EndX.l)
      }
  -- end proof

  ob : {X : ℂ.Obj}(win : ℂ.is-weak-initial X) → ℂ.Obj
  ob win = LimEnX.Vx
         where open proof win
  is-init : {X : ℂ.Obj}(win : ℂ.is-weak-initial X) → ℂ.is-initial (ob win)
  is-init win = LimEnX-init
              where open proof win
-- end weak-init2init
