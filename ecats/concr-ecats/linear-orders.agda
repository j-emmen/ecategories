
{-# OPTIONS --without-K #-}

module ecats.concr-ecats.linear-orders where

open import tt-basics.all-basics renaming (||_|| to ||_||std)
open import ecats.basic-defs.ecat-def&not
--open import ecats.basic-defs.isomorphism
--open import ecats.basic-defs.commut-shapes
open import ecats.basic-defs.preorder
--open import ecats.basic-props.isomorphism
--open import ecats.constructions.free-ecat-on-graph
--open import ecats.concr-ecats.Std-lev
open import ecats.functors.defs.efunctor
--open import ecats.functors.defs.natural-iso
--open import ecats.functors.defs.natural-transformation


---------------------------
-- Countable linear orders
---------------------------

module finite-linear-preorders-data where
  𝔽Hom : (n : N) → Fin n → Fin n → setoid {0ₗₑᵥ} {0ₗₑᵥ}
  𝔽Hom (s O) x y = Freestd N₁
  𝔽Hom (s (s n)) (inl x) (inl y) = 𝔽Hom (s n) x y
  𝔽Hom (s (s n)) (inl x) (inr y) = Freestd N₁
  𝔽Hom (s (s n)) (inr x) (inl y) = Freestd N₀
  𝔽Hom (s (s n)) (inr x) (inr y) = Freestd N₁

  𝔽id :  (n : N)(i : Fin n) → || 𝔽Hom n i i ||
  𝔽id (s O) i = i
  𝔽id (s (s n)) (inl x) = 𝔽id (s n) x
  𝔽id (s (s n)) (inr x) = x

  𝔽cmp : (n : N){i j k : Fin n} → || 𝔽Hom n j k || → || 𝔽Hom n i j ||
            → || 𝔽Hom n i k ||
  𝔽cmp (s O) {i} {j} {k} jk ij = 0₁
  𝔽cmp (s (s n)) {inl x} {inl y} {inl z} jk ij = 𝔽cmp (s n) jk ij
  𝔽cmp (s (s n)) {inl x} {inl y} {inr z} jk ij = 0₁
  𝔽cmp (s (s n)) {inl x} {inr y} {inr z} jk ij = 0₁
  𝔽cmp (s (s n)) {inr x} {inr x₁} {inr x₂} jk ij = 0₁

  ispreorder : (n : N){i j : Fin n}{ij ij' :  || 𝔽Hom n i j ||} → < 𝔽Hom n i j > ij ~ ij'
  ispreorder (s O) {i} {j} {ij} {ij'} = isContr→isProp N₁-isContr ij ij'
  ispreorder (s (s n)) {inl x} {inl x₁} {ij} {ij'} = ispreorder (s n) {ij = ij} {ij'}
  ispreorder (s (s n)) {inl x} {inr x₁} {ij} {ij'} = isContr→isProp N₁-isContr ij ij'
  ispreorder (s (s n)) {inr x} {inr x₁} {ij} {ij'} = isContr→isProp N₁-isContr ij ij'
-- end finite-linear-preorders-data


FinLinOrd : (n : N) → small-ecategory
FinLinOrd n = record
            { Obj = Fin n
            ; Hom = 𝔽Hom n
            ; isecat = record
                     { _∘_ = 𝔽cmp n
                     ; idar = 𝔽id n
                     ; ∘ext = λ f f' g g' x x₁ → ispreorder n
                     ; lidax = λ f → ispreorder n
                     ; ridax = λ f → ispreorder n
                     ; assoc = λ f g h → ispreorder n
                     }
            }
            where open finite-linear-preorders-data

FinLinOrd-is-preorder : (n : N) → is-preorder (FinLinOrd n)
FinLinOrd-is-preorder n = record { pf = ispreorder n }
                      where open finite-linear-preorders-data

𝔽inPreOrd : (n : N) → small-preorder
𝔽inPreOrd n = record
             { ℂ = FinLinOrd n
             ; ispreord = FinLinOrd-is-preorder n
             }

module FinLinOrd (n : N) where
  open ecategory-aux (FinLinOrd n) public
  module ispreord = is-preorder (FinLinOrd-is-preorder n)

0ᶜᵃᵗ 1ᶜᵃᵗ 2ᶜᵃᵗ 3ᶜᵃᵗ 4ᶜᵃᵗ ⇨ : small-ecategory
0ᶜᵃᵗ = FinLinOrd O
1ᶜᵃᵗ = FinLinOrd (s O)
2ᶜᵃᵗ = FinLinOrd (s (s O))
3ᶜᵃᵗ = FinLinOrd (s (s (s O)))
4ᶜᵃᵗ = FinLinOrd (s (s (s (s O))))
⇨ = 2ᶜᵃᵗ

module ωCat-data where
  Hom : N → N → setoid {0ₗₑᵥ} {0ₗₑᵥ}
  Hom O O = Freestd N₁
  Hom O (s n) = Freestd N₁
  Hom (s m) O = Freestd N₀
  Hom (s m) (s n) = Hom m n

  suc :  (n : N) → || Hom n (s n) ||
  suc O = 0₁
  suc (s n) = suc n

  idar : (n : N) → || Hom n n ||
  idar O = 0₁
  idar (s n) = idar n

  cmp : {a b c : N} → || Hom b c || → || Hom a b || → || Hom a c ||
  cmp {O} {O} {O} bc ab = 0₁
  cmp {O} {O} {s c} bc ab = 0₁
  cmp {O} {s b} {s c} bc ab = 0₁
  cmp {s a} {s b} {s c} bc ab = cmp {a} bc ab

  ispreorder : {m n : N}{f f' : || Hom m n ||} → < Hom m n > f ~ f'
  ispreorder {O} {O} {f} {f'} = isContr→isProp N₁-isContr f f'
  ispreorder {O} {s n} {f} {f'} = isContr→isProp N₁-isContr f f'
  ispreorder {s m} {s n} {f} {f'} = ispreorder {m} {n} {f} {f'}
-- end ωCat-data

ω : small-ecategory
ω = record
  { Obj = N
  ; Hom = Hom
  ; isecat = record
           { _∘_ = λ {a} → cmp {a}
           ; idar = idar
           ; ∘ext = λ {m} f f' g g' eqf eqg → ispreorder {m}
           ; lidax = λ {m} f → ispreorder {m}
           ; ridax = λ {m} f → ispreorder {m}
           ; assoc = λ {m} f g h → ispreorder {m}
           }
  }
  where open ωCat-data

ω-is-preorder : is-preorder ω
ω-is-preorder = record { pf =  λ {m} {n} {f} {f'} → ispreorder {m} {n} {f} {f'} }
              where open ωCat-data

ωPreOrd : small-preorder
ωPreOrd = record
        { ℂ = ω
        ; ispreord = ω-is-preorder
        }

module ω where
  open ecategory-aux ω public
  open ωCat-data using (suc) public
  module ispreord = is-preorder ω-is-preorder


-- embeddings of finite linear preorders into ω
-- it maps Fin (s n) onto the initial segment <0,..,n>

Ι : (n : N) → efunctor (FinLinOrd n) ω
Ι n = record
    { FObj = frgt n
    ; FHom = fctr n
    ; isF = record
          { ext = λ {i} _ → ω.ispreord.pf {frgt n i}
          ; id = λ {i} → ω.ispreord.pf {frgt n i}
          ; cmp = λ {i} _ _ → ω.ispreord.pf {frgt n i}
          }
    }
    where frgt : (n : N) → Fin n → N
          frgt (s O) i = O
          frgt (s (s n)) (inl x) = frgt (s n) x
          frgt (s (s n)) (inr x) = s n

          frgt-ar : (n : N)(i : Fin n) → || ωCat-data.Hom (frgt n i) n ||
          frgt-ar (s O) i = i
          frgt-ar (s (s n)) (inl x) = ω._∘_ {a = frgt (s n) x} (ω.suc (s n)) (frgt-ar (s n) x)
          frgt-ar (s (s n)) (inr x) = ω.suc (s n)

          fctr : (n : N){i j : Fin n} → || ecategoryₗₑᵥ.Hom (FinLinOrd n) i j ||
                    → || ωCat-data.Hom (frgt n i) (frgt n j) ||
          fctr (s O) {i} {j} ij = 0₁
          fctr (s (s n)) {inl x} {inl x₁} ij = fctr (s n) ij
          fctr (s (s n)) {inl x} {inr x₁} ij = frgt-ar (s n) x
          fctr (s (s n)) {inr x} {inr x₁} ij = ω.idar (s n)
