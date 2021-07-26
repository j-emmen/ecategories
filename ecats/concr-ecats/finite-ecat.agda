
{-# OPTIONS --without-K #-}

module ecats.concr-ecats.finite-ecat where

open import tt-basics.basics
open import tt-basics.id-type
open import tt-basics.setoids renaming (||_|| to ||_||std)
open import ecats.basic-defs.ecat-def&not
open import ecats.concr-ecats.Std
open import ecats.functors.defs.efunctor



module FinCat-data where
  𝔽Hom : (n : N) → Fin n → Fin n → setoid {0ₗₑᵥ} {0ₗₑᵥ}
  𝔽Hom (s n) (inl x) (inl y) = 𝔽Hom n x y
  𝔽Hom (s n) (inl x) (inr y) = Freestd N₁
  𝔽Hom (s n) (inr x) (inl y) = Freestd N₀
  𝔽Hom (s n) (inr x) (inr y) = Freestd N₁
  {-
  𝔽Hom (s n) = Finsrec n {λ _ → (_ : Fin (s n)) → setoid}
                       -- one arrow from inl to inr
                       (λ i₁ → Finsrec n {λ _ → setoid} (λ i₂ → 𝔽Hom n i₁ i₂) (Freestd N₁))
                       -- no from inr to inl and one arrow from inr to inr
                       (Finsrec n {λ _ → setoid} (λ _ → Freestd N₀) (Freestd N₁))
  -}

  𝔽id :  (n : N)(i : Fin n) → || 𝔽Hom n i i ||
  𝔽id (s n) (inl x) = 𝔽id n x
  𝔽id (s n) (inr x) = 0₁
  -- Finsrec n {λ j → || 𝔽Hom (s n) j j ||} (λ j → 𝔽id n {j}) 0₁ i

  𝔽cmp : (n : N){i j k : Fin n} → || 𝔽Hom n j k || → || 𝔽Hom n i j ||
            → || 𝔽Hom n i k ||
  𝔽cmp (s n) {inl x} {inl y} {inl z} jk ij = 𝔽cmp n jk ij
  𝔽cmp (s n) {inl x} {inl y} {inr z} jk ij = 0₁
  𝔽cmp (s n) {inl x} {inr y} {inr z} jk ij = 0₁
  𝔽cmp (s n) {inr x} {inr y} {inr z} jk ij = 0₁

  {-
  𝔽cmp (s n) {i} {j} {k} jk ij =
    Finsrec n { C = λ (x : Fin (s n)) → {y z : Fin (s n)}
                     → || 𝔽Hom (s n) x y || → || 𝔽Hom (s n) y z || → || 𝔽Hom (s n) x z || }
            ( λ i₁ {j₁} {k₁} → {! Finsrec n {C = λ z → {y : Fin (s n)}
                                         → || 𝔽Hom (s n) (Fin-emb n i₁) y || → || 𝔽Hom (s n) y z ||
                                          → || 𝔽Hom (s n) (Fin-emb n i₁) z ||} !} )
            {!!}
            i
            ij
            jk

  ck : (n : N){i j k : Fin n} → || 𝔽Hom n j k || → || 𝔽Hom n i j || → Set
  ck  n {i} {j} {k} jk ij = {!𝔽Hom (s n) (inl i) (inl j) !}
  -}

  ispreorder : (n : N){i j : Fin n}{ij ij' :  || 𝔽Hom n i j ||} → < 𝔽Hom n i j > ij ~ ij'
  ispreorder (s n) {inl x} {inl x₁} {ij} {ij'} = ispreorder n {ij = ij} {ij'}
  ispreorder (s n) {inl x} {inr x₁} {ij} {ij'} = isContr→isProp N₁-isContr ij ij'
  ispreorder (s n) {inr x} {inr x₁} {ij} {ij'} = isContr→isProp N₁-isContr ij ij'



{-
  𝔽cmp-ext : (n : N){a b c : Fin n} (f f' : || 𝔽Hom n a b ||)(g g' : || 𝔽Hom n b c ||)
                → < 𝔽Hom n a b > f ~ f' → < 𝔽Hom n b c > g ~ g'
                    → < 𝔽Hom n a c > 𝔽cmp n g f ~ 𝔽cmp n g' f'
  𝔽cmp-ext (s n) {inl x} {inl y} {inl z} ij ij' jk jk' eqij eqjk = 𝔽cmp-ext n ij ij' jk jk' eqij eqjk
  𝔽cmp-ext (s n) {inl x} {inl y} {inr z} ij ij' jk jk' eqij eqjk = =rf
  𝔽cmp-ext (s n) {inl x} {inr y} {inr z} ij ij' jk jk' eqij eqjk = =rf
  𝔽cmp-ext (s n) {inr x} {inr x₁} {inr x₂} ij ij' jk jk' eqij eqjk = =rf

  𝔽lidax : (n : N){a b : Fin n}(f : || 𝔽Hom n a b ||) → < 𝔽Hom n a b > 𝔽cmp n (𝔽id n b) f ~ f
  𝔽lidax (s n) {inl x} {inl x₁} ij = 𝔽lidax n ij
  𝔽lidax (s n) {inl x} {inr x₁} ij = pj2 N₁-isContr ij ⁻¹
  𝔽lidax (s n) {inr x} {inr x₁} ij = pj2 N₁-isContr ij ⁻¹

  𝔽ridax : (n : N){a b : Fin n}(f : || 𝔽Hom n a b ||) → < 𝔽Hom n a b > 𝔽cmp n f (𝔽id n a) ~ f
  𝔽ridax (s n) {inl x} {inl x₁} ij = 𝔽ridax n ij
  𝔽ridax (s n) {inl x} {inr x₁} ij = pj2 N₁-isContr ij ⁻¹
  𝔽ridax (s n) {inr x} {inr x₁} ij = pj2 N₁-isContr ij ⁻¹

  𝔽assoc : (n : N){a b c d : Fin n}(f : || 𝔽Hom n a b ||)(g : || 𝔽Hom n b c ||)(h : || 𝔽Hom n c d ||)
              → < 𝔽Hom n a d > 𝔽cmp n h (𝔽cmp n g f) ~ 𝔽cmp n (𝔽cmp n h g) f
  𝔽assoc (s n) {inl x} {inl x₁} {inl x₂} {inl x₃} ij jk kl = 𝔽assoc n ij jk kl
  𝔽assoc (s n) {inl x} {inl x₁} {inl x₂} {inr x₃} ij jk kl = =rf
  𝔽assoc (s n) {inl x} {inl x₁} {inr x₂} {inr x₃} ij jk kl = =rf
  𝔽assoc (s n) {inl x} {inr x₁} {inr x₂} {inr x₃} ij jk kl = =rf
  𝔽assoc (s n) {inr x} {inr x₁} {inr x₂} {inr x₃} ij jk kl = =rf
  -}
-- end FinCat-data

𝔽inCat : (n : N) → small-ecategory
𝔽inCat n = record
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
         where open FinCat-data

module 𝔽inCat (n : N) where
  open ecategory-aux (𝔽inCat n) public
  open FinCat-data using (ispreorder) public


𝟘 𝟙 𝟚 : small-ecategory
𝟘 = 𝔽inCat O
𝟙 = 𝔽inCat (s O)
𝟚 = 𝔽inCat (s (s O))
𝟛 = 𝔽inCat (s (s (s O)))
𝟜 = 𝔽inCat (s (s (s (s O))))

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

module ω where
  open ecategory-aux ω public
  open ωCat-data using (suc; ispreorder) public


-- embedding of finite preorders into ω

Ι : (n : N) → efunctor (𝔽inCat n) ω
Ι n = record
    { FObj = frgt n
    ; FHom = fctr n
    ; isF = record
          { ext = λ {i} _ → ω.ispreorder {frgt n i}
          ; id = λ {i} → ω.ispreorder {frgt n i}
          ; cmp = λ {i} _ _ → ω.ispreorder {frgt n i}
          }
    }
    where frgt : (n : N) → Fin n → N
          frgt (s n) (inl x) = frgt n x
          --frgt (s n) (inr x) = s n -- this one maps e.g. 'inr : Fin 1' to 's O : N'
          frgt (s n) (inr x) = n -- this one maps e.g. 'inr : Fin 1' to 'O : N'
          frgt-ar : (n : N)(i : Fin n) → || ωCat-data.Hom (frgt n i) n ||
          frgt-ar (s n) (inl x) = ω._∘_ {a = frgt n x} (ω.suc n) (frgt-ar n x)
          frgt-ar (s n) (inr x) = ω.suc n
          fctr : (n : N){i j : Fin n} → || ecategoryₗₑᵥ.Hom (𝔽inCat n) i j ||
                    → || ωCat-data.Hom (frgt n i) (frgt n j) ||
          fctr (s n) {inl x} {inl x₁} ij = fctr n ij
          fctr (s n) {inl x} {inr x₁} ij = frgt-ar n x
          fctr (s n) {inr x} {inr x₁} ij = ω.idar n
          
