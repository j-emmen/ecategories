
{-# OPTIONS --without-K #-}

module ecats.concr-ecats.finite-ecat where

open import tt-basics.all-basics renaming (||_|| to ||_||std)
open import ecats.basic-defs.ecat-def&not
open import ecats.basic-defs.commut-shapes
open import ecats.concr-ecats.Std-lev
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
          frgt (s n) (inr x) = n -- this one maps e.g. 'inr : Fin 1' to 'O : N'
          
          frgt-ar : (n : N)(i : Fin n) → || ωCat-data.Hom (frgt n i) n ||
          frgt-ar (s n) (inl x) = ω._∘_ {a = frgt n x} (ω.suc n) (frgt-ar n x)
          frgt-ar (s n) (inr x) = ω.suc n
          fctr : (n : N){i j : Fin n} → || ecategoryₗₑᵥ.Hom (𝔽inCat n) i j ||
                    → || ωCat-data.Hom (frgt n i) (frgt n j) ||
          fctr (s n) {inl x} {inl x₁} ij = fctr n ij
          fctr (s n) {inl x} {inr x₁} ij = frgt-ar n x
          fctr (s n) {inr x} {inr x₁} ij = ω.idar n


-- the cospan category
module cospan-category where
-- inr (inl 0₁) → inl 0₁ ← inr (inr 0₁)
  Ob : Set
  Ob = N₁ + (N₁ + N₁)
  H : Ob → Ob → Set
  H (inl x) (inl y) = N₁
  H (inr (inl x)) (inr (inl y)) = N₁
  H (inr (inr x)) (inr (inr y)) = N₁
  H (inr x) (inl y) = N₁
  H (inl x) (inr y) = N₀
  H (inr (inl x)) (inr (inr y)) = N₀
  H (inr (inr x)) (inr (inl y)) = N₀  
  Hm : Ob → Ob → setoid {0ₗₑᵥ} {0ₗₑᵥ}
  Hm x y = Freestd (H x y)
  
  cmp :  {a b c : Ob} → || Hm b c || → || Hm a b || → || Hm a c ||
  cmp {inl 0₁} {inl 0₁} {c} g f = g
  cmp {inr x} {inl 0₁} {inl 0₁} g f = f
  cmp {inr (inl 0₁)} {inr (inl 0₁)} {c} g f = g
  cmp {inr (inr 0₁)} {inr (inr 0₁)} {c} g f = g  

  id : (a : Ob) → || Hm a a ||
  id (inl x) = 0₁
  id (inr (inl x)) = 0₁
  id (inr (inr x)) = 0₁

  ext : {a b c : Ob} (f f' : || Hm a b ||) (g g' : || Hm b c ||)
           → < Hm a b > f ~ f' → < Hm b c > g ~ g'
             → < Hm a c > cmp {a} {b} {c} g f ~ cmp {a} {b} {c} g' f'
  ext {inl 0₁} {inl 0₁} {c} f f' g g' eqf eqg = eqg
  ext {inr x} {inl 0₁} {inl 0₁} f f' g g' eqf eqg = eqf
  ext {inr (inl 0₁)} {inr (inl 0₁)} {c} f f' g g' eqf eqg = eqg
  ext {inr (inr 0₁)} {inr (inr 0₁)} {c} f f' g g' eqf eqg = eqg

  lid : {a b : Ob} (f : || Hm a b ||) → < Hm a b > cmp {a} {b} {b} (id b) f ~ f
  lid {inl 0₁} {inl 0₁} 0₁ = =rf
  lid {inr x} {inl 0₁} f = =rf
  lid {inr (inl 0₁)} {inr (inl 0₁)} 0₁ = =rf
  lid {inr (inr 0₁)} {inr (inr 0₁)} 0₁ = =rf

  rid : {a b : Ob} (f : || Hm a b ||) → < Hm a b > cmp {a} {a} {b} f (id a) ~ f
  rid {inl 0₁} {b} f = =rf
  rid {inr (inl 0₁)} {b} f = =rf
  rid {inr (inr 0₁)} {b} f = =rf

  ass : {a b c d : Ob} (f : || Hm a b ||) (g : || Hm b c ||)(h : || Hm c d ||)
           → < Hm a d > cmp h (cmp g f) ~ cmp (cmp h g) f
  ass {inl 0₁} {inl 0₁} {c} {d} f g h = =rf
  ass {inr (inl 0₁)} {inr (inl 0₁)} {c} {d} f g h = =rf
  ass {inr (inr 0₁)} {inr (inr 0₁)} {c} {d} f g h = =rf
  ass {inr (inl x)} {inl 0₁} {inl 0₁} {d} f g h = =rf
  ass {inr (inr x)} {inl 0₁} {inl 0₁} {d} f g h = =rf

-- end cospan-category

Cospan : small-ecategory
Cospan = record
     { Obj = Ob
     ; Hom = Hm
     ; isecat = record
                  { _∘_ = λ {a} {b} {c} → cmp {a} {b} {c}
                  ; idar = id
                  ; ∘ext = ext
                  ; lidax = lid
                  ; ridax = rid
                  ; assoc = ass
                  }
     }
     where open cospan-category

module Cospan-aux where
  open ecategory-aux Cospan public
  crn v₁ v₂ : Obj
  crn = inl 0₁
  v₁ = inr (inl 0₁)
  v₂ = inr (inr 0₁)
  a₁ : || Hom v₁ crn ||
  a₁ = 0₁
  a₂ : || Hom v₂ crn ||
  a₂ = 0₁

module cospan-in-ecat {ℓ₁ ℓ₂ ℓ₃ : Level}(ℂ : ecategoryₗₑᵥ ℓ₁ ℓ₂ ℓ₃) where
  private
    module ℂ where
      open ecategory-aux ℂ public
      open comm-shapes ℂ public
    module Csp = Cospan-aux
    
  diag2cosp : Cospan diag-in ℂ → ℂ.cospan
  diag2cosp cosp = record
    { O12 = cosp.ₒ Csp.crn
    ; cosp/ = record
            { O1 = cosp.ₒ Csp.v₁
            ; O2 = cosp.ₒ Csp.v₂
            ; a1 = cosp.ₐ Csp.a₁
            ; a2 = cosp.ₐ Csp.a₂
            }
    }
    where module cosp = diagram cosp

  cosp2diag : ℂ.cospan → Cospan diag-in ℂ
  cosp2diag cosp = record
    { FObj = FO
    ; FHom = FH
    ; isF = record
          { ext = ext
          ; id = λ {A} → id A
          ; cmp = cmp
          }
    }
    where module cosp = ℂ.cospan cosp
          FO : Csp.Obj → ℂ.Obj
          FO (inl x) = cosp.O12
          FO (inr (inl x)) = cosp.O1
          FO (inr (inr x)) = cosp.O2
          FH : {A B : Csp.Obj} → || Csp.Hom A B || → || ℂ.Hom (FO A) (FO B) ||
          FH {inl x} {inl y} f = ℂ.idar cosp.O12
          FH {inr (inl x)} {inl y} f = cosp.a1
          FH {inr (inl x)} {inr (inl y)} f = ℂ.idar cosp.O1
          FH {inr (inr x)} {inl y} f = cosp.a2
          FH {inr (inr x)} {inr (inr y)} f = ℂ.idar cosp.O2

          ext : {A B : Csp.Obj} {f f' : || Csp.Hom A B ||}
                   → f Csp.~ f' → FH f ℂ.~ FH f'
          ext {inl x} {inl x₁} {f} {f'} eq = ℂ.r
          ext {inr (inl x)} {inl y} {f} {f'} eq = ℂ.r
          ext {inr (inl x)} {inr (inl y)} {f} {f'} eq = ℂ.r
          ext {inr (inr x)} {inl y} {f} {f'} eq = ℂ.r
          ext {inr (inr x)} {inr (inr y)} {f} {f'} eq = ℂ.r

          id : (A : Csp.Obj) → FH (Csp.idar A) ℂ.~ ℂ.idar (FO A)
          id (inl x) = ℂ.r
          id (inr (inl x)) = ℂ.r
          id (inr (inr x)) = ℂ.r

          cmp : {A B C : Csp.Obj}(f : || Csp.Hom A B ||)(g : || Csp.Hom B C ||)
                   → FH g ℂ.∘ FH f ℂ.~ FH (g Csp.∘ f)
          cmp {inl x} {inl y} {inl z} f g = ℂ.lid
          cmp {inr (inl x)} {inl x₁} {inl x₂} f g = ℂ.lid
          cmp {inr (inl x)} {inr (inl x₁)} {inl x₂} f g = ℂ.rid
          cmp {inr (inl x)} {inr (inl x₁)} {inr (inl x₂)} f g = ℂ.rid
          cmp {inr (inr x)} {inl x₁} {inl x₂} f g = ℂ.lid
          cmp {inr (inr x)} {inr (inr x₁)} {inl x₂} f g = ℂ.rid
          cmp {inr (inr x)} {inr (inr x₁)} {inr (inr x₂)} f g = ℂ.rid

-- end cospan-in-ecat
