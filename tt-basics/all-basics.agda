
{-# OPTIONS --without-K #-}

module tt-basics.all-basics where

open import Agda.Primitive
open import tt-basics.basics public
open import tt-basics.id-type public
open import tt-basics.setoids public



-- natural numers equations

+N-ass₁ : (n m : N) → s n +N m == n +N s m
+N-ass₁ n = Nrec =rf (λ m → =ap s {s n +N m} {n +N s m})

+N-ass₁⁻¹ : (n m : N) → n +N s m == s n +N m
+N-ass₁⁻¹ n = Nrec =rf (λ m → =ap s {n +N s m} {s n +N m})

0+n=n : (n : N) → O +N n == n
0+n=n = Nrec =rf (λ n → =ap s {O +N n} {n})

1+n=n : (n : N) → one +N n == s n
1+n=n n = +N-ass₁ O n ■ 0+n=n (s n)


+N-ass : (n m k : N) → n +N m +N k == (n +N m) +N k
+N-ass n m = Nrec {C = λ x → n +N m +N x == (n +N m) +N x}
                  =rf
                  λ x hi → =ap s hi

+N-ass₁⁻¹-emb : (n m : N)(i : Fin (n +N s m))
                → (Fin ● +N-ass₁⁻¹ n (s m)) (Fin-emb (n +N s m) i)
                                       == Fin-emb (s n +N m) ((Fin ● +N-ass₁⁻¹ n m) i)
+N-ass₁⁻¹-emb n m = Fin-emb-=nat-hty (+N-ass₁⁻¹ n m)

--+N-ass₁⁻¹-min : (n m : N) → (Fin ● +N-ass₁⁻¹ n (s m)) (Fin-min (n +N s m)) == Fin-min (s n +N m)
--+N-ass₁⁻¹-min n m = +N-ass₁⁻¹-emb n m (Fin-min (n +N m)) ■ {!!} --Fin-emb-=nat-hty (+N-ass₁⁻¹ n m)

+N-ass-emb : (n m k : N)(i : Fin (n +N m +N k))
                → (Fin ● +N-ass n m (s k)) (Fin-emb (n +N m +N k) i)
                                       == Fin-emb ((n +N m) +N k) ((Fin ● +N-ass n m k) i)
+N-ass-emb n m k = Fin-emb-=nat-hty (+N-ass n m k)

{-
Nrec {C = λ k → (i : Fin (n +N m +N k))
                                      → (Fin ● +N-ass n m (s k)) (Fin-emb (n +N m +N k) i)
                                             == Fin-emb ((n +N m) +N k) ((Fin ● +N-ass n m k) i)}
                      (λ _ → =rf)
                      λ k hi → {!!}
                      {-Finsrec ( n +N m +N k )
                                        { λ i → (Fin ● +N-ass n m (s (s k))) (inl i)
                                                      == inl ((Fin ● +N-ass n m (s k)) i) }
                                         {!!}
                                         {!!}-}
-}

-- +N-ass n m (s k) = =ap s (+N-ass n m k)

-- (Fin ● +N-ass n m (s (s k))) (inl i) = (Fin ● =ap s (+N-ass n m (s k))) (inl i)
-- inl ((Fin ● +N-ass n m (s k)) i) = inl ((Fin ● =ap s (+N-ass n m k)) i)




-- coproduct equations

{- good to know:
Fin-inl-tr₁ : (n m : N)(i : Fin n)
                → Fin-inl (n +N m) one (Fin-inl n m i) == Fin-inl n (s m) i
Fin-inl-tr₁ n m i = =rf

Fin-inr-tr-max₁ : (n m : N)
                → Fin-inr (n +N m) one Fin-singlel == Fin-inr n (s m) (Fin-max m)
Fin-inr-tr-max₁ n m = =rf

Fin-inlr-tr₁ : (n m : N)(i : Fin m)
                → Fin-inl (n +N m) one (Fin-inr n m i) == Fin-inr n (s m) (Fin-emb m i)
Fin-inlr-tr₁ n m i = =rf

Fin-inr-emb : (n m : N)(i : Fin m)
            → Fin-inl (n +N m) one (Fin-inr n m i) == Fin-inr n (s m) (Fin-emb m i)
Fin-inr-emb n m i = =rf
-}

-- coproduct inclusions
{-
Fin-suc-inl : (n m : N)(i : Fin n)
  → Fin-inl (s n) (s m) (Fin-suc n i) == Fin-suc (s n +N m) (Fin-inl (s n) m (Fin-emb n i))
Fin-suc-inl n = Nrec
  {C = λ m → (i : Fin n)
    → Fin-inl (s n) (s m) (Fin-suc n i) == Fin-suc (s n +N m) (Fin-inl (s n) m (Fin-emb n i))}
  (λ _ → =rf)
  (λ m hi i → =ap (Fin-emb (s n +N s m)) (hi i))
--   → Fin-suc (n +N m) (Fin-inl n m i) == (Fin ● +N-ass₁ n m) (Fin-inl (s n) m (Fin-suc n i))

Fin-suc-inr : (n m : N)(i : Fin m)
                 → Fin-inr n (s m) (Fin-suc m i) == Fin-suc (n +N m) (Fin-inr n m i)
Fin-suc-inr n = Nrec 
  {C = λ m → (i : Fin m) → Fin-inr n (s m) (Fin-suc m i) == Fin-suc (n +N m) (Fin-inr n m i)}
  N₀rec
  λ x hi → Finsrec x (λ i → =ap (Fin-emb (n +N s x)) (hi i)) =rf

Fin-ass₁ : (n m : N)
  → Fin-inr (s n) (s m) (Fin-min m) == Fin-suc (s n +N m) (Fin-inl (s n) m (Fin-max n))
Fin-ass₁ n = Nrec =rf (λ m hi → =ap (Fin-emb (s n +N s m)) hi)

-- triangles

Fin-+unv-trl : {ℓ : Level}{A : Set ℓ}(n m : N)(f : Fin n → A)(g : Fin m → A)(i : Fin n)
                     → Fin-+unvar n m f g (Fin-inl n m i) == f i
Fin-+unv-trl {A = A} = Nrec { C = λ n → (m : N)(f : Fin n → A)(g : Fin m → A)(i : Fin n)
                                           → Fin-+unvar n m f g (Fin-inl n m i) == f i }
                            ( λ m f g → N₀rec )
                            ( λ n hi m f →
  Nrec {C = λ x → (g : Fin x → A) (i : Fin (s n))
                     → Fin-+unvar (s n) x f g (Fin-inl (s n) x i) == f i}
       ( λ g i → =rf )
       ( λ x his g → Finsrec n
                              {C = λ i → Fin-+unvar (s n) (s x) f g (Fin-inl (s n) (s x) i) == f i}
                              (λ i → his (λ j → g (Fin-emb x j)) (Fin-emb n i))
                              (his ((λ j → g (Fin-emb x j))) (Fin-max n)) )
       m )
-- Fin-inl n (s x) f g = Fin-emb (n +N x) ∘ Fin-inl n x

-- Fin-+unvar n (s x) f g ∘ Fin-emb (n +N x) =
-- = ( λ hi g → hi (λ i → g (Fin-emb m i)) ) (Fin-+unvar n x f) g ∘  Fin-emb (n +N x)
-- = Fin-+unvar n x f (λ i → g (Fin-emb m i)) ∘  Fin-emb (n +N x)

Fin-+unv-trr : {ℓ : Level}{A : Set ℓ}(n m : N)(f : Fin n → A)(g : Fin m → A)(i : Fin m)
                     → Fin-+unvar n m f g (Fin-inr n m i) == g i
Fin-+unv-trr {A = A} n m f =
  Nrec {C = λ x → (g : Fin x → A) (i : Fin x) → Fin-+unvar n x f g (Fin-inr n x i) == g i}
       (λ _ → N₀rec)
       (λ x hi g → Finsrec x
                            {C = λ i → Fin-+unvar n (s x) f g (Fin-inr n (s x) i) == g i}
                            (hi (λ i → g (Fin-emb x i)))
                            =rf)
       m

Fin-+unv-ass : (n m k : N){ℓ : Level}{A : Set ℓ}(f : Fin n → A)(g : Fin m → A)(h : Fin k → A)(i : Fin (n +N m +N k))
                  → Fin-+unvar n (m +N k) f (Fin-+unvar m k g h) i ==
                       Fin-+unvar (n +N m) k (Fin-+unvar n m f g) h ((Fin ● (+N-ass n m k)) i)
Fin-+unv-ass n m k {A = A} f g =
  Nrec { C = λ x → (h : Fin x → A)(i : Fin (n +N m +N x))
                  → Fin-+unvar n (m +N x) f (Fin-+unvar m x g h) i ==
                       Fin-+unvar (n +N m) x (Fin-+unvar n m f g) h ((Fin ● (+N-ass n m x)) i) }
       ( λ _ _ → =rf )
       ( λ x hi h → Finsrec ( n +N m +N x )
                             { λ i → Fin-+unvar n (m +N s x) f (Fin-+unvar m (s x) g h) i ==
                   Fin-+unvar (n +N m) (s x) (Fin-+unvar n m f g) h ((Fin ● +N-ass n m (s x)) i) }
                             ( λ i → hi (λ j → h (Fin-emb x j)) i
                                          ■ =ap (Fin-+unvar (n +N m) (s x) (Fin-+unvar n m f g) h)
                                                (+N-ass-emb n m x i ⁻¹) )
                             ( =ap (Fin-+unvar (n +N m) (s x) (Fin-+unvar n m f g) h)
                                   (Fin-max-=nat (+N-ass n m x) ⁻¹) ))
       k
-- The equation in the recursive part of the last Fin-+unvar:
-- Fin-+unvar n (m +N s x) f (Fin-+unvar m (s x) g h) (Fin-emb (n +N m +N x) i) =
-- = Fin-+unvar n (m +N x) f (λ j →  Fin-+unvar m (s x) g h (Fin-emb (m +N x) j)) i
-- = Fin-+unvar n (m +N x) f (Fin-+unvar m x g (λ j → h (Fin-emb x j))) i
-- [by hi]
-- = Fin-+unvar (n +N m) x (Fin-+unvar n m f g) (λ j → h (Fin-emb x j)) ((Fin ● +N-ass n m x) i)
-- = Fin-+unvar (n +N m) (s x) (Fin-+unvar n m f g) h (Fin-emb ((n +N m) +N x) ((Fin ● +N-ass n m x) i))
-- [by +N-ass-emb ⁻¹]
-- == Fin-+unvar (n +N m) (s x) (Fin-+unvar n m f g) h ((Fin ● +N-ass n m (s x)) (Fin-emb (n +N m +N x) i))
-}

Fin-inl-min : (n m : N) → Fin-inl (s n) (s m) (Fin-min n) == Fin-min (s n +N m)
Fin-inl-min n = Nrec =rf (λ m hi → =ap inl hi)

Fin-inr-max : (n m : N) → Fin-inr n (s m) (Fin-max m) == Fin-max (n +N m)
Fin-inr-max n = Nrec =rf (λ _ _ → =rf)
