
{-# OPTIONS --without-K #-}

module ecats.basic-defs.isomorphism where

open import ecats.basic-defs.ecat-def&not
open import ecats.basic-defs.commut-shapes

-- Definitions

module iso-defs (ℂ : ecategory) where
  open ecategory ℂ

  -- isomorphic objects

  record is-iso-pair {a b : Obj} (f : || Hom a b ||) (invf : || Hom b a ||) : Set where
    field
      iddom : invf ∘ f ~ idar a
      idcod : f ∘ invf ~ idar b

  inv-uq : {a b : Obj}{f : || Hom a b ||}{g g' : || Hom b a ||}
              → is-iso-pair f g → is-iso-pair f g' → g ~ g'
  inv-uq {f = f} {g} {g'} isop isop' = ~proof g           ~[ ridggˢ r g'.idcod ] /
                                              g ∘ f ∘ g'   ~[ ass ⊙ lidgg r g.iddom ]∎
                                              g' ∎
                                     where open ecategory-aux-only ℂ
                                           module g = is-iso-pair isop
                                           module g' = is-iso-pair isop'

  inv-uqg : {a b : Obj}{f f' : || Hom a b ||}{g g' : || Hom b a ||}
               → is-iso-pair f g → is-iso-pair f' g' → f ~ f' → g ~ g'
  inv-uqg {f = f} {f'} {g} {g'} isop isop' eq = ~proof
                                              g            ~[ ridggˢ r g'.idcod ] /
                                              g ∘ f' ∘ g'   ~[ ∘e (∘e r (eq ˢ)) r  ] /
                                              g ∘ f ∘ g'    ~[ ass ⊙ lidgg r g.iddom ]∎
                                              g' ∎
                                              where open ecategory-aux-only ℂ
                                                    module g = is-iso-pair isop
                                                    module g' = is-iso-pair isop'


  inv-iso-pair : {a b : Obj} {f : || Hom a b ||} {invf : || Hom b a ||}
                    → is-iso-pair f invf → is-iso-pair invf f
  inv-iso-pair isop = record
    { iddom = idcod
    ; idcod = iddom
    }
    where open is-iso-pair isop

  iso-pair-ext : {a b : Obj}{f g : || Hom a b ||}{f' g' : || Hom b a ||}
                    → is-iso-pair f f' → g ~ f → g' ~ f' → is-iso-pair g g'
  iso-pair-ext isop eq eq' = record
    { iddom = ∘e eq eq' ⊙ f.iddom
    ; idcod = ∘e eq' eq ⊙ f.idcod
    }
    where module f = is-iso-pair isop
          open ecategory-aux-only ℂ

  iso-pair-cmp : {a b c : Obj}{f : || Hom a b ||}{f' : || Hom b a ||}
                 {g : || Hom b c ||}{g' : || Hom c b ||}
                    → is-iso-pair f f' → is-iso-pair g g'
                      → is-iso-pair (g ∘ f) (f' ∘ g')
  iso-pair-cmp isopf isopg = record
    { iddom = assˢ ⊙ ∘e (ass ⊙ lidgg r g.iddom) r ⊙ f.iddom
    ; idcod = assˢ ⊙ ∘e (ass ⊙ lidgg r f.idcod) r ⊙ g.idcod
    }
    where module f = is-iso-pair isopf
          module g = is-iso-pair isopg
          open ecategory-aux-only ℂ

  iso-pair-tricmp : {a b c d : Obj}{f : || Hom a b ||}{f' : || Hom b a ||}
                    {g : || Hom b c ||}{g' : || Hom c b ||}
                    {h : || Hom c d ||}{h' : || Hom d c ||}
                    → is-iso-pair f f' → is-iso-pair g g' → is-iso-pair h h'
                      → is-iso-pair (h ∘ g ∘ f) (f' ∘ g' ∘ h')
  iso-pair-tricmp isopf isopg isoph = iso-pair-ext (iso-pair-cmp (iso-pair-cmp isopf isopg) isoph) r ass
    where module f = is-iso-pair isopf
          module g = is-iso-pair isopg
          module h = is-iso-pair isoph
          open ecategory-aux-only ℂ
    

  record is-iso {a b : Obj} (f : || Hom a b ||) : Set where
    constructor mkis-iso
    field
      {invf} : || Hom b a ||
      isisopair : is-iso-pair f invf
    open is-iso-pair isisopair public
    ⁻¹ : || Hom b a ||
    ⁻¹ = invf


  invf-is-iso : {a b : Obj} → {f : || Hom a b ||} → (f⁻¹ : is-iso f) → is-iso (is-iso.invf f⁻¹)
  invf-is-iso {f = f} f⁻¹ = mkis-iso (inv-iso-pair isisopair)
                          where open is-iso f⁻¹

  iso-ext : {a b : Obj} {f f' : || Hom a b ||} → is-iso f → f' ~ f → is-iso f'
  iso-ext {f' = f'} isof pf = mkis-iso isop
                            where open ecategory-aux-only ℂ
                                  open is-iso isof
                                  isop : is-iso-pair f' invf
                                  isop = record
                                       { iddom = ∘e pf r ⊙ iddom
                                       ; idcod = ∘e r pf ⊙ idcod
                                       }
  
{-
  inverses : {a b : Obj} → (f : || Hom a b ||) → (f⁻¹ : || Hom b a ||) → Set
  inverses {a} {b} f f⁻¹ = prod (< Hom a a > f⁻¹ ∘ f ~ idar a)
                                (< Hom b b > f ∘ f⁻¹ ~ idar b)
-}
{-
  _≅ₒ_ : (a b : Obj) → Set
  a ≅ₒ b = Σ (prod || Hom a b || || Hom b a ||) (λ ff → inverses (prj1 ff) (prj2 ff) )
-}

  infix 0 _≅ₒ_ 
  record _≅ₒ_ (a b : Obj) : Set where
    constructor mk≅
    field
      {a12} : || Hom a b ||
      {a21} : || Hom b a ||
      isop : is-iso-pair a12 a21
    open is-iso-pair isop public

  iso-trdom : {a b c : Obj} {f : || Hom a b ||} {f' : || Hom b a ||}(isop : is-iso-pair f f')
              {g : || Hom b c ||} {h : || Hom a  c ||}
                → g ∘ f ~ h → h ∘ f' ~ g
  iso-trdom isop pf = ∘e r (pf ˢ) ⊙ ass ˢ ⊙ ridgg r idcod
                    where open is-iso-pair isop
                          open ecategory-aux-only ℂ

  iso-trcod : {a b c : Obj} {f : || Hom a b ||} {f' : || Hom b a ||}(isop : is-iso-pair f f')
              {g : || Hom c a ||} {h : || Hom c b ||}
                → f ∘ g ~ h → f' ∘ h ~ g
  iso-trcod isop pf = ∘e (pf ˢ) r ⊙ ass ⊙ lidgg r iddom
                    where open is-iso-pair isop
                          open ecategory-aux-only ℂ

-- end module iso-defs


-- If a natural transformation has object-wise inverses, then it's a natural iso. Done elementarily

  invIsNatΣ : {a a' b b' : Obj} → {f : || Hom a b || } → {f' : || Hom a' b' ||}
                → {m : || Hom a a' ||} → {m⁻¹ : || Hom a' a ||} → {n : || Hom b b' ||} → {n⁻¹ : || Hom b' b ||}
                  → is-iso-pair m m⁻¹ → is-iso-pair n n⁻¹
                    → n ∘ f ~ f' ∘ m → n⁻¹ ∘ f' ~ f ∘ m⁻¹
  invIsNatΣ {f = f} {f'} {m} {m⁻¹} {n} {n⁻¹} isom ison pf = ~proof  
       n⁻¹ ∘ f'                  ~[ ridggˢ r M.idcod ⊙ assˢ ⊙ ∘e ass r  ] /
       n⁻¹ ∘ (f' ∘ m) ∘ m⁻¹       ~[ ∘e (∘e r (pf ˢ)) r ] /
       n⁻¹ ∘ (n ∘ f) ∘ m⁻¹        ~[ ass ⊙ ∘e r (ass ⊙ ∘e r N.iddom ⊙ lid) ]∎       
       f ∘ m⁻¹                    ∎
                                  where open ecategory-aux-only ℂ
                                        module M = is-iso-pair isom
                                        module N = is-iso-pair ison


  invIsNat : {a a' b b' : Obj} → {f : || Hom a b || } → {f' : || Hom a' b' ||}
                → {m : || Hom a a' ||} → {m⁻¹ : || Hom a' a ||} → {n : || Hom b b' ||} → {n⁻¹ : || Hom b' b ||}
                  → is-iso-pair m m⁻¹ → is-iso-pair n n⁻¹
                    → n ∘ f ~ f' ∘ m → n⁻¹ ∘ f' ~ f ∘ m⁻¹
  invIsNat {f = f} {f'} {m} {m⁻¹} {n} {n⁻¹} isom ison pf = ~proof  
       n⁻¹ ∘ f'                  ~[ ridˢ ⊙ ∘e (mm⁻¹=id ˢ) r ⊙ assˢ ⊙ ∘e ass r  ] /
       n⁻¹ ∘ (f' ∘ m) ∘ m⁻¹       ~[ ∘e (∘e r (pf ˢ)) r ] /
       n⁻¹ ∘ (n ∘ f) ∘ m⁻¹        ~[ ass ⊙ ∘e r (ass ⊙ ∘e r n⁻¹n=id ⊙ lid) ]∎       
       f ∘ m⁻¹                    ∎
       where open ecategory-aux-only ℂ
             open is-iso-pair isom renaming (iddom to m⁻¹m=id; idcod to mm⁻¹=id)
             open is-iso-pair ison renaming (iddom to n⁻¹n=id; idcod to nn⁻¹=id)
       

module iso-transports (ℂ : ecategory) where
  open ecategory-aux ℂ
  open iso-defs ℂ
  open comm-shapes ℂ

-- transport along isomorphisms


  record iso-transportable (Propos : {X Y : Obj} → || Hom X Y || → Set₁) : Set₁ where
    constructor mkiso-transp
    field
      congr : is-ecat-congr ℂ Propos
      on-iso : {X Y : Obj} → (f :  || Hom X Y ||) → is-iso f → Propos f
    open is-ecat-congr congr public             


  module iso-transp (Propos : {X Y : Obj} → || Hom X Y || → Set₁) (trn : iso-transportable Propos) where
    --open is-ext-prop
    open is-iso
    open iso-transportable

    invtr-dom : (tr : comm-triang) → is-iso (comm-triang.a12 tr) → comm-triang
    invtr-dom tr a12⁻¹ = mktriang (~proof a13 ∘ invf a12⁻¹          ~[ ∘e r (pftr ˢ) ⊙  assˢ ] /
                                          a23 ∘ a12 ∘ invf a12⁻¹    ~[ ridgg r (idcod a12⁻¹) ]∎
                                          a23 ∎)
                       where open comm-triang tr
    {-record
                           { O1 = O2 ; O2 = O1 ; O3 = O3
                           ; a13 = a23
                           ; a12 = invf a12⁻¹
                           ; a23 = a13
                           ; pftr = ∘e r (pftr ˢ) ⊙  assˢ ⊙ ridgg r (idcod a12⁻¹)
                           }
-}

    invtr-cod : (tr : comm-triang) → is-iso (comm-triang.a23 tr) → comm-triang
    invtr-cod tr a23⁻¹ = mktriang (~proof invf a23⁻¹ ∘ a13          ~[ ∘e (pftr ˢ) r ] /
                                          invf a23⁻¹ ∘ a23 ∘ a12    ~[ ass ⊙ lidgg r (iddom a23⁻¹) ]∎
                                          a12 ∎)
                       where open comm-triang tr

    module iso-transp-tr-domrl (tr : comm-triang) where
      open comm-triang tr
      trnsp-tr-domrl : is-iso a12 → Propos a23 → Propos a13
      trnsp-tr-domrl a12⁻¹ pf = trnsp trn pftr (∘c trn pf (on-iso trn a12 a12⁻¹)) --


    module iso-transp-tr-domlr (tr : comm-triang) where
      open comm-triang tr
      trnsp-tr-domlr : is-iso a12 → Propos a13 → Propos a23
      trnsp-tr-domlr a12⁻¹ pf = trnsp-tr-domrl (invf-is-iso a12⁻¹) pf
                                               where open iso-transp-tr-domrl (invtr-dom tr a12⁻¹)


    module iso-transp-tr-codrl (tr : comm-triang) where
      open comm-triang tr
      trnsp-tr-codrl : is-iso a23 → Propos a13 → Propos a12
      trnsp-tr-codrl a13⁻¹ pf = trnsp trn {x = invf a13⁻¹ ∘ a13}
                                      (∘e (pftr ˢ) r ⊙ ass ⊙ lidgg r (iddom a13⁻¹))
                                      (∘c trn (on-iso trn (invf a13⁻¹) (invf-is-iso a13⁻¹)) pf)


    module iso-transp-tr-codlr (tr : comm-triang) where
      open comm-triang tr
      trnsp-tr-codlr : is-iso a23 → Propos a12 → Propos a13
      trnsp-tr-codlr a23⁻¹ pf = trnsp-tr-codrl (invf-is-iso a23⁻¹) pf
                                               where open iso-transp-tr-codrl (invtr-cod tr a23⁻¹)
  

    module iso-transp-sq-rl (sq : comm-square) where
      open comm-square sq
      trnsp-sq-rl : is-iso down → is-iso up → Propos right → Propos left
      trnsp-sq-rl d⁻¹ u⁻¹ pf = trnsp-tr-codrl d⁻¹ (trnsp-tr-domrl u⁻¹ pf)
                                              where uptr : comm-triang
                                                    uptr = record
                                                             { O1 = ul ; O2 = ur ; O3 = dr
                                                             ; a13 = right ∘ up
                                                             ; a12 = up
                                                             ; a23 = right
                                                             ; pftr = r
                                                             }
                                                    downtr : comm-triang
                                                    downtr = record
                                                             { O1 = ul ; O2 = dl ; O3 = dr
                                                             ; a13 = right ∘ up
                                                             ; a12 = left
                                                             ; a23 = down
                                                             ; pftr = sq-pf
                                                             }
                                                    open iso-transp-tr-domrl uptr
                                                    open iso-transp-tr-codrl downtr
                                                    
  -- end module iso-transp
