
{-# OPTIONS --without-K #-}

module ecats.basic-props.isomorphism where

open import ecats.basic-defs.ecat-def&not
open import ecats.basic-defs.commut-shapes
open import ecats.basic-defs.isomorphism

module iso-props {ℓ₁ ℓ₂ ℓ₃ : Level}(ℂ : ecategoryₗₑᵥ ℓ₁ ℓ₂ ℓ₃) where
  open ecat ℂ
  open iso-defs ℂ

  inv-iso-pair : {a b : Obj} {f : || Hom a b ||} {invf : || Hom b a ||}
                    → is-iso-pair f invf → is-iso-pair invf f
  inv-iso-pair isop = record
    { iddom = idcod
    ; idcod = iddom
    }
    where open is-iso-pair isop

  invf-is-iso : {a b : Obj} → {f : || Hom a b ||} → (f⁻¹ : is-iso f) → is-iso (is-iso.invf f⁻¹)
  invf-is-iso {f = f} f⁻¹ = mkis-iso (inv-iso-pair isisopair)
                          where open is-iso f⁻¹

  linvr-uq :  {a b : Obj} {f : || Hom a b ||} {linvf rinvf : || Hom b a ||}
                 → linvf ∘ f ~ idar a → f ∘ rinvf ~ idar b
                   → linvf ~ rinvf
  linvr-uq {f = f} {linvf} {rinvf} iddom idcod = ~proof
    linvf               ~[ ridggˢ r idcod ] /
    linvf ∘ f ∘ rinvf   ~[ ass ⊙ lidgg r iddom ]∎
    rinvf ∎
    where open ecategory-aux-only ℂ

  inv-uq-r :  {a b : Obj} {f : || Hom a b ||} {invf invf' : || Hom b a ||}
               → is-iso-pair f invf → is-iso-pair f invf' → invf ~ invf'
  inv-uq-r isop isop' = linvr-uq isop.iddom isop'.idcod
                      where module isop = is-iso-pair isop
                            module isop' = is-iso-pair isop'

  inv-uq :  {a b : Obj} {f f' : || Hom a b ||} {invf invf' : || Hom b a ||}
               → is-iso-pair f invf → is-iso-pair f' invf'
                 → f ~ f' → invf ~ invf'
  inv-uq {f = f} {f'} {invf} {invf'} isop isop' pf = ~proof
    invf               ~[ ridggˢ r isop'.idcod ] /
    invf ∘ f' ∘ invf'  ~[ ∘e (∘e r (pf ˢ)) r ] /
    invf ∘ f ∘ invf'   ~[ ass ⊙ lidgg r isop.iddom ]∎
    invf' ∎
    where open ecategory-aux-only ℂ
          module isop = is-iso-pair isop
          module isop' = is-iso-pair isop'
    
  idar-is-isopair : (a : Obj) → is-iso-pair (idar a) (idar a)
  idar-is-isopair a = record
    { iddom = lidax (idar a)
    ; idcod = lidax (idar a)
    }

  idar-is-iso : (a : Obj) → is-iso (idar a)
  idar-is-iso a = mkis-iso (idar-is-isopair a)

  isopair-cmp : {a b c : Obj}{f : || Hom a b ||}{invf : || Hom b a ||}
                {g : || Hom b c ||}{invg : || Hom c b ||}
                  → is-iso-pair f invf → is-iso-pair g invg
                    → is-iso-pair (g ∘ f) (invf ∘ invg)
  isopair-cmp {f = f} {invf} {g} {invg} isopf isopg = record
    { iddom = assˢ ⊙ ∘e (ass ⊙ lidgg r g.iddom) r ⊙ f.iddom
    ; idcod = assˢ ⊙ ∘e (ass ⊙ lidgg r f.idcod) r ⊙ g.idcod
    }
    where open ecategory-aux-only ℂ
          module f = is-iso-pair isopf
          module g = is-iso-pair isopg

  iso-cmp : {a b c : Obj}{f : || Hom a b ||}{g : || Hom b c ||}
                  → is-iso f → is-iso g → is-iso (g ∘ f)
  iso-cmp isof isog = mkis-iso (isopair-cmp f.isisopair g.isisopair)
                    where module f = is-iso isof
                          module g = is-iso isog

  iso-ext : {a b : Obj} {f f' : || Hom a b ||} → is-iso f → f' ~ f → is-iso f'
  iso-ext {f' = f'} isof pf = mkis-iso isop
                            where open ecategory-aux-only ℂ
                                  open is-iso isof
                                  isop : is-iso-pair f' invf
                                  isop = record
                                       { iddom = ∘e pf r ⊙ iddom
                                       ; idcod = ∘e r pf ⊙ idcod
                                       }


  -- iso pairs fit in same triangles
  
  iso-trdom : {a b c : Obj} {f : || Hom a b ||} {f' : || Hom b a ||}(isop : is-iso-pair f f')
              {g : || Hom b c ||} {h : || Hom a  c ||}
                → g ∘ f ~ h → h ∘ f' ~ g
  iso-trdom  {f = f} {f'} isop {g} {h} pf = ~proof
    h ∘ f'        ~[ ∘e r (pf ˢ) ⊙ ass ˢ ] /
    g ∘ f ∘ f'    ~[ ridgg r idcod ]∎
    g ∎
    where open is-iso-pair isop
          open ecategory-aux-only ℂ

  iso-trcod : {a b c : Obj} {f : || Hom a b ||} {f' : || Hom b a ||}(isop : is-iso-pair f f')
              {g : || Hom c a ||} {h : || Hom c b ||}
                → f ∘ g ~ h → f' ∘ h ~ g
  iso-trcod {f = f} {f'} isop {g} {h} pf  = ~proof
    f' ∘ h          ~[ ∘e (pf ˢ) r ⊙ ass ] /
    (f' ∘ f) ∘ g    ~[ lidgg r iddom ]∎
    g ∎
    where open is-iso-pair isop
          open ecategory-aux-only ℂ

  -- and squares
  
  iso-sq : {a a' b b' : Obj}{f : || Hom a b || }{f' : || Hom a' b' ||}
             {m : || Hom a a' ||}{m⁻¹ : || Hom a' a ||}{n : || Hom b b' ||}{n⁻¹ : || Hom b' b ||}
                → is-iso-pair m m⁻¹ → is-iso-pair n n⁻¹ → n ∘ f ~ f' ∘ m
                  → n⁻¹ ∘ f' ~ f ∘ m⁻¹
  iso-sq {f = f} {f'} {m} {m⁻¹} {n} {n⁻¹} isom ison pf =
    iso-trcod ison {_} {f'} (ass ⊙ iso-trdom isom {f'} {n ∘ f} (pf ˢ))
      where open ecategory-aux-only ℂ

  ≅ₒrefl : (a : Obj) → a ≅ₒ a
  ≅ₒrefl a = record
           { a12 = idar a
           ; a21 = idar a
           ; isop = idar-is-isopair a
           }

  ≅ₒsym : {a b : Obj} → a ≅ₒ b → b ≅ₒ a
  ≅ₒsym iso = record
            { a12 = a21
            ; a21 = a12
            ; isop = inv-iso-pair isop
            }
            where open _≅ₒ_ iso

  ≅ₒtra : {a b c : Obj} → a ≅ₒ b → b ≅ₒ c → a ≅ₒ c
  ≅ₒtra iso1 iso2 = record
                  { a12 = i2.a12 ∘ i1.a12
                  ; a21 = i1.a21 ∘ i2.a21
                  ; isop = isopair-cmp i1.isop i2.isop
                  }
                  where module i1 = _≅ₒ_ iso1
                        module i2 = _≅ₒ_ iso2
  
-- end iso-props


module iso-transports (ℂ : ecategory) where
  open ecategory-aux ℂ
  open comm-shapes ℂ
  open iso-defs ℂ
  open iso-props ℂ
  open hom-ext-prop-defs ℂ

-- transport along isomorphisms

  record iso-transportable (Prp : {X Y : Obj} → || Hom X Y || → Set₁) : Set₁ where
    constructor mkiso-transp
    field
      congr : is-ecat-congr Prp
      on-iso : {X Y : Obj} → (f :  || Hom X Y ||) → is-iso f → Prp f
    open is-ecat-congr congr public

  module iso-transp (Prp : {X Y : Obj} → || Hom X Y || → Set₁)
                    (trn : iso-transportable Prp)
                    where
    --open is-iso
    open iso-transportable trn

    invtr-dom : (tr : comm-triang) → is-iso (comm-triang.a12 tr) → comm-triang
    invtr-dom tr a12⁻¹ = mktriang (~proof a13 ∘ a12.⁻¹          ~[ ∘e r (pftr ˢ) ⊙  assˢ ] /
                                          a23 ∘ a12 ∘ a12.⁻¹    ~[ ridgg r a12.idcod ]∎
                                          a23 ∎)
                       where open comm-triang tr
                             module a12 = is-iso a12⁻¹

    invtr-cod : (tr : comm-triang) → is-iso (comm-triang.a23 tr) → comm-triang
    invtr-cod tr a23⁻¹ = mktriang (~proof a23.⁻¹ ∘ a13          ~[ ∘e (pftr ˢ) r ] /
                                          a23.⁻¹ ∘ a23 ∘ a12    ~[ ass ⊙ lidgg r a23.iddom ]∎
                                          a12 ∎)
                       where open comm-triang tr
                             module a23 = is-iso a23⁻¹

    module iso-transp-tr-domrl (tr : comm-triang) where
      open comm-triang tr
      trnsp-tr-domrl : is-iso a12 → Prp a23 → Prp a13
      trnsp-tr-domrl a12⁻¹ pf = trnsp pftr (∘c pf (on-iso a12 a12⁻¹))

    module iso-transp-tr-domlr (tr : comm-triang) where
      open comm-triang tr
      trnsp-tr-domlr : is-iso a12 → Prp a13 → Prp a23
      trnsp-tr-domlr a12⁻¹ pf = trnsp-tr-domrl (invf-is-iso a12⁻¹) pf
                              where open iso-transp-tr-domrl (invtr-dom tr a12⁻¹)

    module iso-transp-tr-codrl (tr : comm-triang) where
      open comm-triang tr
      trnsp-tr-codrl : is-iso a23 → Prp a13 → Prp a12
      trnsp-tr-codrl a13⁻¹ pf = trnsp {x = a13.⁻¹ ∘ a13}
                                      (∘e (pftr ˢ) r ⊙ ass ⊙ lidgg r a13.iddom)
                                      (∘c (on-iso a13.⁻¹ (invf-is-iso a13⁻¹)) pf)
                              where module a13 = is-iso a13⁻¹

    module iso-transp-tr-codlr (tr : comm-triang) where
      open comm-triang tr
      trnsp-tr-codlr : is-iso a23 → Prp a12 → Prp a13
      trnsp-tr-codlr a23⁻¹ pf = trnsp-tr-codrl (invf-is-iso a23⁻¹) pf
                                               where open iso-transp-tr-codrl (invtr-cod tr a23⁻¹)  

    module iso-transp-sq-rl (sq : comm-square) where
      open comm-square sq
      trnsp-sq-rl : is-iso down → is-iso up → Prp right → Prp left
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
  
  -- end iso-transports
-- end isos
