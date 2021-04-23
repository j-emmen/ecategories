
{-# OPTIONS --without-K #-}

module ecats.basic-props.image-fact where

open import ecats.basic-defs.ecat-def&not
open import ecats.basic-defs.arrows
open import ecats.basic-defs.image-fact
open import ecats.basic-props.isomorphism
open import ecats.basic-props.epi&mono-basic
open import ecats.finite-limits.all


module image-fact-props (ℂ : ecategory) where
  open ecategory-aux ℂ
  open arrows-defs ℂ
  open iso-props ℂ
  open iso-transports ℂ
  open hom-ext-prop-defs ℂ
  open epi&mono-props ℂ
  open image-fact-defs ℂ
  open binary-products ℂ
  open wequaliser-defs ℂ
  open equaliser-defs ℂ
  open wpullback-squares ℂ
  open pullback-squares ℂ
  open pullback-props ℂ
  open bow-defs ℂ
  open wWlim-defs ℂ
  private
    module sp = span/
    --module sp = span
    module sq/ = square/cosp
    module sq = comm-square
    module pbof = pullback-of
    module pbsq = pb-square
    module ×of = product-of
    module prd = bin-product
    module eqlof = equaliser-of
    module weqlof = wequaliser-of
    module wpbof = wpullback-of
    module bwof = bow-of
    module imgof = img-fact-of


  -- Image factorisations of the same arrow are isomorphic
  
  module img-uptoiso {A B : Obj} {f : || Hom A B ||} (imgf imgf' : img-fact-of f)
                     where
    private
      module imgf = img-fact-of imgf
      module imgf' = img-fact-of imgf'
    med-ar : || Hom imgf.Ob imgf'.Ob ||
    med-ar = imgf.univ imgf'.M-is-monic imgf'.tr
    med-trM : imgf'.M ∘ med-ar ~ imgf.M
    med-trM = imgf.univ-tr imgf'.M-is-monic imgf'.tr
    med-ar⁻¹ : || Hom imgf'.Ob imgf.Ob ||
    med-ar⁻¹ = imgf'.univ imgf.M-is-monic imgf.tr
    med-trM⁻¹ : imgf.M ∘ med-ar⁻¹ ~ imgf'.M
    med-trM⁻¹ = imgf'.univ-tr imgf.M-is-monic imgf.tr

    med-ar-iso-pair : is-iso-pair med-ar med-ar⁻¹
    med-ar-iso-pair = record
                    { iddom = imgf.Mpf (ass ⊙ ∘e r med-trM⁻¹ ⊙ ridgenˢ med-trM)
                    ; idcod = imgf'.Mpf (ass ⊙ ∘e r med-trM ⊙ ridgenˢ med-trM⁻¹ )
                    }
    med-trC : med-ar ∘ imgf.C ~ imgf'.C
    med-trC = imgf'.Mpf (ass ⊙ ∘e r med-trM ⊙ imgf.tr ⊙ imgf'.tr ˢ)
    med-trC⁻¹ : med-ar⁻¹ ∘ imgf'.C ~ imgf.C
    med-trC⁻¹ = imgf.Mpf (ass ⊙ ∘e r med-trM⁻¹ ⊙ imgf'.tr ⊙ imgf.tr ˢ)
  -- end img-uptoiso

  module img-uptoiso-gen {A B : Obj} {f : || Hom A B ||} (imgf imgf' : img-fact-of f)
                         {m : || Hom (imgof.Ob imgf) (imgof.Ob imgf') ||}
                         (trM : imgof.M imgf' ∘ m ~ imgof.M imgf)
                         where
      private
        module imgf = img-fact-of imgf
        module imgf' = img-fact-of imgf'

      m⁻¹ : || Hom (imgof.Ob imgf') (imgof.Ob imgf) ||
      m⁻¹ = imgf'.univ imgf.M-is-monic imgf.tr
      isopair : is-iso-pair m m⁻¹
      isopair = record
              { iddom = imgf.Mpf (ass ⊙ ∘e r (imgf'.univ-tr imgf.M-is-monic imgf.tr) ⊙ ridgenˢ trM)
              ; idcod = imgf'.Mpf (ass ⊙ ∘e r trM ⊙ ridgenˢ (imgf'.univ-tr imgf.M-is-monic imgf.tr))
              }
      open is-iso-pair isopair public
      m-iso : is-iso m
      m-iso = record
            { invf = m⁻¹
            ; isisopair = isopair
            }
      trM⁻¹ : imgof.M imgf ∘ m⁻¹ ~ imgof.M imgf'
      trM⁻¹ = epi-pf (assˢ ⊙ ridgg (trM ˢ) iddom)
            where open is-epic (iso-is-epic m-iso)
      trC : m ∘ imgf.C ~ imgf'.C
      trC = imgf'.Mpf (ass ⊙ ∘e r trM ⊙ imgf.tr ⊙ imgf'.tr ˢ)
      trC⁻¹ : m⁻¹ ∘ imgf'.C ~ imgf.C
      trC⁻¹ = imgf.Mpf (ass ⊙ ∘e r trM⁻¹ ⊙ imgf'.tr ⊙ imgf.tr ˢ)
  -- end img-uptoiso-gen

{-
  img-uptoiso-ar : {A B : Obj} {f : || Hom A B ||} (imgf imgf' : img-fact-of f)
                   {m : || Hom (imgof.Ob imgf) (imgof.Ob imgf') ||}
                     → imgof.M imgf' ∘ m ~ imgof.M imgf → is-iso m
  img-uptoiso-ar imgf imgf' {m} mtrM = record
    { invf = imgf'.univ imgf.M-is-monic imgf.tr
    ; isisopair = record
                { iddom = imgf.Mpf (ass ⊙ ∘e r (imgf'.univ-tr imgf.M-is-monic imgf.tr) ⊙ ridgenˢ mtrM)
                ; idcod = imgf'.Mpf (ass ⊙ ∘e r mtrM ⊙ ridgenˢ (imgf'.univ-tr imgf.M-is-monic imgf.tr))
                }
    }
    where module imgf = img-fact-of imgf
          module imgf' = img-fact-of imgf'
-}

  imgCmonic-is-idar : {A B : Obj} {m : || Hom A B ||}
                       → is-monic m → is-img-fact (rid {f = m})
  imgCmonic-is-idar {A} {B} {m} ism = record
    { M-is-monic = ism
    ; univ = λ {C} {m} {c} _ _ → c
    ; univ-tr = λ _ com → com
    }


  imgMcov-is-idar : {A B : Obj} {c : || Hom A B ||}
                       → is-cover c → is-img-fact (lid {f = c})
  imgMcov-is-idar {A} {B} {c} isc = record
    { M-is-monic = iso-is-monic (idar-is-iso B)
    ; univ = m.⁻¹
    ; univ-tr = m.idcod
    }
    where open is-cover isc
          module m {C : Obj} {m : || Hom C B ||} {f : || Hom A C ||} (ism : is-monic m) (tr : m ∘ f ~ c)
                   = is-iso (cov-pf tr ism)


  module img-of-monic-is-iso {A B : Obj} {m : || Hom A B ||} (imgm : img-fact-of m) (ism : is-monic m)
         = img-uptoiso-gen (record { isimg = imgCmonic-is-idar ism })
                           imgm
                           (imgof.tr imgm)

  img-of-monic-is-iso : {A B : Obj} {m : || Hom A B ||} (imgm : img-fact-of m)
                       → is-monic m → is-iso (imgof.C imgm)
  img-of-monic-is-iso {A} {B} {m} imgm ism = m-iso
                                           where open img-of-monic-is-iso imgm ism


  any-imgC-is-cover : {A B If : Obj} {f : || Hom A B ||}
                      {cf : || Hom A If ||} {mf : || Hom If B ||} {trf : mf ∘ cf ~ f}
                         → is-img-fact trf → is-cover cf
  any-imgC-is-cover {f = f} {cf} {mf} {trf} imgf = record
    { cov-pf = λ {C} {p} {m} pfc pfm → monic-sepi-is-iso pfm (record
             { rinv = imgf.univ (mcongr.∘c imgf.M-is-monic pfm) (assˢ ⊙ ∘e pfc r ⊙ trf)
             ; rinv-ax = imgf.Mpf (ass ⊙ (imgf.univ-tr (mcongr.∘c imgf.M-is-monic pfm)
                                                        (assˢ ⊙ ∘e pfc r ⊙ trf)) ⊙ ridˢ)
             })
    }
    where module imgf = is-img-fact imgf
          module mcongr = is-ecat-congr mono-is-congr

  
  strepi-mono-is-img-fact : {A B If : Obj} {f : || Hom A B ||} {qf : || Hom A If ||} {mf : || Hom If B ||} (trf : mf ∘ qf ~ f)
                             → is-strong-epi qf → is-monic mf → is-img-fact trf
  strepi-mono-is-img-fact trf qstr mmon = record
    { M-is-monic = mmon
    ; univ = λ m'mon pfcom' → lift (trf ⊙ pfcom' ˢ) m'mon
    ; univ-tr = λ m'mon pfcom' → tr-down (trf ⊙ pfcom' ˢ) m'mon
    }
    where open is-strong-epi qstr
                                                      

  repi-mono-is-img-fact : {A B If : Obj} {f : || Hom A B ||} {cf : || Hom A If ||} {mf : || Hom If B ||} (trf : mf ∘ cf ~ f)
                             → is-regular-epi cf → is-monic mf → is-img-fact trf
  repi-mono-is-img-fact {f = f} {cf} {mf} trf pfr pfm = record
    { M-is-monic = pfm
    ; univ = λ {_} {m'} {c'} pfm' pfcom' → frepi.univ c' (c'-coeq pfm' pfcom')
    ; univ-tr = λ pfm' pfcom' →
                      frepi.epi-pf (assˢ ⊙ ∘e (frepi.univ-eq (c'-coeq pfm' pfcom')) r
                              ⊙ pfcom' ⊙ (trf ˢ)) 
    }
    where module frepi = is-regular-epi pfr
          open is-monic pfm renaming (mono-pf to mf-monic)
          f-coeq : f ∘ frepi.rel₁ ~ f ∘ frepi.rel₂
          f-coeq = ∘e r (trf ˢ) ⊙ assˢ ⊙ ∘e frepi.eq r ⊙ ass ⊙ ∘e r trf
          c'-coeq : {C : Obj} {m' : || Hom C _ ||} {c' : || Hom _ C ||}
                       → is-monic m' → m' ∘ c' ~ f
                         → c' ∘ frepi.rel₁ ~ c' ∘ frepi.rel₂
          c'-coeq pfm' pfcom' = m'-monic (ass ⊙ ∘e r pfcom' ⊙ f-coeq ⊙ ∘e r (pfcom' ˢ) ⊙ assˢ)
                    where open is-monic pfm' renaming (mono-pf to m'-monic)


  -- kernel pair of f is kernel pair of (imgC f)

  imgC-kp : {A B : Obj} {f : || Hom A B ||} (kerf : pullback-of f f) (imgf : img-fact-of f)
               → pullback-of (img-fact-of.C imgf) (img-fact-of.C imgf)
  imgC-kp kerf imgf = mkpb-of (monic-sub-pb-sq kerf.×/pbsq
                                               imgf.tr
                                               imgf.tr
                                               imgf.M-is-monic)
            where module kerf = pullback-of-not kerf
                  module imgf = img-fact-of imgf



  -- when base objects have product, image factorisation of a span is obtained as an image factorisation of the universal arrow

  private
    sp2ar : {O1 O2 : Obj} (prd : product-of O1 O2) (sp/ : span/ O1 O2)
                → || Hom (sp.O12 sp/) (×of.O12 prd) ||
    sp2ar prd sp/ = < sp.a1 sp/ , sp.a2 sp/ >
                  where open product-of prd
    ar2sp : {O1 O2 : Obj} (prd : product-of O1 O2) {A : Obj} (f : || Hom A (×of.O12 prd) ||)
               → span/ O1 O2
    ar2sp prd f = mkspan/ (π₁ ∘ f) (π₂ ∘ f)
                where open product-of prd
  
  is-img-fact→is-img-fact₂-covdata : {O1 O2 : Obj} (prd : product-of O1 O2) {sp/ : span/ O1 O2}
                                      (img : img-fact-of (sp2ar prd sp/))
                                        → span/-mor sp/ (ar2sp prd (img-fact-of.M img))
  is-img-fact→is-img-fact₂-covdata prd img = record
    { ar = img.C
    ; tr₁ = assˢ ⊙ ∘e img.tr r ⊙ O1×O2.×tr₁
    ; tr₂ = assˢ ⊙ ∘e img.tr r ⊙ O1×O2.×tr₂
    }
    where module img = img-fact-of img
          module O1×O2 = product-of-not prd

  is-img-fact→is-img-fact₂ : {O1 O2 : Obj} (prd : product-of O1 O2) {sp/ : span/ O1 O2}
                              (img : img-fact-of (sp2ar prd sp/))
                                → is-img-fact₂ (is-img-fact→is-img-fact₂-covdata prd img)
  is-img-fact→is-img-fact₂ {O1} {O2} prd {sp/} img = record
    { M-is-jm/ = <>monic→isjm/ prd r r img.M-is-monic
    ; univ = un
    ; univ-tr₁ = λ {msp/'} c'-data isjm/ → 
      ~proof span/.a1 msp/' ∘ un c'-data isjm/               ~[ ∘e r (O1×O2.×tr₁ {g = span/.a2 msp/'} ˢ) ⊙ assˢ  ] /
             O1×O2.π₁ ∘ sp2ar prd msp/' ∘ un c'-data isjm/   ~[ ∘e (img.univ-tr (isjm/→<>monic isjm/ prd) (un-aux c'-data isjm/)) r ]∎ 
             O1×O2.π₁ ∘ img.M ∎ -- =  span/.a1 (ar2sp prd img.M)
    ; univ-tr₂ = λ {msp/'} c'-data isjm/ → 
      ~proof span/.a2 msp/' ∘ un c'-data isjm/               ~[ ∘e r (O1×O2.×tr₂ {f = span/.a1 msp/'} ˢ) ⊙ assˢ  ] /
             O1×O2.π₂ ∘ sp2ar prd msp/' ∘ un c'-data isjm/   ~[ ∘e (img.univ-tr (isjm/→<>monic isjm/ prd) (un-aux c'-data isjm/)) r ]∎ 
             O1×O2.π₂ ∘ img.M ∎ -- =  span/.a1 (ar2sp prd img.M)
    }
    where module img = img-fact-of img
          module O1×O2 = product-of-not prd
          un-aux : {msp/' : span/ O1 O2} (c'-data : span/-mor sp/ msp/') → is-jointly-monic/ msp/'
                          → sp2ar prd msp/' ∘ span/-mor.ar c'-data ~ sp2ar prd sp/
          un-aux {msp/'} c'-data isjm/ =
            sp2ar prd msp/' ∘ span/-mor.ar c'-data
                   ~[ O1×O2.<>ar~ar (O1×O2.×tr₁ ⊙ span/-mor.tr₁ c'-data ˢ) (O1×O2.×tr₂ ⊙ span/-mor.tr₂ c'-data ˢ) ]
            sp2ar prd sp/
          un : {msp/' : span/ O1 O2} → span/-mor sp/ msp/' → is-jointly-monic/ msp/'
                      → || Hom (span/.O12 (ar2sp prd img.M)) (span/.O12 msp/') ||
          un c'-data isjm/ = img.univ (isjm/→<>monic isjm/ prd) (un-aux c'-data isjm/)

-- end image-fact-props
