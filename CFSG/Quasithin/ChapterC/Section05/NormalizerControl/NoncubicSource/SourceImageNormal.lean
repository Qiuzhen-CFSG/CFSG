module
public import Theory.GroupTheory.SylowSubgroupNormalizerImage
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NormalImage
/-!
# The C.5.12 core-image normalizer

The original core image has a Sylow preimage whose intersection with the
quotient kernel lies in the core. The relative Frattini argument therefore
identifies the image of the whole core normalizer with the Sylow normalizer.
The auxiliary span is central over that image, so its image is normal in the
centralizer of the core image. Both ambient quotient maps remain literal.
Source: Aschbacher–Smith C.5.12, printed p.163.
-/
public section
open Subgroup Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC.Section05.NormalizerControl
open ConjugateSource.RankOne
variable {G : Type*} [Group G] [Finite G]

theorem source_auxiliary_normalizer_image
    (K T X V : Subgroup G) (hK : IsShort K)
    (hT : IsPGroup 2 T) (hTK : T ≤ normalizer (K : Set G))
    (P : Sylow 2 (K ⊔ T : Subgroup G))
    (hP : (P : Subgroup (K ⊔ T : Subgroup G)).map (K ⊔ T).subtype = T)
    (S : Sylow 2 X) (hS : (S : Subgroup X).map X.subtype = T)
    (hAX : K ⊔ T ≤ X) (hVX : V ≤ X) (hXV : X ≤ normalizer (V : Set G))
    (hUV : U K ≤ V) :
    let C := (K ⊔ T).pCoreIn 2
    let N := X ⊓ normalizer (C : Set G)
    let : (V.subgroupOf X).Normal := (normal_subgroupOf_iff_le_normalizer hVX).mpr hXV
    let q := QuotientGroup.mk' (centralizer (V.subgroupOf X : Set X))
    (N.subgroupOf X).map q = normalizer ((C.subgroupOf X).map q : Set _) := by
  let C := (K ⊔ T).pCoreIn 2
  let N := X ⊓ normalizer (C : Set G)
  let : (V.subgroupOf X).Normal := (normal_subgroupOf_iff_le_normalizer hVX).mpr hXV
  let q := QuotientGroup.mk' (centralizer (V.subgroupOf X : Set X))
  have hCX : C ≤ X := (pCoreIn_le 2 _).trans hAX
  have hTX : T ≤ X := le_sup_right.trans hAX
  have hCT : C ≤ T := (pCoreIn_le_sylow _ P).trans_eq hP
  have hs : T.subgroupOf X = (S : Subgroup X) := by
    apply map_injective X.subtype_injective
    rw [map_subgroupOf_eq_of_le hTX,hS]
  have hk : (S : Subgroup X) ⊓ q.ker ≤ C.subgroupOf X := by
    rw [← hs]
    rintro t ⟨ht,hc⟩
    have hc' : t ∈ centralizer (V.subgroupOf X : Set X) :=
      (QuotientGroup.eq_one_iff t).mp hc
    have hu : (t : G) ∈ centralizer (U K : Set G) := by
      intro u hu
      exact congrArg X.subtype (hc' ⟨u,hVX (hUV hu)⟩ (hUV hu))
    change (t : G) ∈ (K ⊔ T).pCoreIn 2
    rw [← CounterexampleCharacteristic.ReducedMarking.normal_short_extension_centralizer K T hK hT hTK]
    exact ⟨mem_sup_right ht,hu⟩
  have he := S.normalizer_map_of_contains_kernel_intersection (C.subgroupOf X)
    (hs ▸ subgroupOf_mono X hCT) q (QuotientGroup.mk'_surjective _) hk
  have hN : N.subgroupOf X = normalizer (C.subgroupOf X : Set X) := by
    rw [← subgroupOf_normalizer_eq hCX]
    change (X ⊓ normalizer (C : Set G)).subgroupOf X = _
    ext x
    exact and_iff_right x.property
  change (N.subgroupOf X).map q = _
  rw [hN]
  exact he
/-- The actual auxiliary span image is normal in the normalizer of the core image. -/
theorem source_auxiliary_image_normal
    (K T X V : Subgroup G) (hK : IsShort K)
    (hT : IsPGroup 2 T) (hTK : T ≤ normalizer (K : Set G))
    (P : Sylow 2 (K ⊔ T : Subgroup G))
    (hP : (P : Subgroup (K ⊔ T : Subgroup G)).map (K ⊔ T).subtype = T)
    (S : Sylow 2 X) (hS : (S : Subgroup X).map X.subtype = T)
    (hAX : K ⊔ T ≤ X) (hVX : V ≤ X) (hXV : X ≤ normalizer (V : Set G))
    (hUV : U K ≤ V) :
    let C := (K ⊔ T).pCoreIn 2
    let N := X ⊓ normalizer (C : Set G)
    let L := conjugateSpanBy K N
    let : (V.subgroupOf X).Normal := (normal_subgroupOf_iff_le_normalizer hVX).mpr hXV
    let q := QuotientGroup.mk' (centralizer (V.subgroupOf X : Set X))
    let Pstar := (C.subgroupOf X).map q
    let Lstar := (L.subgroupOf X).map q
    Lstar ≤ normalizer (Pstar : Set _) ∧
      (Lstar.subgroupOf (normalizer (Pstar : Set _))).Normal := by
  let C := (K ⊔ T).pCoreIn 2
  let N := X ⊓ normalizer (C : Set G)
  let L := conjugateSpanBy K N
  let : (V.subgroupOf X).Normal := (normal_subgroupOf_iff_le_normalizer hVX).mpr hXV
  let q := QuotientGroup.mk' (centralizer (V.subgroupOf X : Set X))
  have hAN : K ⊔ T ≤ N := le_inf hAX ((K ⊔ T).le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image (K ⊔ T) (pCore 2 (K ⊔ T : Subgroup G))))
  have hLN : L ≤ N := conjugateSpanBy_le_self (le_sup_left.trans hAN)
  have hLX : L ≤ X := hLN.trans inf_le_left
  have he := source_auxiliary_normalizer_image K T X V hK hT hTK P hP S hS hAX hVX hXV hUV
  have hLNq : (L.subgroupOf X).map q ≤ normalizer ((C.subgroupOf X).map q : Set _) := by
    rw [← he]
    exact map_mono (subgroupOf_mono X hLN)
  refine ⟨hLNq,(normal_subgroupOf_iff_le_normalizer hLNq).mpr ?_⟩
  rw [← he]
  apply (map_mono (f := q) ?_).trans (le_normalizer_map _)
  rw [← subgroupOf_normalizer_eq hLX]
  exact subgroupOf_mono X (le_normalizer_conjugateSpanBy K N)
/-- The original auxiliary span is normal inside the centralizer of the core image. -/
theorem noncubic_source_auxiliary_centralizer_normal
    (K T X V : Subgroup G) (hK : IsChiZeroBlock K) (h3 : ¬ IsAlternatingBlock K 3)
    (hT : IsPGroup 2 T) (hTK : T ≤ normalizer (K : Set G))
    (P : Sylow 2 (K ⊔ T : Subgroup G))
    (hP : (P : Subgroup (K ⊔ T : Subgroup G)).map (K ⊔ T).subtype = T)
    (S : Sylow 2 X) (hS : (S : Subgroup X).map X.subtype = T)
    (hAX : K ⊔ T ≤ X) (hVX : V ≤ X) (hXV : X ≤ normalizer (V : Set G))
    (hUV : U K ≤ V) [IsElementaryAbelian 2 V] :
    let C := (K ⊔ T).pCoreIn 2
    let N := X ⊓ normalizer (C : Set G)
    let L := conjugateSpanBy K N
    let : (V.subgroupOf X).Normal := (normal_subgroupOf_iff_le_normalizer hVX).mpr hXV
    let q := QuotientGroup.mk' (centralizer (V.subgroupOf X : Set X))
    let Pstar := (C.subgroupOf X).map q
    let Lstar := (L.subgroupOf X).map q
    Lstar ≤ centralizer (Pstar : Set _) ∧
      (Lstar.subgroupOf (centralizer (Pstar : Set _))).Normal := by
  let C := (K ⊔ T).pCoreIn 2
  let N := X ⊓ normalizer (C : Set G)
  let L := conjugateSpanBy K N
  let : (V.subgroupOf X).Normal := (normal_subgroupOf_iff_le_normalizer hVX).mpr hXV
  let q := QuotientGroup.mk' (centralizer (V.subgroupOf X : Set X))
  let Pstar := (C.subgroupOf X).map q
  let Lstar := (L.subgroupOf X).map q
  have hc : Lstar ≤ centralizer (Pstar : Set _) := by
    apply le_centralizer_iff.mp
    have he := noncubic_core_image_eq_span_centralizer K T X V hK h3 hT hTK P hP hAX hVX hXV hUV
    exact he.le.trans inf_le_right
  have hn := source_auxiliary_image_normal K T X V hK.chi.short hT hTK P hP S hS hAX hVX hXV hUV
  have hbound := (normal_subgroupOf_iff_le_normalizer hn.1).mp hn.2
  have hbound' := hbound
  refine ⟨hc,(normal_subgroupOf_iff_le_normalizer hc).mpr ?_⟩
  show centralizer (Pstar : Set _) ≤ normalizer (Lstar : Set (X ⧸ centralizer (V.subgroupOf X : Set X)))
  show centralizer (Pstar : Set _) ≤ normalizer (Lstar : Set (X ⧸ centralizer (V.subgroupOf X : Set X)))
  intro a ha
  apply hbound'
  exact Subgroup.centralizer_le_normalizer (Pstar : Set (X ⧸ centralizer (V.subgroupOf X : Set X))) ha
