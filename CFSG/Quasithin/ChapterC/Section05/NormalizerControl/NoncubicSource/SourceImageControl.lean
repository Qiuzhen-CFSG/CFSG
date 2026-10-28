module
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NormalImage
/-!
# Lifting the actual C.5.12 quotient normalizer

The source two-core contains the quotient kernel inside T. Hence it is
recovered by intersecting T with the preimage of its image. Normalizer
control in X/C_X(V) therefore lifts to the original core and then applies
the C.5.13 normalizer conclusion on its actual auxiliary normalizer.
Source: Aschbacher–Smith C.5.12, printed p.163.
-/
public section
open Subgroup Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC.Section05.NormalizerControl
open ConjugateSource.RankOne
variable {G : Type*} [Group G] [Finite G]
theorem noncubic_control_of_quotient_normalizer
    (K T X V : Subgroup G) (hK : IsChiZeroBlock K)
    (hT : IsPGroup 2 T) (hTK : T ≤ normalizer (K : Set G))
    (P : Sylow 2 (K ⊔ T : Subgroup G))
    (hP : (P : Subgroup (K ⊔ T : Subgroup G)).map (K ⊔ T).subtype = T)
    (hAX : K ⊔ T ≤ X) (hVX : V ≤ X) (hXV : X ≤ normalizer (V : Set G))
    (hUV : U K ≤ V) [IsElementaryAbelian 2 V]
    (hnormalizer : let : (V.subgroupOf X).Normal := (normal_subgroupOf_iff_le_normalizer hVX).mpr hXV
      let q := QuotientGroup.mk' (centralizer (V.subgroupOf X : Set X))
      normalizer ((T.subgroupOf X).map q : Set (X ⧸ centralizer (V.subgroupOf X : Set X))) ≤
      normalizer ((((K ⊔ T).pCoreIn 2).subgroupOf X).map q : Set (X ⧸ centralizer (V.subgroupOf X : Set X))))
    (h513 : (X ⊓ normalizer ((K ⊔ T).pCoreIn 2 : Set G)) ⊓ normalizer (T : Set G) ≤
      normalizer (U K : Set G)) :
    X ⊓ normalizer (T : Set G) ≤ normalizer (U K : Set G) := by
  let C := (K ⊔ T).pCoreIn 2
  let : (V.subgroupOf X).Normal := (normal_subgroupOf_iff_le_normalizer hVX).mpr hXV
  let q := QuotientGroup.mk' (centralizer (V.subgroupOf X : Set X))
  have hCX : C ≤ X := (pCoreIn_le 2 _).trans hAX
  have hTX : T ≤ X := le_sup_right.trans hAX
  have hCT : C ≤ T := (pCoreIn_le_sylow _ P).trans_eq hP
  have hk : T.subgroupOf X ⊓ q.ker ≤ C.subgroupOf X := by
    rintro t ⟨ht,hc⟩
    have hc' : t ∈ centralizer (V.subgroupOf X : Set X) := (QuotientGroup.eq_one_iff t).mp hc
    have hu : (t : G) ∈ centralizer (U K : Set G) := by
      intro u hu
      exact congrArg X.subtype (hc' ⟨u,hVX (hUV hu)⟩ (hUV hu))
    change (t : G) ∈ (K ⊔ T).pCoreIn 2
    exact (CounterexampleCharacteristic.ReducedMarking.normal_short_extension_centralizer
      K T hK.chi.short hT hTK) ▸ ⟨mem_sup_right ht,hu⟩
  have hi : T.subgroupOf X ⊓ ((C.subgroupOf X).map q).comap q = C.subgroupOf X := by
    rw [comap_map_eq]
    apply le_antisymm
    · rintro t ⟨ht,hc⟩
      obtain ⟨c,hcC,k,hk',rfl⟩ := mem_sup_of_normal_right.mp hc
      have hkt : k ∈ T.subgroupOf X := by
        have h := (T.subgroupOf X).mul_mem ((T.subgroupOf X).inv_mem (hCT hcC)) ht
        simpa using h
      exact (C.subgroupOf X).mul_mem hcC (hk ⟨hkt,hk'⟩)
    · exact le_inf (subgroupOf_mono X hCT) le_sup_left
  have hpre : normalizer (T.subgroupOf X : Set X) ≤
      normalizer (((C.subgroupOf X).map q).comap q : Set X) :=
    (map_le_iff_le_comap.mp (((T.subgroupOf X).le_normalizer_map q).trans hnormalizer)).trans
      (le_normalizer_comap q)
  have hn : normalizer (T.subgroupOf X : Set X) ≤ normalizer (C.subgroupOf X : Set X) := by
    rw [← hi]
    exact (le_inf le_rfl hpre).trans inf_normalizer_le_normalizer_inf
  rintro g ⟨hgX,hgT⟩
  have hg : (⟨g,hgX⟩ : X) ∈ normalizer (T.subgroupOf X : Set X) := by
    rw [← subgroupOf_normalizer_eq hTX]
    exact hgT
  have hgC := hn hg
  rw [← subgroupOf_normalizer_eq hCX] at hgC
  exact h513 ⟨⟨hgX,hgC⟩,hgT⟩
end CFSG.Quasithin.ChapterC.Section05.NormalizerControl
