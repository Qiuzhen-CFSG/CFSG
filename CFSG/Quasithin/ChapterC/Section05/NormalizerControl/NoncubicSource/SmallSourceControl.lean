module
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.SmallModelControl
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.SourceImageControl
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.EmbeddingSelection.LargerSource.FullSpanKernel
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.EmbeddingSelection.SurvivingTransport
/-!
# The literal C.5.12 small full-span models

The intrinsic full-span quotient is transported through its exact action
kernel. The original full Sylow normalizes the auxiliary span, so the proved
A₇, perfect three-cover and PSL₂(25) model bounds normalize its marked core
centralizer. The exact kernel recovery lifts the result to N_X(T), where
the already proved C.5.13 bound gives control of U(K).
Source: Aschbacher–Smith C.5.12, printed p.163.
-/
public section
open Subgroup Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.Section05.NormalizerControl
open ConjugateSource.RankOne Chapter1.Section02 Chapter1.Section02.LocalModels
variable {G : Type*} [Group G] [Finite G]
theorem noncubic_control_of_small_full_span
    (K T X : Subgroup G) (hK : IsChiZeroBlock K) (h3 : ¬ IsAlternatingBlock K 3)
    (hT : IsPGroup 2 T) (hUT : U K ≤ T) (hTK : T ≤ normalizer (K : Set G))
    (P : Sylow 2 (K ⊔ T : Subgroup G))
    (hP : (P : Subgroup (K ⊔ T : Subgroup G)).map (K ⊔ T).subtype = T)
    (hAX : K ⊔ T ≤ X) (hX : X ∈ Chapter1.He G)
    (S : Sylow 2 X) (hS : (S : Subgroup X).map X.subtype = T)
    (hVC : conjugateSpanBy (U K) X ≤ centralizer (U K : Set G))
    (hmodels : let D := (conjugateSpanBy K X).subgroupOf X
      IsAlternating (D ⧸ pCore 2 D) 7 ∨ IsAlternatingCover (D ⧸ pCore 2 D) 7 ∨
        ClassicalGroup.IsPSL (D ⧸ pCore 2 D) 2 25)
    (h513 : (X ⊓ normalizer ((K ⊔ T).pCoreIn 2 : Set G)) ⊓ normalizer (T : Set G) ≤
      normalizer (U K : Set G)) :
    X ⊓ normalizer (T : Set G) ≤ normalizer (U K : Set G) := by
  let C := (K ⊔ T).pCoreIn 2
  let N := X ⊓ normalizer (C : Set G)
  let L := conjugateSpanBy K N
  let D := conjugateSpanBy K X
  let V := conjugateSpanBy (U K) X
  have hKX : K ≤ X := le_sup_left.trans hAX
  have hTX : T ≤ X := le_sup_right.trans hAX
  have hDX : D ≤ X := conjugateSpanBy_le_self hKX
  have hVX : V ≤ X := conjugateSpanBy_le_self ((map_subtype_le _).trans hKX)
  have hXV : X ≤ normalizer (V : Set G) := le_normalizer_conjugateSpanBy _ _
  have hr := noncubic_full_span_reduced K T hK h3 hUT hT hTK X hKX S hS hVC
  let : IsElementaryAbelian 2 (U K) := hK.chi.short.elementary.map K.subtype
  let : IsMulCommutative V := (conjugateSpanBy_commutative_iff (U K) X).mpr (le_centralizer_iff.mp hVC)
  let : IsElementaryAbelian 2 V := conjugateSpanBy_elementary_of_commutative (U K) X
  let : (V.subgroupOf X).Normal := hr.normal
  let q := QuotientGroup.mk' (centralizer (V.subgroupOf X : Set X))
  let E := (D.subgroupOf X).map q
  let B := (L.subgroupOf X).map q
  let Q := S.mapSurjective (QuotientGroup.mk'_surjective (centralizer (V.subgroupOf X : Set X)))
  let : (D.subgroupOf X).Normal := (normal_subgroupOf_iff_le_normalizer hDX).mpr
    (le_normalizer_conjugateSpanBy K X)
  let : E.Normal := by dsimp [E]; infer_instance
  have hQE : (Q : Subgroup _)= (T.subgroupOf X).map q := by
    change (S : Subgroup X).map q = _
    congr 1
    apply map_injective X.subtype_injective
    rw [hS,map_subgroupOf_eq_of_le hTX]
  have hAN : K ⊔ T ≤ N := le_inf hAX ((K ⊔ T).le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image (K ⊔ T) (pCore 2 (K ⊔ T : Subgroup G))))
  have hLX : L ≤ X := (conjugateSpanBy_le_self (le_sup_left.trans hAN)).trans inf_le_left
  have hQB : (Q : Subgroup (X ⧸ centralizer (V.subgroupOf X : Set X))) ≤
      normalizer (B : Set (X ⧸ centralizer (V.subgroupOf X : Set X))) := by
    rw [hQE]
    apply (map_mono (f := q) ?_).trans (le_normalizer_map _)
    rw [← subgroupOf_normalizer_eq hLX]
    exact subgroupOf_mono X ((le_sup_right.trans hAN).trans (le_normalizer_conjugateSpanBy K N))
  have hBE : B ≤ E := map_mono (subgroupOf_mono X (conjugateSpanBy_mono le_rfl inf_le_left))
  obtain ⟨eD⟩ := (noncubic_full_span_kernel K T X hK h3 hUT hT hTK hKX hX S hS hVC).2.2.2.1
  have hm : IsAlternating E 7 ∨ IsAlternatingCover E 7 ∨ ClassicalGroup.IsPSL E 2 25 := by
    rcases hmodels with h | h | h
    · obtain ⟨e⟩ := h
      exact .inl ⟨eD.symm.trans e⟩
    · exact .inr (.inl (EmbeddingSelection.alternatingCover_transport eD h))
    · exact .inr (.inr (h.of_mulEquiv eD.symm))
  have hn := small_model_normalizer_centralizer E hm Q B hBE hQB
  have he := noncubic_core_image_eq_span_centralizer K T X V hK h3 hT hTK
    P hP hAX hVX hXV (le_conjugateSpanBy _ _)
  have hnormalizer : normalizer ((T.subgroupOf X).map q : Set (X ⧸ centralizer (V.subgroupOf X : Set X))) ≤
      normalizer ((C.subgroupOf X).map q : Set (X ⧸ centralizer (V.subgroupOf X : Set X))) := by
    rw [he,← hQE]
    exact hn
  exact noncubic_control_of_quotient_normalizer K T X V hK hT hTK P hP hAX hVX hXV
    (le_conjugateSpanBy _ _) hnormalizer h513
end CFSG.Quasithin.ChapterC.Section05.NormalizerControl
