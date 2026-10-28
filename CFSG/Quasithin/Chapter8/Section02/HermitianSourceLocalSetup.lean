module
public import CFSG.Quasithin.Chapter8.Section02.Offenders.Parabolic.Construction.Selection
public import Theory.GroupTheory.AmalgamLocalCores

/-!
# The local E.2.8 setup without a two-closedness premise

For an original HStar member, H ∩ M is the unique maximal subgroup above
T. Relative normalization puts V in its two-core. The intersection of
that two-core with its normal core is exactly O₂(H), so escape from O₂(H)
already gives escape from the normal core. Thus the E.2.8 setup needs no
additional universal B.6.8(5) input. All cores are intrinsic to H.

The chosen Hermitian orbit supplies the normalization and noncontainment
premises in NonFFSourceNonMathieuHermitianLocalSetup. This is the local
setup for selection, not an existence theorem for the selected pair.
Source: Aschbacher–Smith, the proof of 8.2.2(2), printed p.715, using
E.2.8, printed p.221 (1 March 2004 manuscript, refs/quasithin.pdf).
-/

public noncomputable section
open scoped IsMulCommutative
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter8.Section02.HermitianSource
open ChapterB ChapterE Offenders.Parabolic.Construction
variable {G : Type*} [Group G] [Finite G]

/-- Relative normalization and escape from O₂(H) give the complete E.2.8
setup. The normal-core intersection identity removes any separate B.6.8(5)
input about two-closedness. -/
theorem hypothesisE28_of_HStar_outside_twoCore {K : GroupClass} (hG : IsSimpleQTKE K G)
    (T : Sylow 2 G) {H M V : Subgroup G} [IsElementaryAbelian 2 V]
    (hTM : (T : Subgroup G) ≤ M) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hVT : V ≤ T) (hn : (V.subgroupOf (T : Subgroup G)).Normal)
    (hMV : H ⊓ M ≤ normalizer (V : Set G))
    (hout : ¬ V ≤ (pCore 2 H).map H.subtype) :
    HypothesisE28 K H T M V := by
  have hTH := hH.1.1.2
  let S := T.subtype hTH
  have hS : (S : Subgroup H) = (T : Subgroup G).subgroupOf H := rfl
  have hmap : ((T : Subgroup G).subgroupOf H).map H.subtype = T :=
    map_subgroupOf_eq_of_le hTH
  obtain ⟨B, hB, hu⟩ := Chapter3.HStar.unique_maximal_subgroup T hTM hH
  have hSB : (S : Subgroup H) ≤ B := by
    apply (map_le_map_iff_of_injective H.subtype_injective).mp
    simpa only [hS, hmap] using hB.2
  have hP : IsMinimalParabolicOver S ⊤ := by
    apply (isMinimalParabolicOver_top_iff S).mpr
    refine ⟨⟨B, ⟨hB.1, hSB⟩, ?_⟩, ?_⟩
    · intro Y hY
      apply hu Y
      refine ⟨hY.1, ?_⟩
      have hy := map_mono (f := H.subtype) hY.2
      simpa only [hS, hmap] using hy
    · intro hs
      have hcore : (S : Subgroup H) ≤ pCore 2 H := le_sSup ⟨hs, S.isPGroup'⟩
      have hc := map_mono (f := H.subtype) hcore
      rw [hS, hmap] at hc
      exact hout (hVT.trans hc)
  have hMB : M.subgroupOf H = B := by
    have hBM : B ≤ M.subgroupOf H := by
      have hbH : B.map H.subtype < H := by
        have hb := (map_lt_map_iff_of_injective H.subtype_injective).mpr hB.1.lt_top
        simpa only [← MonoidHom.range_eq_map, range_subtype] using hb
      have hbM := Chapter3.HStar.proper_overgroup_le T hH hB.2 hbH
      intro x hx
      exact hbM (mem_map_of_mem H.subtype hx)
    have hnM : M.subgroupOf H ≠ ⊤ := by
      intro he
      apply hH.1.2
      intro x hx
      exact (show (⟨x, hx⟩ : H) ∈ M.subgroupOf H by rw [he]; trivial)
    exact (eq_of_le_of_not_lt hBM (fun hlt => hnM (hB.1.2 _ hlt))).symm
  have hM : M.subgroupOf H = minimalParabolicMax S hP :=
    hMB.trans (minimalParabolicMax_unique S hP hB.1 hSB)
  have hVH := hVT.trans hTH
  have hVM : V ≤ (pCore 2 (M.subgroupOf H)).map
      (H.subtype.comp (M.subgroupOf H).subtype) := by
    have hVm : V.subgroupOf H ≤ M.subgroupOf H := comap_mono (hVT.trans hTM)
    have hnorm : (M.subgroupOf H) ≤ normalizer (V.subgroupOf H : Set H) := by
      rw [← subgroupOf_normalizer_eq hVH]
      intro x hx
      exact hMV ⟨x.property, hx⟩
    let _ : ((V.subgroupOf H).subgroupOf (M.subgroupOf H)).Normal :=
      (normal_subgroupOf_iff_le_normalizer hVm).mpr hnorm
    have hc : (V.subgroupOf H).subgroupOf (M.subgroupOf H) ≤ pCore 2 (M.subgroupOf H) :=
      le_sSup ⟨inferInstance, (IsElementaryAbelian.isPGroup 2 V).comap_subtype.comap_subtype⟩
    have hm := map_mono (f := H.subtype.comp (M.subgroupOf H).subtype) hc
    rwa [← map_map, map_subgroupOf_eq_of_le hVm, map_subgroupOf_eq_of_le hVH] at hm
  refine ⟨hTH, ⟨S, hS, hP, hM⟩, Chapter3.sqtk_of_mem_H hG hH.1.1.1,
    inferInstance, hVT, hn, hVM, ?_⟩
  intro hcore
  apply hout
  have hVcore : V.subgroupOf H ≤ (M.subgroupOf H).pCoreIn 2 := by
    intro v hv
    obtain ⟨a, ha, he⟩ := hVM hv
    exact ⟨a, ha, Subtype.ext he⟩
  have hVJ : V.subgroupOf H ≤ localCore M H := by
    intro v hv
    obtain ⟨a, ha, he⟩ := hcore hv
    exact (show a = v from Subtype.ext he) ▸ ha
  have he := Theory.GroupTheory.AmalgamLocalCores.core_eq_edge_inf_kernel
    S (M.subgroupOf H) (hM.symm ▸ (minimalParabolicMax_spec S hP).2)
  have hc : V.subgroupOf H ≤ pCore 2 H := by
    rw [he]
    exact le_inf hVcore hVJ
  have hm := map_mono (f := H.subtype) hc
  rwa [map_subgroupOf_eq_of_le hVH] at hm

end CFSG.Quasithin.Chapter8.Section02.HermitianSource
